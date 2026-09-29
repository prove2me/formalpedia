-- Prove2me | solution 1 for CuspForm.exists_GammaH_coe_eq_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/301e37b8-3058-5ecc-a883-4048e3ef2e23

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspFormClass_isZeroAt_slash_ratCast
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash

set_option autoImplicit false

noncomputable section

open Matrix CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace AlTrHk

variable {M p : ℕ} (W : ModularForm.AtkinLehnerDatum M p)

def repMat : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => !![1, (j : ℤ); 0, (p : ℤ)]

@[scoped simp] lemma repMat_none : repMat W none = W.mat := rfl

@[scoped simp] lemma repMat_some (j : Fin p) : repMat W (some j) = !![1, (j : ℤ); 0, (p : ℤ)] := rfl

lemma not_dvd_b (hp : 1 < p) : ¬ (p : ℤ) ∣ W.b := by
  intro hdvd
  have h1 : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) ∣ (p : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_left _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma not_dvd_R (hp : 1 < p) : ¬ (p : ℤ) ∣ (W.R : ℤ) := by
  intro hdvd
  have h1 : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) ∣ (p : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_right _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma repMat_unique (hp : 1 < p) {E : Matrix (Fin 2) (Fin 2) ℤ}
    {i i' : Option (Fin p)} (h : repMat W i' = E * repMat W i) : i' = i := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>
      exfalso
      rw [repMat_some, repMat_none, ModularForm.AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * ((p : ℤ) * W.a) + E 0 1 * ((p : ℤ) * (W.R : ℤ)) :=
        congrFun (congrFun h 0) 0
      have hdvd : (p : ℤ) ∣ 1 :=
        ⟨E 0 0 * W.a + E 0 1 * (W.R : ℤ), by linear_combination h00⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases i' with
    | none =>
      exfalso
      rw [repMat_some, repMat_none, ModularForm.AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (p : ℤ) * W.a = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : W.b = E 0 0 * (j : ℤ) + E 0 1 * (p : ℤ) := congrFun (congrFun h 0) 1
      exact not_dvd_b W hp ⟨W.a * (j : ℤ) + E 0 1, by linear_combination h01 - (j : ℤ) * h00⟩
    | some j' =>
      rw [repMat_some, repMat_some, Matrix.eta_fin_two E, Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : (j' : ℤ) = E 0 0 * (j : ℤ) + E 0 1 * (p : ℤ) := congrFun (congrFun h 0) 1
      have hE : E 0 0 = 1 := by linear_combination -h00
      rw [hE, one_mul] at h01
      have hcast : ((j' : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
        have := congrArg (Int.cast : ℤ → ZMod p) h01
        push_cast at this
        simpa using this
      have hval : (j' : ℕ) = (j : ℕ) := by
        have hj := ZMod.val_cast_of_lt j.isLt
        have hj' := ZMod.val_cast_of_lt j'.isLt
        rw [← hj, ← hj', hcast]
      exact congrArg some (Fin.ext hval)

lemma exists_fin_dvd_sub_mul (hp : p.Prime) {x : ℤ} (t : ℤ) (hx : ¬ (p : ℤ) ∣ x) :
    ∃ j' : Fin p, (p : ℤ) ∣ t - x * (j' : ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hcop : IsCoprime (p : ℤ) x :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hx
  obtain ⟨u, v, huv⟩ := hcop
  have hmod := Int.emod_add_mul_ediv (v * t) (p : ℤ)
  have hnonneg : 0 ≤ (v * t) % (p : ℤ) := Int.emod_nonneg _ hp0
  have hlt : (v * t) % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ hppos
  have hcoe : ((((v * t) % (p : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (p : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  refine ⟨⟨((v * t) % (p : ℤ)).toNat, by omega⟩, ⟨t * u + x * ((v * t) / (p : ℤ)), ?_⟩⟩
  show t - x * ((((v * t) % (p : ℤ)).toNat : ℕ) : ℤ) = (p : ℤ) * (t * u + x * ((v * t) / (p : ℤ)))
  rw [hcoe]
  linear_combination (-t) * huv + (-x) * hmod

theorem mat_mul_normalizes (α β c δ : ℤ)
    (hdet : α * δ - β * ((p : ℤ) * (W.R : ℤ) * c) = 1) :
    ∃ x y s t : ℤ, x * t - y * ((p : ℤ) * (W.R : ℤ) * s) = 1 ∧
      t = -((W.R : ℤ) * W.b) * (α + (p : ℤ) * c) + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ) ∧
      W.mat * !![α, β; (p : ℤ) * (W.R : ℤ) * c, δ]
        = !![x, y; (p : ℤ) * (W.R : ℤ) * s, t] * W.mat := by
  refine ⟨(p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
        - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ),
      -(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β + W.a * W.b * δ,
      α + (p : ℤ) * c - (W.R : ℤ) * β - δ,
      -((W.R : ℤ) * W.b) * (α + (p : ℤ) * c) + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ),
      ?_, rfl, ?_⟩
  · linear_combination ((p : ℤ) * W.a - (W.R : ℤ) * W.b) ^ 2 * hdet
      + ((p : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout
  · rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ) * c)
        = ((p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ)) * ((p : ℤ) * W.a)
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * ((p : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * W.b * c * (p : ℤ) + W.a * α * (p : ℤ))) * W.bezout
    · show (p : ℤ) * W.a * β + W.b * δ
        = ((p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ)) * W.b
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * (p : ℤ)
      linear_combination (-(W.a * β * (p : ℤ) + W.b * δ)) * W.bezout
    · show (p : ℤ) * (W.R : ℤ) * α + (p : ℤ) * ((p : ℤ) * (W.R : ℤ) * c)
        = (p : ℤ) * (W.R : ℤ) * (α + (p : ℤ) * c - (W.R : ℤ) * β - δ) * ((p : ℤ) * W.a)
          + (-((W.R : ℤ) * W.b) * (α + (p : ℤ) * c)
              + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ)) * ((p : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * α * (p : ℤ) + (W.R : ℤ) * c * (p : ℤ) ^ 2)) * W.bezout
    · show (p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ
        = (p : ℤ) * (W.R : ℤ) * (α + (p : ℤ) * c - (W.R : ℤ) * β - δ) * W.b
          + (-((W.R : ℤ) * W.b) * (α + (p : ℤ) * c)
              + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ)) * (p : ℤ)
      linear_combination (-((W.R : ℤ) * β * (p : ℤ) + δ * (p : ℤ))) * W.bezout

lemma natCast_R_eq_zero : ((W.R : ℕ) : ZMod W.R) = 0 := ZMod.natCast_self W.R

lemma p_mul_a_eq_one : ((p : ℕ) : ZMod W.R) * ((W.a : ℤ) : ZMod W.R) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod W.R) W.bezout
  push_cast at this
  rw [ZMod.natCast_self, zero_mul, sub_zero] at this
  exact this

theorem exists_cocycle (hp : p.Prime) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 W.R) (i : Option (Fin p)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
        = (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) ∧
      ∃ i' : Option (Fin p),
        repMat W i * (g : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i' := by
  have hp1 : 1 < p := hp.one_lt
  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hRc : (W.R : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set α : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hα
  set β : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hβ
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  obtain ⟨c, hc⟩ := hRc
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (W.R : ℤ) * c, d] := by
    rw [← hc, hα, hβ, hd]
    exact Matrix.eta_fin_two _
  have hdet' : α * d - β * ((W.R : ℤ) * c) = 1 := by
    rw [← hc]; linear_combination hdetG
  have hmemM : ∀ x : ℤ, (((p : ℤ) * (W.R : ℤ) * x : ℤ) : ZMod M) = 0 := by
    intro x
    rw [← W.hM_int]
    push_cast
    simp
  have hR0 := natCast_R_eq_zero W
  have hpa := p_mul_a_eq_one W
  cases i with
  | none =>
    by_cases hqc : (p : ℤ) ∣ c
    ·
      obtain ⟨c', rfl⟩ := hqc
      obtain ⟨x, y, s, t, hdet1, ht, hmat⟩ := mat_mul_normalizes W α β c' d
        (by linear_combination hdet')
      have hdetδ : Matrix.det !![x, y; (p : ℤ) * (W.R : ℤ) * s, t] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination hdet1
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM s
      · show ((t : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        rw [ht]
        push_cast
        rw [hR0]
        linear_combination ((d : ℤ) : ZMod W.R) * hpa
      · rw [repMat_none, hgmat,
          show (W.R : ℤ) * ((p : ℤ) * c') = (p : ℤ) * (W.R : ℤ) * c' by ring]
        exact hmat
    ·
      have hqRc : ¬ (p : ℤ) ∣ (W.R : ℤ) * c :=
        fun hdvd => hqc ((Int.Prime.dvd_mul' hp hdvd).resolve_left (not_dvd_R W hp1))
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hp d hqRc
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![(W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α, -(W.a * α * (j' : ℤ)) + W.a * β + W.b * e;
             (p : ℤ) * (W.R : ℤ) * (α + c), -((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β
               + (p : ℤ) * e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination ((p : ℤ) * W.a - (W.R : ℤ) * W.b) * hdet' + W.bezout
          + ((W.R : ℤ) * α * W.b - W.a * α * (p : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM (α + c)
      · show ((-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e : ℤ) : ZMod W.R)
          = ((d : ℤ) : ZMod W.R)
        have hec := congrArg (Int.cast : ℤ → ZMod W.R) he
        push_cast at hec ⊢
        rw [hR0] at hec ⊢
        linear_combination -hec
      · rw [repMat_none, repMat_some, hgmat]
        show W.mat * _ = _
        rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (p : ℤ) * W.a * α + W.b * ((W.R : ℤ) * c)
            = ((W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α) * 1
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * 0
          ring
        · show (p : ℤ) * W.a * β + W.b * d
            = ((W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α) * (j' : ℤ)
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * (p : ℤ)
          linear_combination W.b * he
        · show (p : ℤ) * (W.R : ℤ) * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * (α + c) * 1
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e) * 0
          ring
        · show (p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * (α + c) * (j' : ℤ)
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e) * (p : ℤ)
          linear_combination (p : ℤ) * he
  | some j =>
    by_cases hpiv : (p : ℤ) ∣ (α + (j : ℤ) * ((W.R : ℤ) * c))
    ·
      obtain ⟨e, he⟩ := hpiv
      have hdetδ : Matrix.det
          !![-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e,
             W.a * β + W.a * d * (j : ℤ) - W.b * e;
             (p : ℤ) * (W.R : ℤ) * (c - d), -((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet'
          + (-((W.R : ℤ) * β * c) - (W.R : ℤ) * c * d * (j : ℤ) + d * e * (p : ℤ)) * W.bezout
          + (-d) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM (c - d)
      · show ((-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        push_cast
        rw [hR0]
        linear_combination ((d : ℤ) : ZMod W.R) * hpa
      · rw [repMat_some, repMat_none, hgmat]
        show _ = _ * W.mat
        rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e) * ((p : ℤ) * W.a)
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * ((p : ℤ) * (W.R : ℤ))
          linear_combination he + (-((p : ℤ) * e)) * W.bezout
        · show 1 * β + (j : ℤ) * d
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e) * W.b
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * (p : ℤ)
          linear_combination (-(β + d * (j : ℤ))) * W.bezout
        · show 0 * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * (c - d) * ((p : ℤ) * W.a)
              + (-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d) * ((p : ℤ) * (W.R : ℤ))
          linear_combination (-((p : ℤ) * (W.R : ℤ) * c)) * W.bezout
        · show 0 * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * (c - d) * W.b
              + (-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d) * (p : ℤ)
          linear_combination (-((p : ℤ) * d)) * W.bezout
    ·
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hp (β + (j : ℤ) * d) hpiv
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![α + (j : ℤ) * ((W.R : ℤ) * c), e;
             (p : ℤ) * (W.R : ℤ) * c, d - (W.R : ℤ) * c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet' + ((W.R : ℤ) * c) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM c
      · show ((d - (W.R : ℤ) * c * (j' : ℤ) : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        push_cast
        rw [hR0]
        ring
      · rw [repMat_some, repMat_some, hgmat]
        rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * 1 + e * 0
          ring
        · show 1 * β + (j : ℤ) * d
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * (j' : ℤ) + e * (p : ℤ)
          linear_combination he
        · show 0 * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * c * 1 + (d - (W.R : ℤ) * c * (j' : ℤ)) * 0
          ring
        · show 0 * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * c * (j' : ℤ) + (d - (W.R : ℤ) * c * (j' : ℤ)) * (p : ℤ)
          ring

section GLtransfer

variable [NeZero M]

def repGL : Option (Fin p) → GL (Fin 2) ℝ
  | none => W.alGL
  | some j => ModularForm.heckeMatrix p (j : ℕ)

@[scoped simp] lemma repGL_none : repGL W none = W.alGL := rfl

@[scoped simp] lemma repGL_some (j : Fin p) : repGL W (some j) = ModularForm.heckeMatrix p (j : ℕ) := rfl

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma repGL_coe (hp : p ≠ 0) (i : Option (Fin p)) :
    (repGL W i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat W i).map (algebraMap ℤ ℝ) := by
  cases i with
  | none => exact W.alGL_coe
  | some j =>
    rw [repGL_some, repMat_some, ModularForm.val_heckeMatrix hp]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y <;> simp

lemma repGL_cocycle_of_int (hp : p ≠ 0) {g δ : SL(2, ℤ)} {i i' : Option (Fin p)}
    (hint : repMat W i * (g : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i') :
    repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * repGL W i' := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (repGL W i : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (repGL W i' : Matrix (Fin 2) (Fin 2) ℝ)
  rw [repGL_coe W hp, repGL_coe W hp, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq,
    ← map_int_mul_eq, hint]

lemma sum_slash_repGL (k : ℤ) (f : UpperHalfPlane → ℂ) :
    ∑ i : Option (Fin p), f ∣[k] repGL W i
      = ModularForm.alSlash W k f + ModularForm.heckeU k p f := by
  rw [Fintype.sum_option, repGL_none, ModularForm.alSlash_def, ModularForm.heckeU_def,
    Finset.sum_range (fun j => f ∣[k] ModularForm.heckeMatrix p j)]
  rfl

end GLtransfer

lemma mem_GammaH_of_congr (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M)
    {u : (ZMod M)ˣ} (hu : u ∈ H)
    (hcongr : (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
      = (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u : ZMod W.R)) :
    δ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  set v : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨δ, hδ⟩ with hv
  have hmap : ZMod.unitsMap (Dvd.intro_left p W.hM.symm) v
      = ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u := by
    ext
    rw [← hcongr, ZMod.unitsMap_val, hv, CohCarrier.val_gamma0Units]
    show (((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod W.R) = _
    rw [ZMod.cast_intCast (Dvd.intro_left p W.hM.symm)]
  have hker : v * u⁻¹ ∈ H := hHp _ (by rw [map_mul, map_inv, hmap, mul_inv_cancel])
  simpa using H.mul_mem hker hu

theorem main [NeZero M] (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ Gamma0 W.R)
    (hgH : ∃ u ∈ H, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = CohCarrier.gamma0Units W.R ⟨g, hg⟩) :
    (ModularForm.alSlash W k f + ModularForm.heckeU k p f) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ)
      = ModularForm.alSlash W k f + ModularForm.heckeU k p f := by
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨u, hu, hug⟩ := hgH

  choose δ hδ hcong m hm using fun i => exists_cocycle W hp hg i

  have hδH : ∀ i, δ i ∈ CohCarrier.GammaH M H := by
    intro i
    refine mem_GammaH_of_congr W H hHp (hδ i) hu ?_
    rw [hcong i, hug, CohCarrier.val_gamma0Units]
    rfl

  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁
    have hg_inv : (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hδ₂ : (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcomb : repMat W i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i₂ := by
      have step : repMat W i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat W i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact repMat_unique W hp.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj
  have hmGL : ∀ i, repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL W (m i) :=
    fun i => repGL_cocycle_of_int W hp0 (hm i)
  rw [← sum_slash_repGL W k f]
  calc (∑ i : Option (Fin p), f ∣[k] repGL W i) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Option (Fin p), (f ∣[k] repGL W i) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.sum_slash]
    _ = ∑ i : Option (Fin p), f ∣[k] (repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin p), f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL W (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin p), (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k]
          repGL W (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin p), f ∣[k] repGL W (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf _ (Subgroup.mem_map.mpr ⟨δ i, hδH i, rfl⟩)]
    _ = ∑ i : Option (Fin p), f ∣[k] repGL W i :=
        hbij.sum_comp fun i => f ∣[k] repGL W i

end AlTrHk
p2m_reactivate "P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk"

end
p2m_reactivate "P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk"

noncomputable section

namespace AlTrHk2

open Matrix CongruenceSubgroup AlTrHk
open scoped MatrixGroups ModularForm

variable {M p : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)

omit [NeZero M] in

theorem Gamma1_le_GammaH (H : Subgroup (ZMod M)ˣ) : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem H

scoped instance finiteIndex_GammaH (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH H)

theorem exists_alGL_mul_eq (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {g : SL(2, ℤ)} (hg : g ∈ CohCarrier.GammaH M H) :
    ∃ δ : SL(2, ℤ), δ ∈ CohCarrier.GammaH M H ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by
  obtain ⟨hg0, hgu⟩ := CohCarrier.mem_GammaH_iff.mp hg
  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hMc : (M : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg0
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMc
  set α : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hα
  set β : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hβ
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (p : ℤ) * (W.R : ℤ) * c', d] := by
    rw [show (p : ℤ) * (W.R : ℤ) * c' = (M : ℤ) * c' by rw [W.hM_int], ← hc', hα, hβ, hd]
    exact Matrix.eta_fin_two _
  have hdet' : α * d - β * ((p : ℤ) * (W.R : ℤ) * c') = 1 := by
    rw [show (p : ℤ) * (W.R : ℤ) * c' = (M : ℤ) * c' by rw [W.hM_int], ← hc']
    linear_combination hdetG
  obtain ⟨x, y, s, t, hdet1, ht, hmat⟩ := mat_mul_normalizes W α β c' d hdet'
  have hdetδ : Matrix.det !![x, y; (p : ℤ) * (W.R : ℤ) * s, t] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet1
  set δ : SL(2, ℤ) := ⟨!![x, y; (p : ℤ) * (W.R : ℤ) * s, t], hdetδ⟩ with hδdef
  have hδ10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (p : ℤ) * (W.R : ℤ) * s := by
    rw [hδdef]; rfl
  have hδ11 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = t := by
    rw [hδdef]; rfl
  have hδ0 : δ ∈ Gamma0 M := by
    rw [Gamma0_mem, hδ10, ← W.hM_int]
    push_cast
    simp
  have hδH : δ ∈ CohCarrier.GammaH M H := by
    refine mem_GammaH_of_congr W H hHp hδ0 hgu ?_
    show ((t : ℤ) : ZMod W.R) = (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) (CohCarrier.gamma0Units M ⟨g, hg0⟩) : ZMod W.R)
    rw [ZMod.unitsMap, Units.coe_map]
    show _ = ZMod.castHom (Dvd.intro_left p W.hM.symm) (ZMod W.R) ((CohCarrier.gamma0Units M ⟨g, hg0⟩ : ZMod M))
    rw [CohCarrier.val_gamma0Units]
    show (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
      = ZMod.castHom (Dvd.intro_left p W.hM.symm) (ZMod W.R) ((( (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M))
    rw [map_intCast, ← hd, hδ11, ht]
    push_cast
    rw [natCast_R_eq_zero W]
    linear_combination ((d : ℤ) : ZMod W.R) * p_mul_a_eq_one W
  refine ⟨δ, hδH, ?_⟩
  refine repGL_cocycle_of_int W hp.ne_zero (i := none) (i' := none) ?_
  show W.mat * (g : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * W.mat
  rw [hgmat, hδdef]
  exact hmat

theorem alSlash_slash_eq_self (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    (ModularForm.alSlash W k f) ∣[k] γ = ModularForm.alSlash W k f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨δ, hδ, hWg⟩ := exists_alGL_mul_eq W hp H hHp hg
  rw [ModularForm.alSlash_def, ← SlashAction.slash_mul]
  show f ∣[k] (W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g) = f ∣[k] W.alGL
  rw [hWg, SlashAction.slash_mul, hf _ (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

def alSlashCusp (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k) : CuspForm (CohCarrier.GammaH M H) k where
  toFun := ModularForm.alSlash W k ⇑F
  slash_action_eq' γ hγ := alSlash_slash_eq_self W hp H hHp k
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ) γ hγ
  holo' := (CuspFormClass.holo F).slash k W.alGL
  zero_at_cusps' hc := by
    show OnePoint.IsZeroAt _ (⇑F ∣[k] W.alGL) k
    rw [← W.alGLQ_map_castHom]
    exact CuspFormClass.isZeroAt_slash_ratCast F W.alGLQ hc

@[scoped simp] theorem coe_alSlashCusp (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(alSlashCusp W hp H hHp k F) = ModularForm.alSlash W k ⇑F := rfl

theorem unitsMap_eq_one_iff_of_eq {N a b : ℕ} (hab : a = b) (ha : a ∣ N) (hb : b ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap ha u = 1 ↔ ZMod.unitsMap hb u = 1 := by subst hab; rfl

theorem unitsMap_val_eq_iff_of_eq {N a b : ℕ} (hab : a = b) (ha : a ∣ N) (hb : b ∣ N) (u : (ZMod N)ˣ)
    (n : ℕ) : (ZMod.unitsMap ha u : ZMod a) = (n : ZMod a) ↔ (ZMod.unitsMap hb u : ZMod b) = (n : ZMod b) := by
  subst hab; rfl

omit [NeZero M] in
theorem dvd_of_datum (W' : ModularForm.AtkinLehnerDatum M p) : p ∣ M := Dvd.intro _ W'.hM.symm

theorem div_eq_R (W' : ModularForm.AtkinLehnerDatum M p) : M / p = W'.R :=
  Nat.div_eq_of_eq_mul_left W'.q_pos (W'.hM.trans (mul_comm _ _))

theorem alSlash_alSlash (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (d : (ZMod M)ˣ)
    (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) = (p : ZMod W.R))
    (F : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W k (ModularForm.alSlash W k ⇑F) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k d F) : UpperHalfPlane → ℂ) := by
  have hR := div_eq_R W
  refine CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH M p (dvd_of_datum W) H ?_ W k d ?_ F
  · intro u hu
    exact hHp u ((unitsMap_eq_one_iff_of_eq hR (Nat.div_dvd_of_dvd (dvd_of_datum W)) (Dvd.intro_left p W.hM.symm) u).mp hu)
  · exact (unitsMap_val_eq_iff_of_eq hR (Nat.div_dvd_of_dvd (dvd_of_datum W)) (Dvd.intro_left p W.hM.symm) d p).mpr hd

theorem isCusp_GammaH_of_isCusp {R : ℕ} [NeZero R] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod R)ˣ) {c : OnePoint ℝ}
    (hc : IsCusp c (CohCarrier.GammaH R H' : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact hc

theorem exists_outside (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k)
    (d : (ZMod M)ˣ)
    (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) = (p : ZMod W.R)) :
    ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) k,
      ⇑G = ⇑(CuspForm.diamondLinH k d F) + (p : ℂ) ^ (2 - k) •
        ModularForm.heckeU k p (ModularForm.alSlash W k ⇑F) := by
  haveI : NeZero W.R := ⟨fun h => NeZero.ne M (by rw [W.hM, h, mul_zero])⟩
  set f : UpperHalfPlane → ℂ := ModularForm.alSlash W k ⇑F with hfdef
  have hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f :=
    alSlash_slash_eq_self W hp H hHp k (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero

  set Gf : UpperHalfPlane → ℂ := ⇑(CuspForm.diamondLinH k d F) + (p : ℂ) ^ (2 - k) •
    ModularForm.heckeU k p f with hGf
  have hGf' : Gf = (p : ℂ) ^ (2 - k) • (ModularForm.alSlash W k f + ModularForm.heckeU k p f) := by
    rw [hGf, smul_add, hfdef, alSlash_alSlash W hp H hHp k d hd F, smul_smul, ← zpow_add₀ hpC,
      show (2 - k) + (k - 2) = 0 by ring, zpow_zero, one_smul]

  have hinv : ∀ γ ∈ (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) :
      Subgroup (GL (Fin 2) ℝ)), Gf ∣[k] γ = Gf := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨hg0, hgu⟩ := CohCarrier.mem_GammaH_iff.mp hg
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp hgu
    rw [hGf']
    have hm := main W hp H hHp k hf g hg0 ⟨u, hu, hug⟩
    exact (ModularForm.SL_smul_slash k g _ _).trans (congrArg ((p : ℂ) ^ (2 - k) • ·) hm)

  have hholf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f := (CuspFormClass.holo F).slash k W.alGL
  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) Gf := by
    rw [hGf]
    exact (CuspFormClass.holo (CuspForm.diamondLinH k d F)).add
      ((ModularForm.mdifferentiable_heckeU hholf k p).const_smul _)

  have hzero : ∀ c : OnePoint ℝ,
      IsCusp c (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) :
        Subgroup (GL (Fin 2) ℝ)) → OnePoint.IsZeroAt c Gf k := by
    intro c hc
    have hc' : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) :=
      isCusp_GammaH_of_isCusp H _ hc
    have h1 : OnePoint.IsZeroAt c (⇑(CuspForm.diamondLinH k d F)) k :=
      CuspFormClass.zero_at_cusps (CuspForm.diamondLinH k d F) hc'
    have h2 : OnePoint.IsZeroAt c (ModularForm.heckeU k p f) k := by
      have := CuspFormClass.isZeroAt_heckeU (alSlashCusp W hp H hHp k F) p hc'
      rwa [coe_alSlashCusp] at this
    rw [hGf]
    intro g hg
    rw [SlashAction.add_slash, ModularForm.smul_slash]
    exact (h1 g hg).add ((h2 g hg).smul _)
  refine ⟨{ toFun := Gf
            slash_action_eq' := fun γ hγ => hinv γ hγ
            holo' := hhol
            zero_at_cusps' := fun hc => hzero _ hc }, ?_⟩
  rfl

theorem coe_diamondLinH_inv_diamondLinH (H : Subgroup (ZMod M)ˣ) (k : ℤ) (d' : (ZMod M)ˣ)
    (F : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(CuspForm.diamondLinH k d'⁻¹ (CuspForm.diamondLinH k d' F)) = ⇑F := by
  have hD := CuspForm.stableD M H k
  rw [CuspForm.coe_diamondLinH_apply k hD, CuspForm.coe_diamondLinH_apply k hD, ← SlashAction.slash_mul,
    ← map_mul]
  have hmem : ((CuspForm.gammaLift M d' : Gamma0 M) : SL(2, ℤ)) * ((CuspForm.gammaLift M d'⁻¹ : Gamma0 M) : SL(2, ℤ))
      ∈ CohCarrier.GammaH M H := by
    refine CohCarrier.mem_GammaH_iff.mpr ⟨(Gamma0 M).mul_mem (CuspForm.gammaLift M d').2 (CuspForm.gammaLift M d'⁻¹).2, ?_⟩
    have : CohCarrier.gamma0Units M ⟨((CuspForm.gammaLift M d' : Gamma0 M) : SL(2, ℤ)) *
        ((CuspForm.gammaLift M d'⁻¹ : Gamma0 M) : SL(2, ℤ)), (Gamma0 M).mul_mem (CuspForm.gammaLift M d').2
          (CuspForm.gammaLift M d'⁻¹).2⟩ =
        CohCarrier.gamma0Units M (CuspForm.gammaLift M d') * CohCarrier.gamma0Units M (CuspForm.gammaLift M d'⁻¹) := by
      rw [← map_mul]; rfl
    rw [this, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift, mul_inv_cancel]
    exact one_mem H
  exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)

theorem exists_inside (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k)
    (d' : (ZMod M)ˣ)
    (hd' : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d' : ZMod W.R) * (p : ZMod W.R) = 1) :
    ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) k,
      ⇑G = ⇑F + (p : ℂ) ^ (2 - k) •
        ModularForm.heckeU k p (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d' F)) := by
  have hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d'⁻¹ : ZMod W.R) = (p : ZMod W.R) := by
    rw [map_inv]
    have hu := Units.inv_mul (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d')

    calc ((ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d')⁻¹ : (ZMod W.R)ˣ).val
        = ((ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d')⁻¹ : (ZMod W.R)ˣ).val *
            ((ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d' : ZMod W.R) * (p : ZMod W.R)) := by rw [hd', mul_one]
      _ = (p : ZMod W.R) := by rw [← mul_assoc, hu, one_mul]
  obtain ⟨G, hG⟩ := exists_outside W hp H hHp k (CuspForm.diamondLinH k d' F) d'⁻¹ hd
  refine ⟨G, ?_⟩
  rw [hG, coe_diamondLinH_inv_diamondLinH]

end AlTrHk2
p2m_reactivate "P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk2"

end
p2m_reactivate "P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.AlTrHk2"

theorem solution
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑F :=
  ⟨AlTrHk2.alSlashCusp W hp H hHp k F, rfl⟩

end S_CuspForm_exists_GammaH_coe_eq_alSlash
end P2MW
export P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash (solution)
