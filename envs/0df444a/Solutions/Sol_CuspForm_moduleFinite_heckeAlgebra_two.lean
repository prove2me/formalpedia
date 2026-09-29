-- Prove2me | solution 1 for CuspForm.moduleFinite_heckeAlgebra_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7a6e234f-dcf1-5869-9914-b75a162aaa92

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two

namespace Fact1

set_option autoImplicit false

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] lemma repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] lemma repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

lemma det_repMat (ℓ : ℕ) (i : Option (Fin ℓ)) : (repMat ℓ i).det = (ℓ : ℤ) := by
  cases i <;> simp [repMat, Matrix.det_fin_two_of]

lemma repMat_unique {ℓ : ℕ} (hℓ : 1 < ℓ) {E : Matrix (Fin 2) (Fin 2) ℤ} {m m' : Option (Fin ℓ)}
    (h : repMat ℓ m' = E * repMat ℓ m) : m' = m := by
  have hℓ' : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
  cases m with
  | none =>
    cases m' with
    | none => rfl
    | some j' =>
      exfalso
      have h00 := congrFun (congrFun h 0) 0
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h00
      have hdvd : (ℓ : ℤ) ∣ 1 := ⟨E 0 0, by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases m' with
    | none =>
      exfalso
      have h10 := congrFun (congrFun h 1) 0
      have h11 := congrFun (congrFun h 1) 1
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h10 h11
      rw [← h10, zero_mul, zero_add] at h11
      have hdvd : (ℓ : ℤ) ∣ 1 := ⟨E 1 1, by linear_combination h11⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    | some j' =>
      have h00 := congrFun (congrFun h 0) 0
      have h01 := congrFun (congrFun h 0) 1
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
      have hcast : ((j' : ℕ) : ZMod ℓ) = ((j : ℕ) : ZMod ℓ) := by
        have : ((j' : ℤ) : ZMod ℓ) = ((E 0 0 * (j : ℤ) + E 0 1 * (ℓ : ℤ) : ℤ) : ZMod ℓ) := by
          exact_mod_cast congrArg (Int.cast : ℤ → ZMod ℓ) h01
        rw [← h00] at this
        push_cast at this
        simpa using this
      have hval : (j' : ℕ) = (j : ℕ) := by
        have hj := ZMod.val_cast_of_lt j.isLt
        have hj' := ZMod.val_cast_of_lt j'.isLt
        rw [← hj, ← hj', hcast]
      exact congrArg some (Fin.ext hval)

lemma exists_cocycle {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _
  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos
    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  cases i with
  | none =>
    by_cases hcdvd : (ℓ : ℤ) ∣ c
    ·
      obtain ⟨c', hc'⟩ := hcdvd
      have hdetδ : Matrix.det !![a, (ℓ : ℤ) * b; c', d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + b * hc'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      ·
        rw [Gamma0_mem]
        show ((c' : ℤ) : ZMod N) = 0
        have hcopN : Nat.Coprime N ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
        have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
          simpa [Int.gcd_natCast_natCast] using hcopN)
        have hNc' : (N : ℤ) ∣ c' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [← hc']
          exact hNc
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a, (ℓ : ℤ) * b; c', d] * repMat ℓ none
        rw [hgmat, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = a * (ℓ : ℤ) + (ℓ : ℤ) * b * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = a * 0 + (ℓ : ℤ) * b * 1
          ring
        · show (0 * a + 1 * c : ℤ) = c' * (ℓ : ℤ) + d * 0
          linear_combination hc'
        · show (0 * b + 1 * d : ℤ) = c' * 0 + d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key c d hcdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - a * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] * repMat ℓ (some j')
        rw [hgmat, repMat_none, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = (ℓ : ℤ) * a * 1 + (b - a * (j' : ℤ)) * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = (ℓ : ℤ) * a * (j' : ℤ) + (b - a * (j' : ℤ)) * (ℓ : ℤ)
          ring
        · show (0 * a + 1 * c : ℤ) = c * 1 + e * 0
          ring
        · show (0 * b + 1 * d : ℤ) = c * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
  | some j =>
    by_cases hpdvd : (ℓ : ℤ) ∣ (a + (j : ℤ) * c)
    ·
      obtain ⟨p', hp'⟩ := hpdvd
      have hdetδ : Matrix.det !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - d * hp'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] * repMat ℓ none
        rw [hgmat, repMat_some, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = p' * (ℓ : ℤ) + (b + (j : ℤ) * d) * 0
          linear_combination hp'
        · show (1 * b + (j : ℤ) * d : ℤ) = p' * 0 + (b + (j : ℤ) * d) * 1
          ring
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = c * (ℓ : ℤ) + (ℓ : ℤ) * d * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = c * 0 + (ℓ : ℤ) * d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + c * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast
        rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
          mul_zero]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
        rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
          ring
        · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
          ring

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGL_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat ℓ i).map (algebraMap ℤ ℝ) := rfl

private lemma mapGL_coe'_HeckeAnalytic (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_HeckeAnalytic (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

def heckeSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i

lemma heckeSlashSum_add (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f g : ℍ → ℂ) :
    heckeSlashSum k ℓ (f + g) = heckeSlashSum k ℓ f + heckeSlashSum k ℓ g := by
  simp only [heckeSlashSum, SlashAction.add_slash]
  exact Finset.sum_add_distrib

theorem heckeSlashSum_slash {N : ℕ} {k : ℤ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeSlashSum k ℓ f) ∣[k] γ = heckeSlashSum k ℓ f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  choose δ hδ m hm using exists_cocycle hℓ hℓN hg
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
    have hcomb : repMat ℓ i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ i₂ := by
      have step : repMat ℓ i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat ℓ i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact repMat_unique hℓ.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj
  have hmGL : ∀ i, repGL ℓ i * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (m i) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ (δ i) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (repGL ℓ (m i) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [repGL_coe, repGL_coe, mapGL_coe'_HeckeAnalytic, mapGL_coe'_HeckeAnalytic, ← map_int_mul_HeckeAnalytic, ← map_int_mul_HeckeAnalytic, hm i]
  calc (heckeSlashSum k ℓ f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Option (Fin ℓ), (f ∣[k] repGL ℓ i) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [heckeSlashSum, SlashAction.sum_slash]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] (repGL ℓ i * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ),
          f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin ℓ),
          (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k] repGL ℓ (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i := hbij.sum_comp fun i => f ∣[k] repGL ℓ i
    _ = heckeSlashSum k ℓ f := rfl

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

private def _root_.Fact1.SlashInvariantForm.hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : SlashInvariantForm (Gamma0 N) k) : SlashInvariantForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := heckeSlashSum k ℓ f
    slash_action_eq' := fun _ hγ => heckeSlashSum_slash hℓ hℓN f.slash_action_eq' hγ }

p2m_export "Fact1.SlashInvariantForm" "hecke"
end SlashInvariantForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace HeckeAnalytic

open OnePoint
open scoped Manifold

def repGLQ (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℚ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGLQ_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGLQ ℓ i : Matrix (Fin 2) (Fin 2) ℚ) = (repMat ℓ i).map (algebraMap ℤ ℚ) := rfl

lemma repGLQ_map_castHom (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGLQ ℓ i).map (Rat.castHom ℝ) = repGL ℓ i := by
  apply Units.ext
  show (Rat.castHom ℝ).mapMatrix ((repGLQ ℓ i : Matrix (Fin 2) (Fin 2) ℚ))
      = (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ)
  rw [repGLQ_coe, repGL_coe, RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1

lemma isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨gQ • c₀, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

lemma isCusp_repGL_smul {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ] (i : Option (Fin ℓ))
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp (repGL ℓ i • c) ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat hc (repGLQ ℓ i) (repGLQ_map_castHom ℓ i)

private lemma isBoundedAt_zero_HeckeAnalytic {c : OnePoint ℝ} {k : ℤ} :
    IsBoundedAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact (Filter.zero_zeroAtFilter _).boundedAtFilter

private lemma isZeroAt_zero_HeckeAnalytic {c : OnePoint ℝ} {k : ℤ} :
    IsZeroAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

private lemma isBoundedAt_finsetSum_HeckeAnalytic {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsBoundedAt c (F i) k) :
    IsBoundedAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isBoundedAt_zero_HeckeAnalytic
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

private lemma isZeroAt_finsetSum_HeckeAnalytic {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsZeroAt c (F i) k) :
    IsZeroAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isZeroAt_zero_HeckeAnalytic
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

lemma heckeSlashSum_mdiff {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlashSum k ℓ f) := by
  show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i)
  exact MDifferentiable.sum fun i _ => hf.slash k (repGL ℓ i)

lemma heckeSlashSum_isBoundedAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (heckeSlashSum k ℓ f) k := by
  show IsBoundedAt c (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i) k
  refine isBoundedAt_finsetSum_HeckeAnalytic _ fun i _ => ?_
  exact IsBoundedAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) i hc))

lemma heckeSlashSum_isZeroAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (heckeSlashSum k ℓ f) k := by
  show IsZeroAt c (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i) k
  refine isZeroAt_finsetSum_HeckeAnalytic _ fun i _ => ?_
  exact IsZeroAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) i hc))

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.Fact1.ModularForm.hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ModularForm (Gamma0 N) k) :
    ModularForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.hecke ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeSlashSum_mdiff f.holo'
    bdd_at_cusps' := fun hc =>
      heckeSlashSum_isBoundedAt (fun _ hc' => f.bdd_at_cusps' hc') hc }

p2m_export "Fact1.ModularForm" "hecke"
end ModularForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.Fact1.CuspForm.hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.hecke ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeSlashSum_mdiff f.holo'
    zero_at_cusps' := fun hc =>
      heckeSlashSum_isZeroAt (fun _ hc' => f.zero_at_cusps' hc') hc }

p2m_export "Fact1.CuspForm" "hecke"
end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace HeckeAnalytic

variable {ℓ : ℕ} [NeZero ℓ]

lemma repGL_entry (i : Option (Fin ℓ)) (a b : Fin 2) :
    (repGL ℓ i) a b = algebraMap ℤ ℝ ((repMat ℓ i) a b) := by
  show ((repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ)) a b = _
  rw [repGL_coe, Matrix.map_apply]

lemma val_det_repGL (i : Option (Fin ℓ)) : ((repGL ℓ i).det : ℝ) = (ℓ : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, repGL_coe]
  have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, det_repMat]
  simp

lemma det_repGL_pos (i : Option (Fin ℓ)) : 0 < ((repGL ℓ i).det : ℝ) := by
  rw [val_det_repGL]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

lemma denom_repGL_some (j : Fin ℓ) (z : ℂ) : denom (repGL ℓ (some j)) z = (ℓ : ℂ) := by
  simp [UpperHalfPlane.denom, repGL_entry, repMat]

lemma denom_repGL_none (z : ℂ) : denom (repGL ℓ none) z = 1 := by
  simp [UpperHalfPlane.denom, repGL_entry, repMat]

lemma num_repGL_some (j : Fin ℓ) (z : ℂ) : num (repGL ℓ (some j)) z = z + (j : ℕ) := by
  simp [UpperHalfPlane.num, repGL_entry, repMat]

lemma num_repGL_none (z : ℂ) : num (repGL ℓ none) z = (ℓ : ℂ) * z := by
  simp [UpperHalfPlane.num, repGL_entry, repMat]

lemma coe_smul_repGL_some (j : Fin ℓ) (τ : ℍ) :
    ((repGL ℓ (some j) • τ : ℍ) : ℂ) = ((τ : ℂ) + (j : ℕ)) / (ℓ : ℂ) := by
  rw [coe_smul_of_det_pos (det_repGL_pos _), num_repGL_some, denom_repGL_some]

lemma coe_smul_repGL_none (τ : ℍ) :
    ((repGL ℓ none • τ : ℍ) : ℂ) = (ℓ : ℂ) * τ := by
  rw [coe_smul_of_det_pos (det_repGL_pos _), num_repGL_none, denom_repGL_none, div_one]

lemma σ_repGL_apply (i : Option (Fin ℓ)) (z : ℂ) : σ (repGL ℓ i) z = z := by
  rw [UpperHalfPlane.σ, if_pos (det_repGL_pos i)]
  simp

lemma slash_repGL_some_apply (k : ℤ) (f : ℍ → ℂ) (j : Fin ℓ) (τ : ℍ) :
    (f ∣[k] repGL ℓ (some j)) τ = (ℓ : ℂ)⁻¹ * f (repGL ℓ (some j) • τ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  rw [ModularForm.slash_apply, σ_repGL_apply, val_det_repGL, denom_repGL_some,
    abs_of_pos hℓR]
  push_cast
  have hexp : (k - 1) + (-k) = (-1 : ℤ) := by ring
  rw [mul_assoc, ← zpow_add₀ hℓC, hexp, _root_.zpow_neg_one]
  ring

lemma slash_repGL_none_apply (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] repGL ℓ none) τ = (ℓ : ℂ) ^ (k - 1) * f (repGL ℓ none • τ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  rw [ModularForm.slash_apply, σ_repGL_apply, val_det_repGL, denom_repGL_none,
    abs_of_pos hℓR, _root_.one_zpow, mul_one]
  push_cast
  ring

local notation "𝕢" => Function.Periodic.qParam

lemma qParam_one_eq (z : ℂ) : 𝕢 1 z = Complex.exp (2 * π * Complex.I * z) := by
  simp [Function.Periodic.qParam]

lemma qParam_eq (h : ℝ) (z : ℂ) : 𝕢 h z = Complex.exp (2 * π * Complex.I * z / h) := rfl

lemma qParam_one_smul_none (τ : ℍ) :
    𝕢 1 ((repGL ℓ none • τ : ℍ) : ℂ) = (𝕢 1 (τ : ℂ)) ^ ℓ := by
  rw [coe_smul_repGL_none, qParam_one_eq, qParam_one_eq, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma qParam_one_smul_some (j : Fin ℓ) (τ : ℍ) :
    𝕢 1 ((repGL ℓ (some j) • τ : ℍ) : ℂ)
      = Complex.exp (2 * π * Complex.I * (j : ℕ) / ℓ) * 𝕢 (ℓ : ℝ) (τ : ℂ) := by
  rw [coe_smul_repGL_some, qParam_one_eq, qParam_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qParam_pow_period (τ : ℍ) : (𝕢 (ℓ : ℝ) (τ : ℂ)) ^ ℓ = 𝕢 1 (τ : ℂ) := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  rw [qParam_eq, qParam_one_eq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

lemma sum_exp_pow (L : ℕ) (hL : L ≠ 0) (m : ℕ) :
    ∑ j : Fin L, (Complex.exp (2 * π * Complex.I * (j : ℕ) / L)) ^ m
      = if L ∣ m then (L : ℂ) else 0 := by
  have hterm : ∀ j : Fin L,
      (Complex.exp (2 * π * Complex.I * (j : ℕ) / L)) ^ m
        = (Complex.exp (2 * π * Complex.I * (m : ℕ) / L)) ^ (j : ℕ) := by
    intro j
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  set ζ : ℂ := Complex.exp (2 * π * Complex.I * (m : ℕ) / L) with hζ
  rw [show ∑ j : Fin L, ζ ^ (j : ℕ) = ∑ j ∈ Finset.range L, ζ ^ j from
    Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) L]
  by_cases hdvd : L ∣ m
  · have hζ1 : ζ = 1 := by
      rw [hζ]
      exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hL).mpr hdvd
    simp [hζ1, hdvd]
  · have hζ1 : ζ ≠ 1 := by
      rw [hζ]
      intro h
      exact hdvd ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hL).mp h)
    have hζL : ζ ^ L = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have harg : (L : ℂ) * (2 * π * Complex.I * (m : ℕ) / L)
          = 2 * π * Complex.I * ((L * m : ℕ) : ℂ) / ((L : ℕ) : ℂ) := by
        push_cast
        ring
      rw [harg]
      exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hL).mpr ⟨m, rfl⟩
    rw [geom_sum_eq hζ1, hζL, sub_self, zero_div, if_neg hdvd]

lemma one_mem_strictPeriods_Gamma0 {N : ℕ} :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

lemma hasSum_qExpansion_gamma0 {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma0 N) k] (f : F) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 f).coeff m • 𝕢 1 (τ : ℂ) ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty
      ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).isCusp_of_mem_strictPeriods
      one_pos one_mem_strictPeriods_Gamma0⟩
  exact hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_Gamma0)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

def heckeCoeff {F : Type*} [FunLike F ℍ ℂ] (ℓ : ℕ) (k : ℤ) (f : F) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff (ℓ * n)
    + (ℓ : ℂ) ^ (k - 1) * (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0)

lemma hasSum_some_part {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma0 N) k] (f : F) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff (ℓ * n) * 𝕢 1 (τ : ℂ) ^ n)
      (∑ j : Fin ℓ, ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j)) τ) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hj : ∀ j : Fin ℓ,
      HasSum (fun m : ℕ ↦ (ℓ : ℂ)⁻¹ * ((qExpansion 1 f).coeff m •
          𝕢 1 ((repGL ℓ (some j) • τ : ℍ) : ℂ) ^ m))
        (((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j)) τ) := by
    intro j
    have h := (hasSum_qExpansion_gamma0 f (repGL ℓ (some j) • τ)).mul_left (ℓ : ℂ)⁻¹
    rwa [← slash_repGL_some_apply k (⇑f) j τ] at h
  have hsum := hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin ℓ))) => hj j)
  have hcoef : ∀ m : ℕ,
      (∑ j : Fin ℓ, (ℓ : ℂ)⁻¹ * ((qExpansion 1 f).coeff m •
          𝕢 1 ((repGL ℓ (some j) • τ : ℍ) : ℂ) ^ m))
        = if ℓ ∣ m then (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m else 0 := by
    intro m
    have hterm : ∀ j : Fin ℓ,
        (ℓ : ℂ)⁻¹ * ((qExpansion 1 f).coeff m •
            𝕢 1 ((repGL ℓ (some j) • τ : ℍ) : ℂ) ^ m)
          = (ℓ : ℂ)⁻¹ * (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m *
              (Complex.exp (2 * π * Complex.I * (j : ℕ) / ℓ)) ^ m := by
      intro j
      rw [qParam_one_smul_some, smul_eq_mul, mul_pow]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, sum_exp_pow ℓ hℓ m]
    by_cases hdvd : ℓ ∣ m
    · rw [if_pos hdvd, if_pos hdvd]
      have hre : (ℓ : ℂ)⁻¹ * (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m * (ℓ : ℂ)
          = ((ℓ : ℂ)⁻¹ * (ℓ : ℂ)) * ((qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m) := by
        ring
      rw [hre, inv_mul_cancel₀ hℓC, one_mul]
    · rw [if_neg hdvd, if_neg hdvd, mul_zero]
  have hsum2 : HasSum
      (fun m : ℕ ↦ if ℓ ∣ m then (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m else 0)
      (∑ j : Fin ℓ, ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j)) τ) :=
    HasSum.congr_fun hsum (fun m => (hcoef m).symm)
  have hinj : Function.Injective (fun m : ℕ ↦ ℓ * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h
  have hvanish : ∀ m : ℕ, m ∉ Set.range (fun m : ℕ ↦ ℓ * m) →
      (if ℓ ∣ m then (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m else 0) = 0 := by
    intro m hm
    rw [if_neg]
    rintro ⟨c, hc⟩
    exact hm ⟨c, hc.symm⟩
  have h2 := (Function.Injective.hasSum_iff hinj hvanish).mpr hsum2
  have hfn : (fun n : ℕ ↦ (qExpansion 1 f).coeff (ℓ * n) * 𝕢 1 (τ : ℂ) ^ n)
      = (fun m : ℕ ↦ if ℓ ∣ m then (qExpansion 1 f).coeff m * 𝕢 (ℓ : ℝ) (τ : ℂ) ^ m else 0)
        ∘ (fun m : ℕ ↦ ℓ * m) := by
    funext n
    simp only [Function.comp_apply]
    rw [if_pos ⟨n, rfl⟩, pow_mul, qParam_pow_period]
  rw [hfn]
  exact h2

lemma hasSum_none_part {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma0 N) k] (f : F) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((ℓ : ℂ) ^ (k - 1) *
        (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0)) * 𝕢 1 (τ : ℂ) ^ n)
      (((⇑f : ℍ → ℂ) ∣[k] repGL ℓ none) τ) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have h := (hasSum_qExpansion_gamma0 f (repGL ℓ none • τ)).mul_left ((ℓ : ℂ) ^ (k - 1))
  rw [← slash_repGL_none_apply k (⇑f) τ] at h
  have hinj : Function.Injective (fun m : ℕ ↦ ℓ * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h
  have hvanish : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ ↦ ℓ * m) →
      ((ℓ : ℂ) ^ (k - 1) *
        (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0)) * 𝕢 1 (τ : ℂ) ^ n = 0 := by
    intro n hn
    rw [if_neg, mul_zero, zero_mul]
    rintro ⟨c, hc⟩
    exact hn ⟨c, hc.symm⟩
  refine (Function.Injective.hasSum_iff hinj hvanish).mp ?_
  have hfn : ((fun n : ℕ ↦ ((ℓ : ℂ) ^ (k - 1) *
        (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0)) * 𝕢 1 (τ : ℂ) ^ n)
      ∘ (fun m : ℕ ↦ ℓ * m))
      = fun m : ℕ ↦ (ℓ : ℂ) ^ (k - 1) * ((qExpansion 1 f).coeff m •
          𝕢 1 ((repGL ℓ none • τ : ℍ) : ℂ) ^ m) := by
    funext m
    simp only [Function.comp_apply]
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hℓ),
      qParam_one_smul_none, ← pow_mul, smul_eq_mul]
    ring
  rw [hfn]
  exact h

theorem hasSum_heckeSlashSum {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma0 N) k] (f : F) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ heckeCoeff ℓ k f n • 𝕢 1 (τ : ℂ) ^ n)
      (heckeSlashSum k ℓ (⇑f) τ) := by
  have hU := hasSum_some_part (ℓ := ℓ) (k := k) f τ
  have hV := hasSum_none_part (ℓ := ℓ) (k := k) f τ
  have hUV := hU.add hV
  have hsplit : heckeSlashSum k ℓ (⇑f) τ
      = (∑ j : Fin ℓ, ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j)) τ)
        + ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ none) τ := by
    show (∑ i : Option (Fin ℓ), ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ i)) τ = _
    rw [Finset.sum_apply, Fintype.sum_option]
    exact add_comm _ _
  rw [hsplit]
  have hfn : (fun n : ℕ ↦ heckeCoeff ℓ k f n • 𝕢 1 (τ : ℂ) ^ n)
      = fun n : ℕ ↦ (qExpansion 1 f).coeff (ℓ * n) * 𝕢 1 (τ : ℂ) ^ n
          + ((ℓ : ℂ) ^ (k - 1) *
            (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0)) * 𝕢 1 (τ : ℂ) ^ n := by
    funext n
    simp only [heckeCoeff, smul_eq_mul]
    ring
  rw [hfn]
  exact hUV

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma hecke_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    ⇑(ModularForm.hecke ℓ hℓ hℓN f) = heckeSlashSum k ℓ (⇑f) := rfl

theorem qExpansion_hecke_coeff (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.hecke ℓ hℓ hℓN f)).coeff n
      = (qExpansion 1 f).coeff (ℓ * n)
        + (ℓ : ℂ) ^ (k - 1) * (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    (Γ := ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))
    one_mem_strictPeriods_Gamma0 (f := ModularForm.hecke ℓ hℓ hℓN f)
    (c := heckeCoeff ℓ k f) (fun τ => by
      rw [hecke_coe]
      exact hasSum_heckeSlashSum f τ) n
  rw [← h]
  rfl

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup PowerSeries

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma hecke_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (Gamma0 N) k) :
    ⇑(CuspForm.hecke ℓ hℓ hℓN f) = heckeSlashSum k ℓ (⇑f) := rfl

theorem qExpansion_hecke_coeff (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.hecke ℓ hℓ hℓN f)).coeff n
      = (qExpansion 1 f).coeff (ℓ * n)
        + (ℓ : ℂ) ^ (k - 1) * (if ℓ ∣ n then (qExpansion 1 f).coeff (n / ℓ) else 0) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    (Γ := ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))
    one_mem_strictPeriods_Gamma0 (f := CuspForm.hecke ℓ hℓ hℓN f)
    (c := heckeCoeff ℓ k f) (fun τ => by
      rw [hecke_coe]
      exact hasSum_heckeSlashSum f τ) n
  rw [← h]
  rfl

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace HeckeAnalytic

lemma heckeSlashSum_smul (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (c : ℂ) (f : ℍ → ℂ) :
    heckeSlashSum k ℓ (c • f) = c • heckeSlashSum k ℓ f := by
  simp only [heckeSlashSum, ModularForm.smul_slash, σ_repGL_apply]
  rw [Finset.smul_sum]

theorem heckeCoeff_comm {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (a : ℕ → ℂ) (L L' : ℂ) (n : ℕ) :
    a (ℓ' * (ℓ * n)) + L' * (if ℓ' ∣ ℓ * n then a (ℓ * n / ℓ') else 0)
      + L * (if ℓ ∣ n then
          a (ℓ' * (n / ℓ)) + L' * (if ℓ' ∣ n / ℓ then a (n / ℓ / ℓ') else 0) else 0)
    = a (ℓ * (ℓ' * n)) + L * (if ℓ ∣ ℓ' * n then a (ℓ' * n / ℓ) else 0)
      + L' * (if ℓ' ∣ n then
          a (ℓ * (n / ℓ')) + L * (if ℓ ∣ n / ℓ' then a (n / ℓ' / ℓ) else 0) else 0) := by
  have hco : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
  have hco' : Nat.Coprime ℓ' ℓ := hco.symm
  have h1 : ℓ' ∣ ℓ * n ↔ ℓ' ∣ n := by
    rw [Nat.Prime.dvd_mul hℓ', Nat.prime_dvd_prime_iff_eq hℓ' hℓ]
    exact or_iff_right (Ne.symm hne)
  have h2 : ℓ ∣ ℓ' * n ↔ ℓ ∣ n := by
    rw [Nat.Prime.dvd_mul hℓ, Nat.prime_dvd_prime_iff_eq hℓ hℓ']
    exact or_iff_right hne
  by_cases hn1 : ℓ ∣ n <;> by_cases hn2 : ℓ' ∣ n
  ·
    have h3 : ℓ' ∣ n / ℓ := by
      obtain ⟨m, rfl⟩ := hn1
      rw [Nat.mul_div_cancel_left m hℓ.pos]
      exact hco'.dvd_of_dvd_mul_left hn2
    have h4 : ℓ ∣ n / ℓ' := by
      obtain ⟨m, rfl⟩ := hn2
      rw [Nat.mul_div_cancel_left m hℓ'.pos]
      exact hco.dvd_of_dvd_mul_left hn1
    rw [if_pos hn1, if_pos hn2, if_pos (h1.mpr hn2), if_pos (h2.mpr hn1), if_pos h3, if_pos h4,
        Nat.mul_div_assoc ℓ hn2, Nat.mul_div_assoc ℓ' hn1,
        Nat.div_div_eq_div_mul n ℓ ℓ', Nat.div_div_eq_div_mul n ℓ' ℓ,
        mul_left_comm ℓ' ℓ n, Nat.mul_comm ℓ' ℓ]
    ring
  ·
    have h5 : ¬ ℓ' ∣ n / ℓ := fun hd => hn2 (hd.trans (Nat.div_dvd_of_dvd hn1))
    rw [if_pos hn1, if_neg hn2, if_neg (fun h => hn2 (h1.mp h)), if_pos (h2.mpr hn1), if_neg h5,
        Nat.mul_div_assoc ℓ' hn1, mul_left_comm ℓ' ℓ n]
    ring
  ·
    have h5 : ¬ ℓ ∣ n / ℓ' := fun hd => hn1 (hd.trans (Nat.div_dvd_of_dvd hn2))
    rw [if_neg hn1, if_pos hn2, if_pos (h1.mpr hn2), if_neg (fun h => hn1 (h2.mp h)), if_neg h5,
        Nat.mul_div_assoc ℓ hn2, mul_left_comm ℓ' ℓ n]
    ring
  ·
    rw [if_neg hn1, if_neg hn2, if_neg (fun h => hn2 (h1.mp h)), if_neg (fun h => hn1 (h2.mp h)),
        mul_left_comm ℓ' ℓ n]
    ring

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma hecke_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f g : ModularForm (Gamma0 N) k) :
    ModularForm.hecke ℓ hℓ hℓN (f + g)
      = ModularForm.hecke ℓ hℓ hℓN f + ModularForm.hecke ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [hecke_coe, ModularForm.coe_add, Pi.add_apply, heckeSlashSum_add]

lemma hecke_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (c : ℂ)
    (f : ModularForm (Gamma0 N) k) :
    ModularForm.hecke ℓ hℓ hℓN (c • f) = c • ModularForm.hecke ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  show heckeSlashSum k ℓ (c • ⇑f) τ = c • heckeSlashSum k ℓ (⇑f) τ
  rw [heckeSlashSum_smul]
  rfl

private def _root_.Fact1.ModularForm.heckeHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    ModularForm (Gamma0 N) k →ₗ[ℂ] ModularForm (Gamma0 N) k where
  toFun := ModularForm.hecke ℓ hℓ hℓN
  map_add' := hecke_add ℓ hℓ hℓN
  map_smul' := hecke_smul ℓ hℓ hℓN

p2m_export "Fact1.ModularForm" "heckeHom"
@[scoped simp] private lemma _root_.Fact1.ModularForm.heckeHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    heckeHom ℓ hℓ hℓN f = ModularForm.hecke ℓ hℓ hℓN f := rfl

p2m_export "Fact1.ModularForm" "heckeHom_apply"
omit [NeZero N] in

theorem eq_of_qExpansion_eq {f g : ModularForm (Gamma0 N) k}
    (h : qExpansion 1 f = qExpansion 1 g) : f = g := by
  ext τ
  have hf := hasSum_qExpansion_gamma0 f τ
  have hg := hasSum_qExpansion_gamma0 g τ
  rw [← h] at hg
  exact hf.unique hg

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup PowerSeries

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma hecke_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f g : CuspForm (Gamma0 N) k) :
    CuspForm.hecke ℓ hℓ hℓN (f + g)
      = CuspForm.hecke ℓ hℓ hℓN f + CuspForm.hecke ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [hecke_coe, CuspForm.coe_add, Pi.add_apply, heckeSlashSum_add]

lemma hecke_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (c : ℂ) (f : CuspForm (Gamma0 N) k) :
    CuspForm.hecke ℓ hℓ hℓN (c • f) = c • CuspForm.hecke ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  show heckeSlashSum k ℓ (c • ⇑f) τ = c • heckeSlashSum k ℓ (⇑f) τ
  rw [heckeSlashSum_smul]
  rfl

def heckeHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N) k where
  toFun := CuspForm.hecke ℓ hℓ hℓN
  map_add' := hecke_add ℓ hℓ hℓN
  map_smul' := hecke_smul ℓ hℓ hℓN

@[scoped simp] lemma heckeHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    heckeHom ℓ hℓ hℓN f = CuspForm.hecke ℓ hℓ hℓN f := rfl

omit [NeZero N] in

theorem eq_of_qExpansion_eq {f g : CuspForm (Gamma0 N) k}
    (h : qExpansion 1 f = qExpansion 1 g) : f = g := by
  ext τ
  have hf := hasSum_qExpansion_gamma0 f τ
  have hg := hasSum_qExpansion_gamma0 g τ
  rw [← h] at hg
  exact hf.unique hg

theorem qExpansion_hecke_comm_coeff (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.hecke ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f))).coeff n
      = (qExpansion 1 (CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.hecke ℓ hℓ hℓN f))).coeff n := by
  simp only [qExpansion_hecke_coeff]
  exact HeckeAnalytic.heckeCoeff_comm hℓ hℓ' hne (fun m => (qExpansion 1 f).coeff m)
    ((ℓ : ℂ) ^ (k - 1)) ((ℓ' : ℂ) ^ (k - 1)) n

theorem qExpansion_hecke_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    qExpansion 1 (CuspForm.hecke ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f))
      = qExpansion 1 (CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.hecke ℓ hℓ hℓN f)) := by
  ext n
  exact qExpansion_hecke_comm_coeff ℓ ℓ' hℓ hℓ' hne hℓN hℓ'N f n

theorem hecke_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm.hecke ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f)
      = CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.hecke ℓ hℓ hℓN f) :=
  eq_of_qExpansion_eq (qExpansion_hecke_comm ℓ ℓ' hℓ hℓ' hne hℓN hℓ'N f)

theorem commute_heckeHom (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) :
    Commute (heckeHom (N := N) (k := k) ℓ hℓ hℓN) (heckeHom ℓ' hℓ' hℓ'N) := by
  refine LinearMap.ext fun f => ?_
  simpa only [Module.End.mul_apply, heckeHom_apply] using
    hecke_comm ℓ ℓ' hℓ hℓ' hne hℓN hℓ'N f

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function PowerSeries
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace CuspForm

section HeckeAlgebraDef

variable (N : ℕ) [NeZero N] (k : ℤ)

def heckeSet : Set (Module.End ℂ (CuspForm (Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), T = heckeHom ℓ hℓ hℓN}

def heckeAlgebraC : Subalgebra ℂ (Module.End ℂ (CuspForm (Gamma0 N) k)) :=
  Algebra.adjoin ℂ (heckeSet N k)

end HeckeAlgebraDef
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section HeckeAlgebraBasic

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma heckeHom_mem_heckeSet (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (heckeHom ℓ hℓ hℓN : Module.End ℂ (CuspForm (Gamma0 N) k)) ∈ heckeSet N k :=
  ⟨ℓ, hℓ, hℓN, rfl⟩

lemma heckeSet_mul_comm :
    ∀ a ∈ heckeSet N k, ∀ b ∈ heckeSet N k, a * b = b * a := by
  rintro a ⟨ℓ, hℓ, hℓN, rfl⟩ b ⟨ℓ', hℓ', hℓ'N, rfl⟩
  rcases eq_or_ne ℓ ℓ' with rfl | hne
  · rfl
  · exact (commute_heckeHom ℓ ℓ' hℓ hℓ' hne hℓN hℓ'N).eq

lemma commute_of_mem_heckeAlgebra {T S : Module.End ℂ (CuspForm (Gamma0 N) k)}
    (hT : T ∈ heckeAlgebraC N k) (hS : S ∈ heckeAlgebraC N k) : Commute T S := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hS fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT fun c hc =>
    (heckeSet_mul_comm b hb c hc)).symm

end HeckeAlgebraBasic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section QCoeffLinear

variable {N : ℕ} {k : ℤ}

end QCoeffLinear
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section EigenCharacter

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (f : CuspForm (Gamma0 N) k)

end EigenCharacter
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section HeckeAlgebraCommRing

variable {N : ℕ} [NeZero N] {k : ℤ}

scoped instance : CommRing (heckeAlgebraC N k) :=
  { (inferInstance : Ring (heckeAlgebraC N k)) with
    mul_comm := fun T S => Subtype.ext ((commute_of_mem_heckeAlgebra T.2 S.2).eq) }

end HeckeAlgebraCommRing
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

set_option autoImplicit false

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace HeckeAnalytic

lemma exists_cocycle_U {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (j : Fin ℓ) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ j' : Fin ℓ,
      repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some j') := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _
  have hℓc : (ℓ : ℤ) ∣ c := dvd_trans (by exact_mod_cast hℓN) hNc
  have hpdvd : ¬ (ℓ : ℤ) ∣ (a + (j : ℤ) * c) := by
    intro hdvd
    have hjc : (ℓ : ℤ) ∣ (j : ℤ) * c := hℓc.mul_left _
    have hla : (ℓ : ℤ) ∣ a := by
      have h3 := dvd_sub hdvd hjc
      have h4 : a + (j : ℤ) * c - (j : ℤ) * c = a := by ring
      rwa [h4] at h3
    have h1 : (ℓ : ℤ) ∣ 1 := by
      have h5 : (ℓ : ℤ) ∣ a * d - b * c := dvd_sub (hla.mul_right d) (hℓc.mul_left b)
      rwa [hdetG] at h5
    have h6 := Int.le_of_dvd one_pos h1
    have hℓ1 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
    omega
  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos
    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
  obtain ⟨e, he⟩ := hj'
  have hdetδ : Matrix.det
      !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdetG + c * he
  refine ⟨⟨_, hdetδ⟩, ?_, j', ?_⟩
  ·
    rw [Gamma0_mem]
    show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
    push_cast
    rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
      mul_zero]
  · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
    rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
      ring
    · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
      linear_combination he
    · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
      ring
    · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
      ring

def heckeUSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j : Fin ℓ, f ∣[k] repGL ℓ (some j)

lemma heckeUSlashSum_add (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f g : ℍ → ℂ) :
    heckeUSlashSum k ℓ (f + g) = heckeUSlashSum k ℓ f + heckeUSlashSum k ℓ g := by
  simp only [heckeUSlashSum, SlashAction.add_slash]
  exact Finset.sum_add_distrib

lemma heckeUSlashSum_smul (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (c : ℂ) (f : ℍ → ℂ) :
    heckeUSlashSum k ℓ (c • f) = c • heckeUSlashSum k ℓ f := by
  simp only [heckeUSlashSum, ModularForm.smul_slash, σ_repGL_apply]
  rw [Finset.smul_sum]

private lemma mapGL_coe_eq_HeckeU (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq_HeckeU (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem heckeUSlashSum_slash {N : ℕ} {k : ℤ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeUSlashSum k ℓ f) ∣[k] γ = heckeUSlashSum k ℓ f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  choose δ hδ m hm using exists_cocycle_U hℓ hℓN hg
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
    have hcomb : repMat ℓ (some i₁) =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some i₂) := by
      have step : repMat ℓ (some i₁) * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat ℓ (some i₁) * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some (m i₂)) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                    repMat ℓ (some (m i₂)))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact Option.some_injective _ (repMat_unique hℓ.one_lt hcomb)
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj
  have hmGL : ∀ i, repGL ℓ (some i) * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (some (m i)) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repGL ℓ (some i) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ (δ i) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (repGL ℓ (some (m i)) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [repGL_coe, repGL_coe, mapGL_coe_eq_HeckeU, mapGL_coe_eq_HeckeU, ← map_int_mul_eq_HeckeU, ← map_int_mul_eq_HeckeU,
      hm i]
  calc (heckeUSlashSum k ℓ f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Fin ℓ, (f ∣[k] repGL ℓ (some i)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [heckeUSlashSum, SlashAction.sum_slash]
    _ = ∑ i : Fin ℓ, f ∣[k] (repGL ℓ (some i) * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Fin ℓ,
          f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (some (m i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Fin ℓ,
          (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k] repGL ℓ (some (m i)) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Fin ℓ, f ∣[k] repGL ℓ (some (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Fin ℓ, f ∣[k] repGL ℓ (some i) :=
        hbij.sum_comp fun i => f ∣[k] repGL ℓ (some i)
    _ = heckeUSlashSum k ℓ f := rfl

open OnePoint

private lemma isBoundedAt_zero_HeckeU {c : OnePoint ℝ} {k : ℤ} :
    IsBoundedAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact (Filter.zero_zeroAtFilter _).boundedAtFilter

private lemma isZeroAt_zero_HeckeU {c : OnePoint ℝ} {k : ℤ} :
    IsZeroAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

private lemma isBoundedAt_finsetSum_HeckeU {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsBoundedAt c (F i) k) :
    IsBoundedAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isBoundedAt_zero_HeckeU
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

private lemma isZeroAt_finsetSum_HeckeU {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsZeroAt c (F i) k) :
    IsZeroAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isZeroAt_zero_HeckeU
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

lemma heckeUSlashSum_mdiff {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeUSlashSum k ℓ f) := by
  show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j))
  exact MDifferentiable.sum fun i _ => hf.slash k (repGL ℓ (Option.some i))

lemma heckeUSlashSum_isBoundedAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (heckeUSlashSum k ℓ f) k := by
  show IsBoundedAt c (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j)) k
  refine isBoundedAt_finsetSum_HeckeU _ fun i _ => ?_
  exact IsBoundedAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) (Option.some i) hc))

lemma heckeUSlashSum_isZeroAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (heckeUSlashSum k ℓ f) k := by
  show IsZeroAt c (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j)) k
  refine isZeroAt_finsetSum_HeckeU _ fun i _ => ?_
  exact IsZeroAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) (Option.some i) hc))

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

private def _root_.Fact1.SlashInvariantForm.heckeU (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : SlashInvariantForm (Gamma0 N) k) : SlashInvariantForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := heckeUSlashSum k ℓ f
    slash_action_eq' := fun _ hγ => heckeUSlashSum_slash hℓ hℓN f.slash_action_eq' hγ }

p2m_export "Fact1.SlashInvariantForm" "heckeU"
end SlashInvariantForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

def heckeUForm (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : ModularForm (Gamma0 N) k) :
    ModularForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.heckeU ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeUSlashSum_mdiff f.holo'
    bdd_at_cusps' := fun hc =>
      heckeUSlashSum_isBoundedAt (fun _ hc' => f.bdd_at_cusps' hc') hc }

lemma heckeU_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    ⇑(ModularForm.heckeUForm ℓ hℓ hℓN f) = heckeUSlashSum k ℓ (⇑f) := rfl

lemma heckeUForm_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f g : ModularForm (Gamma0 N) k) :
    ModularForm.heckeUForm ℓ hℓ hℓN (f + g)
      = ModularForm.heckeUForm ℓ hℓ hℓN f + ModularForm.heckeUForm ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [heckeU_coe, ModularForm.coe_add, Pi.add_apply, heckeUSlashSum_add]

lemma heckeUForm_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (c : ℂ)
    (f : ModularForm (Gamma0 N) k) :
    ModularForm.heckeUForm ℓ hℓ hℓN (c • f) = c • ModularForm.heckeUForm ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  show heckeUSlashSum k ℓ (c • ⇑f) τ = c • heckeUSlashSum k ℓ (⇑f) τ
  rw [heckeUSlashSum_smul]
  rfl

private def _root_.Fact1.ModularForm.heckeUHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    ModularForm (Gamma0 N) k →ₗ[ℂ] ModularForm (Gamma0 N) k where
  toFun := ModularForm.heckeUForm ℓ hℓ hℓN
  map_add' := heckeUForm_add ℓ hℓ hℓN
  map_smul' := heckeUForm_smul ℓ hℓ hℓN

p2m_export "Fact1.ModularForm" "heckeUHom"
@[scoped simp] private lemma _root_.Fact1.ModularForm.heckeUHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    heckeUHom ℓ hℓ hℓN f = ModularForm.heckeUForm ℓ hℓ hℓN f := rfl

p2m_export "Fact1.ModularForm" "heckeUHom_apply"
end ModularForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.Fact1.CuspForm.heckeU (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.heckeU ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeUSlashSum_mdiff f.holo'
    zero_at_cusps' := fun hc =>
      heckeUSlashSum_isZeroAt (fun _ hc' => f.zero_at_cusps' hc') hc }

p2m_export "Fact1.CuspForm" "heckeU"
lemma heckeU_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : CuspForm (Gamma0 N) k) :
    ⇑(CuspForm.heckeU ℓ hℓ hℓN f) = heckeUSlashSum k ℓ (⇑f) := rfl

lemma heckeU_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f g : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (f + g)
      = CuspForm.heckeU ℓ hℓ hℓN f + CuspForm.heckeU ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [heckeU_coe, CuspForm.coe_add, Pi.add_apply, heckeUSlashSum_add]

lemma heckeU_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (c : ℂ) (f : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (c • f) = c • CuspForm.heckeU ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  show heckeUSlashSum k ℓ (c • ⇑f) τ = c • heckeUSlashSum k ℓ (⇑f) τ
  rw [heckeUSlashSum_smul]
  rfl

def heckeUHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N) k where
  toFun := CuspForm.heckeU ℓ hℓ hℓN
  map_add' := heckeU_add ℓ hℓ hℓN
  map_smul' := heckeU_smul ℓ hℓ hℓN

@[scoped simp] lemma heckeUHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    heckeUHom ℓ hℓ hℓN f = CuspForm.heckeU ℓ hℓ hℓN f := rfl

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace HeckeAnalytic

local notation "𝕢" => Function.Periodic.qParam

variable {ℓ : ℕ} [NeZero ℓ]

theorem hasSum_heckeUSlashSum {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma0 N) k] (f : F) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff (ℓ * n) • 𝕢 1 (τ : ℂ) ^ n)
      (heckeUSlashSum k ℓ (⇑f) τ) := by
  have h := hasSum_some_part (ℓ := ℓ) (k := k) f τ
  have hval : heckeUSlashSum k ℓ (⇑f) τ
      = ∑ j : Fin ℓ, ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j)) τ := by
    show (∑ j : Fin ℓ, ((⇑f : ℍ → ℂ) ∣[k] repGL ℓ (some j))) τ = _
    rw [Finset.sum_apply]
  rw [hval]
  exact h.congr_fun fun n => by rw [smul_eq_mul]

end HeckeAnalytic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem qExpansion_heckeU_coeff (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.heckeUForm ℓ hℓ hℓN f)).coeff n = (qExpansion 1 f).coeff (ℓ * n) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    (Γ := ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))
    one_mem_strictPeriods_Gamma0 (f := ModularForm.heckeUForm ℓ hℓ hℓN f)
    (c := fun n => (qExpansion 1 f).coeff (ℓ * n)) (fun τ => by
      rw [heckeU_coe]
      exact hasSum_heckeUSlashSum f τ) n
  exact h.symm

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem qExpansion_heckeU_coeff (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : CuspForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.heckeU ℓ hℓ hℓN f)).coeff n = (qExpansion 1 f).coeff (ℓ * n) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    (Γ := ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))
    one_mem_strictPeriods_Gamma0 (f := CuspForm.heckeU ℓ hℓ hℓN f)
    (c := fun n => (qExpansion 1 f).coeff (ℓ * n)) (fun τ => by
      rw [heckeU_coe]
      exact hasSum_heckeUSlashSum f τ) n
  exact h.symm

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function PowerSeries
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem qExpansion_heckeU_hecke_comm_coeff (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.heckeU ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f))).coeff n
      = (qExpansion 1 (CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f))).coeff n := by
  have hne : ℓ' ≠ ℓ := by rintro rfl; exact hℓ'N hℓN
  have h1 : ℓ' ∣ ℓ * n ↔ ℓ' ∣ n := by
    rw [Nat.Prime.dvd_mul hℓ', Nat.prime_dvd_prime_iff_eq hℓ' hℓ]
    exact or_iff_right hne
  rw [qExpansion_heckeU_coeff ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f) n,
      qExpansion_hecke_coeff ℓ' hℓ' hℓ'N f (ℓ * n),
      qExpansion_hecke_coeff ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f) n,
      qExpansion_heckeU_coeff ℓ hℓ hℓN f (ℓ' * n),
      qExpansion_heckeU_coeff ℓ hℓ hℓN f (n / ℓ'),
      mul_left_comm ℓ' ℓ n]
  by_cases hn : ℓ' ∣ n
  · rw [if_pos hn, if_pos (h1.mpr hn), Nat.mul_div_assoc ℓ hn]
  · rw [if_neg hn, if_neg fun h => hn (h1.mp h)]

theorem qExpansion_heckeU_hecke_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    qExpansion 1 (CuspForm.heckeU ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f))
      = qExpansion 1 (CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f)) := by
  ext n
  exact qExpansion_heckeU_hecke_comm_coeff ℓ ℓ' hℓ hℓ' hℓN hℓ'N f n

theorem heckeU_hecke_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (CuspForm.hecke ℓ' hℓ' hℓ'N f)
      = CuspForm.hecke ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f) :=
  eq_of_qExpansion_eq (qExpansion_heckeU_hecke_comm ℓ ℓ' hℓ hℓ' hℓN hℓ'N f)

theorem commute_heckeUHom_heckeHom (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) :
    Commute (heckeUHom (N := N) (k := k) ℓ hℓ hℓN) (heckeHom ℓ' hℓ' hℓ'N) := by
  refine LinearMap.ext fun f => ?_
  simpa only [Module.End.mul_apply, heckeUHom_apply, heckeHom_apply] using
    heckeU_hecke_comm ℓ ℓ' hℓ hℓ' hℓN hℓ'N f

theorem qExpansion_heckeU_comm_coeff (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.heckeU ℓ hℓ hℓN (CuspForm.heckeU ℓ' hℓ' hℓ'N f))).coeff n
      = (qExpansion 1 (CuspForm.heckeU ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f))).coeff n := by
  rw [qExpansion_heckeU_coeff ℓ hℓ hℓN (CuspForm.heckeU ℓ' hℓ' hℓ'N f) n,
      qExpansion_heckeU_coeff ℓ' hℓ' hℓ'N f (ℓ * n),
      qExpansion_heckeU_coeff ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f) n,
      qExpansion_heckeU_coeff ℓ hℓ hℓN f (ℓ' * n),
      mul_left_comm ℓ' ℓ n]

theorem qExpansion_heckeU_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    qExpansion 1 (CuspForm.heckeU ℓ hℓ hℓN (CuspForm.heckeU ℓ' hℓ' hℓ'N f))
      = qExpansion 1 (CuspForm.heckeU ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f)) := by
  ext n
  exact qExpansion_heckeU_comm_coeff ℓ ℓ' hℓ hℓ' hℓN hℓ'N f n

theorem heckeU_comm (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ℓ' ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (CuspForm.heckeU ℓ' hℓ' hℓ'N f)
      = CuspForm.heckeU ℓ' hℓ' hℓ'N (CuspForm.heckeU ℓ hℓ hℓN f) :=
  eq_of_qExpansion_eq (qExpansion_heckeU_comm ℓ ℓ' hℓ hℓ' hℓN hℓ'N f)

theorem commute_heckeUHom (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ℓ ∣ N) (hℓ'N : ℓ' ∣ N) :
    Commute (heckeUHom (N := N) (k := k) ℓ hℓ hℓN) (heckeUHom ℓ' hℓ' hℓ'N) := by
  refine LinearMap.ext fun f => ?_
  simpa only [Module.End.mul_apply, heckeUHom_apply] using
    heckeU_comm ℓ ℓ' hℓ hℓ' hℓN hℓ'N f

section HeckeAlgebraFullDef

variable (N : ℕ) [NeZero N] (k : ℤ)

def heckeUSet : Set (Module.End ℂ (CuspForm (Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N), T = heckeUHom ℓ hℓ hℓN}

def heckeAlgebraFull : Subalgebra ℂ (Module.End ℂ (CuspForm (Gamma0 N) k)) :=
  Algebra.adjoin ℂ (heckeSet N k ∪ heckeUSet N k)

end HeckeAlgebraFullDef
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section HeckeAlgebraFullBasic

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma heckeUHom_mem_heckeUSet (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    (heckeUHom ℓ hℓ hℓN : Module.End ℂ (CuspForm (Gamma0 N) k)) ∈ heckeUSet N k :=
  ⟨ℓ, hℓ, hℓN, rfl⟩

lemma heckeSetFull_mul_comm :
    ∀ a ∈ heckeSet N k ∪ heckeUSet N k, ∀ b ∈ heckeSet N k ∪ heckeUSet N k, a * b = b * a := by
  rintro a (⟨ℓ, hℓ, hℓN, rfl⟩ | ⟨ℓ, hℓ, hℓN, rfl⟩) b
    (⟨ℓ', hℓ', hℓ'N, rfl⟩ | ⟨ℓ', hℓ', hℓ'N, rfl⟩)
  ·
    exact heckeSet_mul_comm _ (heckeHom_mem_heckeSet ℓ hℓ hℓN) _
      (heckeHom_mem_heckeSet ℓ' hℓ' hℓ'N)
  ·
    exact ((commute_heckeUHom_heckeHom ℓ' ℓ hℓ' hℓ hℓ'N hℓN).symm).eq
  ·
    exact (commute_heckeUHom_heckeHom ℓ ℓ' hℓ hℓ' hℓN hℓ'N).eq
  ·
    exact (commute_heckeUHom ℓ ℓ' hℓ hℓ' hℓN hℓ'N).eq

lemma commute_of_mem_heckeAlgebraFull {T S : Module.End ℂ (CuspForm (Gamma0 N) k)}
    (hT : T ∈ heckeAlgebraFull N k) (hS : S ∈ heckeAlgebraFull N k) : Commute T S := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hS fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT fun c hc =>
    (heckeSetFull_mul_comm b hb c hc)).symm

scoped instance : CommRing (heckeAlgebraFull N k) :=
  { (inferInstance : Ring (heckeAlgebraFull N k)) with
    mul_comm := fun T S => Subtype.ext ((commute_of_mem_heckeAlgebraFull T.2 S.2).eq) }

end HeckeAlgebraFullBasic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

set_option autoImplicit false

open CongruenceSubgroup

noncomputable section

namespace CuspForm

section Carrier

variable (N : ℕ) [NeZero N]

def heckeAlgebraIntFull : Subalgebra ℤ (Module.End ℂ (CuspForm (Gamma0 N) 2)) :=
  Algebra.adjoin ℤ (heckeSet N 2 ∪ heckeUSet N 2)

end Carrier
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section CarrierBasic

variable {N : ℕ} [NeZero N]

lemma heckeHom_mem_heckeAlgebraIntFull (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (heckeHom ℓ hℓ hℓN : Module.End ℂ (CuspForm (Gamma0 N) 2)) ∈ heckeAlgebraIntFull N :=
  Algebra.subset_adjoin (Set.mem_union_left _ (heckeHom_mem_heckeSet ℓ hℓ hℓN))

lemma heckeUHom_mem_heckeAlgebraIntFull (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    (heckeUHom ℓ hℓ hℓN : Module.End ℂ (CuspForm (Gamma0 N) 2)) ∈ heckeAlgebraIntFull N :=
  Algebra.subset_adjoin (Set.mem_union_right _ (heckeUHom_mem_heckeUSet ℓ hℓ hℓN))

end CarrierBasic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

section LatticeStability

variable {N : ℕ} [NeZero N]

scoped instance : Module.IsTorsionFree ℤ (Module.End ℂ (CuspForm (Gamma0 N) 2)) where
  isSMulRegular r hr x y hxy := by
    have hr0 : (r : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (by simpa [isRegular_iff_ne_zero] using hr)
    have hsub : (r : ℂ) • (x - y) = 0 := by
      rw [smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      simpa [sub_eq_zero] using hxy
    rcases smul_eq_zero.mp hsub with hc | hxy'
    · exact absurd hc hr0
    · exact sub_eq_zero.mp hxy'

end LatticeStability
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace FLT
namespace HeckeSaturation

p2m_open "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm ModularForm.CuspForm"

variable (N : ℕ) [NeZero N]

end FLT.HeckeSaturation
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

namespace CuspForm

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

section

namespace ModularCurve

open Subgroup

section AddChars

variable (R : Type*) [Ring R] (G : Type*) [Group G]
variable (M : Type*) [AddCommGroup M] [Module R M]

def addChars : Submodule R (G → M) where
  carrier := {φ | ∀ γ δ : G, φ (γ * δ) = φ γ + φ δ}
  zero_mem' := fun _ _ => (add_zero (0 : M)).symm
  add_mem' := by
    intro φ ψ hφ hψ γ δ
    simp only [Pi.add_apply, hφ γ δ, hψ γ δ]
    abel
  smul_mem' := by
    intro c φ hφ γ δ
    simp only [Pi.smul_apply, hφ γ δ, smul_add]

variable {R G M}

theorem mem_addChars_iff {φ : G → M} :
    φ ∈ addChars R G M ↔ ∀ γ δ : G, φ (γ * δ) = φ γ + φ δ :=
  Iff.rfl

namespace addChars

theorem apply_mul (φ : addChars R G M) (γ δ : G) : φ.1 (γ * δ) = φ.1 γ + φ.1 δ :=
  φ.2 γ δ

theorem apply_one (φ : addChars R G M) : φ.1 1 = 0 := by
  have h := φ.2 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem apply_inv (φ : addChars R G M) (γ : G) : φ.1 γ⁻¹ = -φ.1 γ := by
  have h := φ.2 γ⁻¹ γ
  rw [inv_mul_cancel, apply_one φ] at h
  exact eq_neg_of_add_eq_zero_left h.symm
theorem apply_conj (φ : addChars R G M) (δ γ : G) : φ.1 (δ⁻¹ * γ * δ) = φ.1 γ := by
  rw [apply_mul φ (δ⁻¹ * γ) δ, apply_mul φ δ⁻¹ γ, apply_inv φ δ]
  abel

variable (R M) in

def evalOn (S : Set G) : addChars R G M →ₗ[R] (S → M) where
  toFun φ s := φ.1 s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalOn_injective {S : Set G} (hS : Subgroup.closure S = ⊤) :
    Function.Injective (evalOn R M S) := by
  intro φ ψ h
  ext γ
  have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction with
  | mem s hs => exact congrFun h ⟨s, hs⟩
  | one => rw [apply_one φ, apply_one ψ]
  | mul a b _ _ iha ihb => rw [apply_mul φ a b, apply_mul ψ a b, iha, ihb]
  | inv a _ iha => rw [apply_inv φ a, apply_inv ψ a, iha]

variable (R G M) in

theorem isNoetherian [Group.FG G] [IsNoetherian R M] : IsNoetherian R (addChars R G M) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  haveI : Finite S := hSfin.to_subtype
  exact isNoetherian_of_injective (evalOn R M S) (evalOn_injective hS)

variable (R G M) in

scoped instance instModuleFinite [Group.FG G] [IsNoetherian R M] : Module.Finite R (addChars R G M) :=
  haveI := isNoetherian R G M
  inferInstance

end addChars
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars"

end AddChars
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars"

section SL2Z

open scoped MatrixGroups

open ModularGroup CongruenceSubgroup

scoped instance instGroupFGSL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr
    ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance instGroupFGGamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) :=
  Subgroup.fg_of_index_ne_zero _

end SL2Z
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars"

section Gamma0

open scoped MatrixGroups

open CongruenceSubgroup

variable (N : ℕ) [NeZero N]
end Gamma0
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars"
section Parabolic
open scoped MatrixGroups
variable (R : Type*) [Ring R] (Γ : Subgroup SL(2, ℤ))
variable (M : Type*) [AddCommGroup M] [Module R M]

def parabolicChars : Submodule R (addChars R Γ M) where
  carrier := {φ | ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    φ.1 γ = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ.1 γ + ψ.1 γ = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ.1 γ = 0
    rw [hφ γ hγ, smul_zero]

variable {R Γ M}

theorem parabolicChars.finite [Group.FG Γ] [IsNoetherian R M] :
    Module.Finite R (parabolicChars R Γ M) :=
  haveI := addChars.isNoetherian R Γ M
  inferInstance

end Parabolic
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars"

end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section

namespace ModularCurve

namespace addChars

open Subgroup

section Conj

variable {R : Type*} [Ring R] {G : Type*} [Group G]
variable (Γ : Subgroup G) [hΓ : Γ.Normal]
variable {M : Type*} [AddCommGroup M] [Module R M]
end Conj
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section Transfer
variable {R : Type*} [Ring R] {G : Type*} [Group G]
variable (H : Subgroup G)
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def transferAux (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

@[scoped simp]
theorem coe_transferAux (g : G) (q : G ⧸ H) :
    (transferAux H g q : G) = (g • q).out⁻¹ * (g * q.out) :=
  rfl

theorem transferAux_mul (g₁ g₂ : G) (q : G ⧸ H) :
    transferAux H (g₁ * g₂) q = transferAux H g₁ (g₂ • q) * transferAux H g₂ q := by
  ext
  push_cast [coe_transferAux]
  rw [mul_smul]
  group

variable [H.FiniteIndex]

noncomputable def cores : addChars R H M →ₗ[R] addChars R G M where
  toFun φ :=
    letI := H.fintypeQuotientOfFiniteIndex
    ⟨fun g => ∑ q : G ⧸ H, φ.1 (transferAux H g q), fun g₁ g₂ => by
      show ∑ q : G ⧸ H, φ.1 (transferAux H (g₁ * g₂) q) =
        (∑ q : G ⧸ H, φ.1 (transferAux H g₁ q)) + ∑ q : G ⧸ H, φ.1 (transferAux H g₂ q)
      simp_rw [transferAux_mul, apply_mul]
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·)
        (Fintype.sum_bijective (g₂ • ·) (MulAction.bijective g₂)
          (fun q => φ.1 (transferAux H g₁ (g₂ • q))) (fun q => φ.1 (transferAux H g₁ q))
          fun q => rfl) rfl⟩
  map_add' φ ψ := by
    letI := H.fintypeQuotientOfFiniteIndex
    refine Subtype.ext (funext fun g => ?_)
    show ∑ q : G ⧸ H, (φ.1 (transferAux H g q) + ψ.1 (transferAux H g q)) =
      (∑ q : G ⧸ H, φ.1 (transferAux H g q)) + ∑ q : G ⧸ H, ψ.1 (transferAux H g q)
    exact Finset.sum_add_distrib
  map_smul' c φ := by
    letI := H.fintypeQuotientOfFiniteIndex
    refine Subtype.ext (funext fun g => ?_)
    show ∑ q : G ⧸ H, c • φ.1 (transferAux H g q) = c • ∑ q : G ⧸ H, φ.1 (transferAux H g q)
    exact Finset.smul_sum.symm
end Transfer
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end addChars
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section LevelStructure
open CongruenceSubgroup Subgroup
open scoped MatrixGroups
variable (N : ℕ)
end LevelStructure
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section

namespace ModularCurve

open Subgroup Matrix CongruenceSubgroup

open scoped MatrixGroups

namespace addChars

section CompHom

variable {R : Type*} [Ring R] {G : Type*} [Group G] {K : Type*} [Group K]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in

def compHom (f : G →* K) : addChars R K M →ₗ[R] addChars R G M where
  toFun φ := ⟨fun g => φ.1 (f g), fun g₁ g₂ => by
    show φ.1 (f (g₁ * g₂)) = φ.1 (f g₁) + φ.1 (f g₂)
    rw [map_mul]
    exact φ.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end CompHom
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end addChars
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section ConjMatrix

def alphaMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (ℓ : ℤ)]

@[scoped simp] theorem alphaMat_apply_zero_zero (ℓ : ℕ) : alphaMat ℓ 0 0 = 1 := rfl
@[scoped simp] theorem alphaMat_apply_zero_one (ℓ : ℕ) : alphaMat ℓ 0 1 = 0 := rfl
@[scoped simp] theorem alphaMat_apply_one_zero (ℓ : ℕ) : alphaMat ℓ 1 0 = 0 := rfl
@[scoped simp] theorem alphaMat_apply_one_one (ℓ : ℕ) : alphaMat ℓ 1 1 = (ℓ : ℤ) := rfl

theorem det_alphaMat (ℓ : ℕ) : (alphaMat ℓ).det = (ℓ : ℤ) := by
  rw [alphaMat, det_fin_two_of]; ring

theorem eq_of_mul_alphaMat_eq {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A * alphaMat ℓ = B * alphaMat ℓ) : A = B := by
  ext i j
  have h0 := congrFun (congrFun h i) 0
  have h1 := congrFun (congrFun h i) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    mul_one, mul_zero, add_zero, zero_add] at h0 h1
  fin_cases j
  · exact h0
  · exact mul_right_cancel₀ hℓ h1

def heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 / (ℓ : ℤ); g 1 0 * (ℓ : ℤ), g 1 1]

@[scoped simp] theorem heckeConjMat_apply_zero_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 0 = g 0 0 := rfl
@[scoped simp] theorem heckeConjMat_apply_zero_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 1 = g 0 1 / (ℓ : ℤ) := rfl
@[scoped simp] theorem heckeConjMat_apply_one_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 0 = g 1 0 * (ℓ : ℤ) := rfl
@[scoped simp] theorem heckeConjMat_apply_one_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 1 = g 1 1 := rfl

theorem heckeConjMat_mul_alphaMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) :
    heckeConjMat ℓ g * alphaMat ℓ = alphaMat ℓ * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
      alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
      heckeConjMat_apply_zero_zero, heckeConjMat_apply_zero_one, heckeConjMat_apply_one_zero,
      heckeConjMat_apply_one_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_one, mul_zero,
      one_mul, zero_mul, add_zero, zero_add] <;>
    first
      | exact Int.ediv_mul_cancel hg
      | ring1

theorem dvd_mul_apply_zero_one {ℓ : ℕ} {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) : (ℓ : ℤ) ∣ (g * h) 0 1 := by
  rw [(Matrix.two_mul_expl g h).2.1]
  exact dvd_add (hh.mul_left _) (hg.mul_right _)

theorem heckeConjMat_mul {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) :
    heckeConjMat ℓ (g * h) = heckeConjMat ℓ g * heckeConjMat ℓ h := by
  have key : (heckeConjMat ℓ g * heckeConjMat ℓ h) * alphaMat ℓ = alphaMat ℓ * (g * h) := by
    rw [mul_assoc, heckeConjMat_mul_alphaMat hh, ← mul_assoc, heckeConjMat_mul_alphaMat hg,
      mul_assoc]
  exact eq_of_mul_alphaMat_eq hℓ
    ((heckeConjMat_mul_alphaMat (dvd_mul_apply_zero_one hg hh)).trans key.symm)

theorem det_heckeConjMat {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) : (heckeConjMat ℓ g).det = g.det := by
  have h := congrArg Matrix.det (heckeConjMat_mul_alphaMat hg)
  rw [Matrix.det_mul, Matrix.det_mul, det_alphaMat] at h
  exact mul_right_cancel₀ hℓ (by linear_combination h)

theorem heckeConjMat_one (ℓ : ℕ) : heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeConjMat]
end ConjMatrix
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section HeckeSubgroup

def heckeUpperSL (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {g | (ℓ : ℤ) ∣ g 0 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [Set.mem_setOf_eq, SpecialLinearGroup.coe_mul] at *
    rw [show ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (a : Matrix (Fin 2) (Fin 2) ℤ) * b from rfl, h]
    exact dvd_add (hb.mul_left _) (ha.mul_right _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simpa using ha
variable (N ℓ : ℕ)

def heckeUpper : Subgroup (Gamma0 N) := (heckeUpperSL ℓ).subgroupOf (Gamma0 N)

theorem mem_heckeUpper {γ : Gamma0 N} :
    γ ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
  Iff.rfl

def gammaZeroRed : Gamma0 N →* SL(2, ZMod ℓ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod ℓ))).comp
    (Gamma0 N).subtype

theorem ker_gammaZeroRed_le_heckeUpper : (gammaZeroRed N ℓ).ker ≤ heckeUpper N ℓ := by
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  rw [mem_heckeUpper]
  have h01 : ((((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) = 0 := by
    have h := congrArg (fun A : SL(2, ZMod ℓ) => A 0 1) hγ
    simpa [gammaZeroRed, Matrix.one_apply] using h
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h01

scoped instance instFiniteIndexHeckeUpper [NeZero ℓ] : (heckeUpper N ℓ).FiniteIndex :=
  haveI : (gammaZeroRed N ℓ).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  Subgroup.finiteIndex_of_le (ker_gammaZeroRed_le_heckeUpper N ℓ)
variable [NeZero ℓ]

def heckeConjSL (γ : heckeUpper N ℓ) : SL(2, ℤ) :=
  ⟨heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)), by
    rw [det_heckeConjMat (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)]
    exact ((γ : Gamma0 N) : SL(2, ℤ)).2⟩

theorem heckeConjSL_mem_Gamma0 (γ : heckeUpper N ℓ) : heckeConjSL N ℓ γ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show (((heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ))) 1 0 : ℤ) : ZMod N) = 0
  rw [heckeConjMat_apply_one_zero, Int.cast_mul]
  have hc : ((((γ : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp (γ : Gamma0 N).2
  rw [hc, zero_mul]

def heckeConj : heckeUpper N ℓ →* Gamma0 N where
  toFun γ := ⟨heckeConjSL N ℓ γ, heckeConjSL_mem_Gamma0 N ℓ γ⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = (1 : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_one ℓ
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ
        ((((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      heckeConjMat ℓ (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        heckeConjMat ℓ (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_mul (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
      ((mem_heckeUpper N ℓ).mp γ.2) ((mem_heckeUpper N ℓ).mp δ.2)
end HeckeSubgroup
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section HeckeOperator
variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
variable (N ℓ : ℕ) [NeZero ℓ]
variable (R M) in

noncomputable def heckeOperator : addChars R (Gamma0 N) M →ₗ[R] addChars R (Gamma0 N) M :=
  (addChars.cores (heckeUpper N ℓ)).comp (addChars.compHom R M (heckeConj N ℓ))

theorem heckeOperator_apply (φ : addChars R (Gamma0 N) M) (g : Gamma0 N) :
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    (heckeOperator R M N ℓ φ).1 g =
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        φ.1 (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) g q)) :=
  rfl
end HeckeOperator
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section HeckeModule
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (N : ℕ)
end HeckeModule
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section

set_option autoImplicit false

namespace ModularCurve
namespace Period

open UpperHalfPlane Filter Topology
open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)

def IsEquivariantPrimitive : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c

variable {Γ F}

namespace IsEquivariantPrimitive

noncomputable def period (_hF : IsEquivariantPrimitive Γ F) (γ : Γ) : ℂ :=
  F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I

theorem sub_eq_period (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [hc z, period, hc UpperHalfPlane.I]

theorem period_mul (hF : IsEquivariantPrimitive Γ F) (γ δ : Γ) :
    hF.period (γ * δ) = hF.period γ + hF.period δ := by
  have h1 := hF.sub_eq_period (γ * δ) UpperHalfPlane.I
  have h2 := hF.sub_eq_period γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := hF.sub_eq_period δ UpperHalfPlane.I
  have hsmul : ((γ * δ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I
      = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul]; rfl
  rw [hsmul] at h1
  linear_combination h2 + h3 - h1

noncomputable def periodChar (hF : IsEquivariantPrimitive Γ F) : addChars ℂ Γ ℂ :=
  ⟨hF.period, mem_addChars_iff.mpr hF.period_mul⟩
theorem periodChar_apply (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    (hF.periodChar : Γ → ℂ) γ = hF.period γ :=
  rfl

theorem period_congr {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (c : ℂ) (h : ∀ z, F z - F' z = c) (γ : Γ) :
    hF.period γ = hF'.period γ := by
  rw [← hF.sub_eq_period γ UpperHalfPlane.I, ← hF'.sub_eq_period γ UpperHalfPlane.I]
  have h1 := h ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := h UpperHalfPlane.I
  linear_combination h1 - h2

theorem add {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') : IsEquivariantPrimitive Γ (F + F') := by
  intro γ
  refine ⟨hF.period γ + hF'.period γ, fun z => ?_⟩
  have h1 := hF.sub_eq_period γ z
  have h2 := hF'.sub_eq_period γ z
  simp only [Pi.add_apply]
  linear_combination h1 + h2

theorem period_add {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (γ : Γ) :
    (hF.add hF').period γ = hF.period γ + hF'.period γ := by
  rw [← (hF.add hF').sub_eq_period γ UpperHalfPlane.I]
  have h1 := hF.sub_eq_period γ UpperHalfPlane.I
  have h2 := hF'.sub_eq_period γ UpperHalfPlane.I
  simp only [Pi.add_apply]
  linear_combination h1 + h2

theorem smul (a : ℂ) (hF : IsEquivariantPrimitive Γ F) :
    IsEquivariantPrimitive Γ (a • F) := by
  intro γ
  refine ⟨a * hF.period γ, fun z => ?_⟩
  have h := hF.sub_eq_period γ z
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination a * h

theorem period_smul (a : ℂ) (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    (hF.smul a).period γ = a * hF.period γ := by
  rw [← (hF.smul a).sub_eq_period γ UpperHalfPlane.I]
  have h := hF.sub_eq_period γ UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination a * h

end IsEquivariantPrimitive
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section

set_option autoImplicit false

namespace ModularCurve
namespace Period

p2m_open "UpperHalfPlane Filter Topology Complex Function.Complex Function P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm Metric"
open scoped MatrixGroups Real CongruenceSubgroup ModularForm Manifold

local notation "𝕢" => Function.Periodic.qParam

theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (2 * π * Complex.I / h * 𝕢 h z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * ↑π * Complex.I * w / ↑h)
      (2 * ↑π * Complex.I / ↑h) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * ↑π * Complex.I)).div_const (↑h : ℂ)
  have h2 := h1.cexp
  have hval : 2 * (π:ℂ) * Complex.I / ↑h * 𝕢 h z
      = cexp (2 * ↑π * Complex.I * z / ↑h) * (2 * ↑π * Complex.I / ↑h) := by
    simp only [Function.Periodic.qParam]
    ring
  rw [hval]
  exact h2

section Primitive

variable {h : ℝ} {g : ℍ → ℂ}

theorem exists_primitive (hh : 0 < h) (hper : Periodic (g ∘ ofComplex) h)
    (hhol : MDiff g) (hzero : IsZeroAtImInfty g) :
    ∃ G : ℍ → ℂ, (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := by
  have hbdd : IsBoundedAtImInfty g := hzero.boundedAtFilter

  set Φ : ℂ → ℂ := cuspFunction h g with hΦ
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    differentiableOn_cuspFunction_ball hh hper hhol hbdd
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ, cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hper hhol hbdd) hper]
    exact hzero.valueAtInfty_eq_zero

  set Φ₁ : ℂ → ℂ := dslope Φ 0 with hΦ₁
  have hΦ₁diff : DifferentiableOn ℂ Φ₁ (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hΦdiff
  have hΦ₁mul : ∀ q : ℂ, q * Φ₁ q = Φ q := fun q => by
    have := sub_smul_dslope Φ 0 q
    simpa [hΦ0, smul_eq_mul] using this

  obtain ⟨Ψ, hΨ0, hΨ⟩ := (hΦ₁diff.isExactOn_ball).with_val_at 0 0

  have hqball : ∀ τ : ℍ, 𝕢 h ↑τ ∈ ball (0:ℂ) 1 := by
    intro τ
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑τ := τ.2
    calc Real.exp (-2 * π * Complex.im ↑τ / h) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hh
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero

  refine ⟨fun τ : ℍ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h ↑τ), fun τ => ?_, ?_⟩
  ·
    have hchain : HasDerivAt (fun z : ℂ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h z)) (g τ) ↑τ := by
      have h1 : HasDerivAt (fun z : ℂ => Ψ (𝕢 h z))
          (Φ₁ (𝕢 h ↑τ) * (2 * π * Complex.I / h * 𝕢 h ↑τ)) ↑τ :=
        (hΨ _ (hqball τ)).comp (↑τ : ℂ) (hasDerivAt_qParam h ↑τ)
      have h2 := h1.const_mul (↑h / (2 * π * Complex.I))
      refine h2.congr_deriv ?_
      have hne : (↑h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
      have h3 : ↑h / (2 * ↑π * Complex.I) * (Φ₁ (𝕢 h ↑τ) * (2 * ↑π * Complex.I / ↑h * 𝕢 h ↑τ))
          = 𝕢 h ↑τ * Φ₁ (𝕢 h ↑τ) := by
        field_simp
      rw [h3, hΦ₁mul]
      exact eq_cuspFunction τ hh.ne' hper

    refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  ·
    have hΨcont : ContinuousAt Ψ 0 :=
      (hΨ 0 (mem_ball_self one_pos)).differentiableAt.continuousAt
    have hq0 : Tendsto (fun τ : ℍ => 𝕢 h ↑τ) atImInfty (𝓝 0) :=
      qParam_tendsto_atImInfty hh
    have : Tendsto (fun τ : ℍ => Ψ (𝕢 h ↑τ)) atImInfty (𝓝 (Ψ 0)) :=
      (hΨcont.tendsto).comp hq0
    rw [hΨ0] at this
    simpa using this.const_mul (↑h / (2 * π * Complex.I))

end Primitive
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section Constancy

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z) (fun σ => ((hF σ).fun_sub (hG σ)).congr_deriv (sub_self _)) τ UpperHalfPlane.I

end Constancy
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section ChainRule

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  refine h1.congr_deriv ?_
  rw [hdet]
  push_cast
  rw [_root_.zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by

  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]

  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  refine hcomp.congr_deriv ?_
  exact (SL_slash_apply (g : ℍ → ℂ) γ τ).symm

end ChainRule
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section Assembly

open CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped Pointwise in

theorem natCast_mem_strictPeriods_conj {Γ : Subgroup SL(2, ℤ)} {N : ℕ}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    (N : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul]

  have hT1 : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T
      = Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hTN : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))
      = Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
    rw [zpow_natCast, map_pow, hT1, ← AddChar.map_nsmul_eq_pow]
    norm_num
  rw [← hTN, ← map_mul, ← map_inv, ← map_mul]
  refine Subgroup.mem_map_of_mem _ (hΓ ?_)
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact (Gamma_normal N).conj_mem _ hTmem δ

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

theorem periodic_slash_comp_ofComplex {N : ℕ}
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) (N : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ))
    (natCast_mem_strictPeriods_conj hΓ δ)

theorem SL_slash_eq_self_of_mem [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) : (f : ℍ → ℂ) ∣[k] γ = f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

variable {N : ℕ} [NeZero N] [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) 2]

theorem exists_equivariantPrimitive (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    ∃ Fprim : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) ∧
      Tendsto Fprim atImInfty (𝓝 0) ∧
      IsEquivariantPrimitive Γ Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hN : (0:ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  have hmaster : ∀ δ : SL(2, ℤ), ∃ G : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := fun δ =>
    exists_primitive hN (periodic_slash_comp_ofComplex f hΓ δ)
      ((CuspFormClass.holo f).slash 2 _) (CuspFormClass.zero_at_infty_slash f δ)

  obtain ⟨Fprim, hFprim, hFprim0⟩ := hmaster 1
  have hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ := by
    intro τ
    simpa using hFprim τ
  refine ⟨Fprim, hFf, hFprim0, ?_, ?_⟩
  ·
    intro γ

    have hslash : ((f : ℍ → ℂ) ∣[(2:ℤ)] (γ : SL(2, ℤ))) = f := SL_slash_eq_self_of_mem f γ.2
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim ((γ : SL(2, ℤ)) • ofComplex z))
        (f τ) ↑τ := by
      intro τ
      have := hasDerivAt_comp_smul hFf (γ : SL(2, ℤ)) τ
      rwa [hslash] at this
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hFf
    exact ⟨c, fun z => by simpa using hc z⟩
  ·

    intro δ
    obtain ⟨Gδ, hGδ, hGδ0⟩ := hmaster δ
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim (δ • ofComplex z))
        (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ := fun τ => hasDerivAt_comp_smul hFf δ τ
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hGδ
    refine ⟨c, ?_⟩
    have h1 : (fun w : ℍ => Fprim (δ • w)) = fun w : ℍ => (Gδ ∘ ofComplex) ↑w + c := by
      funext w
      have := hc w
      simp only [ofComplex_apply] at this ⊢
      linear_combination this
    rw [h1]
    have : Tendsto (fun w : ℍ => (Gδ ∘ ofComplex) ↑w) atImInfty (𝓝 0) := by
      simpa [Function.comp_def, ofComplex_apply] using hGδ0
    simpa using this.add_const c
end Assembly
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
section Gamma0
open CongruenceSubgroup

theorem Gamma_le_Gamma0 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma0 N := fun _ hA =>
  Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

variable {N : ℕ} [NeZero N] (f : CuspForm (Gamma0 N) 2)

theorem CuspForm.exists_equivariantPrimitive_gamma0 :
    ∃ Fprim : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) ∧
      Tendsto Fprim atImInfty (𝓝 0) ∧
      IsEquivariantPrimitive (Gamma0 N) Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L) :=
  exists_equivariantPrimitive f (Gamma_le_Gamma0 N)
end Gamma0
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section

set_option autoImplicit false

namespace ModularCurve
namespace Period

p2m_open "UpperHalfPlane Filter Topology Complex Function.Complex Function P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm Matrix CongruenceSubgroup Subgroup"

open scoped MatrixGroups ModularForm

section ChainRule

theorem slash_two_apply_of_det_pos (f : ℍ → ℂ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.val.det)
    (τ : ℍ) :
    (f ∣[(2 : ℤ)] β) τ = f (β • τ) * (↑β.val.det / denom β ↑τ ^ 2) := by
  have hβ' : 0 < β.det.val := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [ModularForm.slash_apply, σ, if_pos hβ', ContinuousAlgEquiv.refl_apply]
  have habs : |β.det.val| = β.val.det := by
    rw [abs_of_pos hβ', Matrix.GeneralLinearGroup.val_det_apply]
  rw [habs, show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, _root_.zpow_neg, zpow_ofNat, mul_assoc,
    ← div_eq_mul_inv]

theorem hasDerivAt_comp_smul_of_det_pos {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) {β : GL (Fin 2) ℝ}
    (hβ : 0 < β.val.det) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (β • ofComplex z)) ((g ∣[(2 : ℤ)] β) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (β • ofComplex z))
      = (G ∘ ofComplex) ∘ fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (β • τ))
      ((fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (β • τ)
  have hinner : HasDerivAt (fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ))
      (↑β.val.det / denom β ↑τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hβ τ).hasDerivAt
  have hcomp := houter.comp (↑τ : ℂ) hinner
  rw [← hfun] at hcomp
  rw [slash_two_apply_of_det_pos g hβ τ]
  exact hcomp

end ChainRule
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

noncomputable local instance (N ℓ : ℕ) [NeZero ℓ] :
    Fintype (Gamma0 N ⧸ heckeUpper N ℓ) :=
  (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex

section CosetRep

variable (N ℓ : ℕ) [NeZero ℓ]

private theorem map_int_mul'_FPHE (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

noncomputable def alphaGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((alphaMat ℓ).map (algebraMap ℤ ℝ)) (by
    have h : ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (alphaMat ℓ).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_alphaMat]
    simp [NeZero.ne ℓ])
theorem alphaGL_val_det : (alphaGL ℓ).val.det = (ℓ : ℝ) := by
  show ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (ℓ : ℝ)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_alphaMat]
  simp

noncomputable def gammaToGL : Gamma0 N →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 N).subtype

@[scoped simp]
theorem gammaToGL_apply (x : Gamma0 N) :
    gammaToGL N x = Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) :=
  rfl

theorem gammaToGL_val_det (x : Gamma0 N) : (gammaToGL N x).val.det = 1 := by
  rw [gammaToGL_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

noncomputable def heckeCosetRep (q : Gamma0 N ⧸ heckeUpper N ℓ) : GL (Fin 2) ℝ :=
  alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹

theorem heckeCosetRep_def (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q = alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹ :=
  rfl

theorem heckeCosetRep_val_det (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    (heckeCosetRep N ℓ q).val.det = (ℓ : ℝ) := by
  rw [heckeCosetRep_def, Units.val_mul, Matrix.det_mul, alphaGL_val_det, gammaToGL_val_det,
    mul_one]

theorem heckeCosetRep_val_det_pos (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    0 < (heckeCosetRep N ℓ q).val.det := by
  rw [heckeCosetRep_val_det]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

theorem gammaToGL_heckeConj_mul_alphaGL (h : heckeUpper N ℓ) :
    gammaToGL N (heckeConj N ℓ h) * alphaGL ℓ = alphaGL ℓ * gammaToGL N (h : Gamma0 N) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (heckeConjMat ℓ ((((h : Gamma0 N) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (algebraMap ℤ ℝ) * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
      = ((alphaMat ℓ).map (algebraMap ℤ ℝ))
        * ((((h : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))
  rw [← map_int_mul'_FPHE, ← map_int_mul'_FPHE,
    heckeConjMat_mul_alphaMat ((mem_heckeUpper N ℓ).mp h.2)]

omit [NeZero ℓ] in

theorem coe_transferAux_inv_smul (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    ((addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q) : heckeUpper N ℓ) : Gamma0 N)
      = (Quotient.out q)⁻¹ * (γ * Quotient.out (γ⁻¹ • q)) := by
  rw [addChars.coe_transferAux, smul_inv_smul]

theorem heckeCosetRep_mul_gammaToGL (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q * gammaToGL N γ
      = gammaToGL N (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
        * heckeCosetRep N ℓ (γ⁻¹ • q) := by
  rw [heckeCosetRep_def, heckeCosetRep_def, ← mul_assoc, gammaToGL_heckeConj_mul_alphaGL,
    mul_assoc, mul_assoc, ← map_mul (gammaToGL N), ← map_mul (gammaToGL N)]
  refine congrArg (fun x : Gamma0 N => alphaGL ℓ * gammaToGL N x) ?_
  rw [coe_transferAux_inv_smul]
  group

end CosetRep
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section Telescoping

variable {N ℓ : ℕ} [NeZero ℓ] {Fprim : ℍ → ℂ}

theorem sum_heckeCosetRep_smul_sub (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (γ : Gamma0 N) (z : ℍ) :
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)) := by

  have hterm : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ,
      Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
        = Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
          + hF.period
              (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))) := by
    intro q
    have h1 : heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)
        = ((heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)) : Gamma0 N)
            : SL(2, ℤ)) • (heckeCosetRep N ℓ (γ⁻¹ • q) • z) := by
      rw [show ((γ : SL(2, ℤ)) • z) = gammaToGL N γ • z from rfl, ← mul_smul,
        heckeCosetRep_mul_gammaToGL, mul_smul]
      rfl
    rw [h1]
    have h2 := hF.sub_eq_period
      (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
      (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
    linear_combination h2

  calc
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          (Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
            + hF.period
                (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
            - Fprim (heckeCosetRep N ℓ q • z)) :=
        Finset.sum_congr rfl fun q _ => by rw [hterm q]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period
                (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [(MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => Fprim (heckeCosetRep N ℓ q • z)),
          (MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => hF.period
              (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)))]
    _ = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)) := by
        ring

end Telescoping
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section Main

variable {N ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

noncomputable def heckeQuotSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, f ∣[(2 : ℤ)] heckeCosetRep N ℓ q

theorem hasDerivAt_sum_heckeCosetRep {Fprim : ℍ → ℂ} {f : ℍ → ℂ}
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt
      ((fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w))
        ∘ ofComplex)
      (heckeQuotSlashSum N ℓ f τ) ↑τ := by
  have key := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Gamma0 N ⧸ heckeUpper N ℓ)))
    (x := (↑τ : ℂ))
    (A := fun (q : Gamma0 N ⧸ heckeUpper N ℓ) (z : ℂ) =>
      Fprim (heckeCosetRep N ℓ q • ofComplex z))
    (A' := fun q : Gamma0 N ⧸ heckeUpper N ℓ => (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ)
    (fun q _ => hasDerivAt_comp_smul_of_det_pos hFf (heckeCosetRep_val_det_pos N ℓ q) τ)
  rw [show heckeQuotSlashSum N ℓ f τ
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ from
    Finset.sum_apply τ Finset.univ fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  exact key

theorem periodChar_heckeQuotSlashSum {Fprim Fprim' : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (heckeQuotSlashSum N ℓ f τ) ↑τ) :
    hF'.periodChar = heckeOperator ℂ ℂ N ℓ hF.periodChar := by

  have hGsub : ∀ (γ : Gamma0 N) (z : ℍ),
      (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)))
        - (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ z
    rw [← Finset.sum_sub_distrib]
    exact sum_heckeCosetRep_smul_sub hF γ z

  have hGequiv : IsEquivariantPrimitive (Gamma0 N)
      (fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w)) :=
    fun γ =>
      ⟨∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)),
        fun z => hGsub γ z⟩

  have hGperiod : ∀ γ : Gamma0 N,
      hGequiv.period γ
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (addChars.transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ
    rw [← hGequiv.sub_eq_period γ UpperHalfPlane.I]
    exact hGsub γ UpperHalfPlane.I

  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hF'f (hasDerivAt_sum_heckeCosetRep hFf)
  apply Subtype.ext
  funext γ
  show hF'.period γ = (heckeOperator ℂ ℂ N ℓ hF.periodChar).1 γ
  rw [hF'.period_congr hGequiv c (fun w => by
      simpa only [Function.comp_apply, ofComplex_apply] using hc w) γ, hGperiod γ]
  rfl

end Main
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"

section Bridge

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

def HeckeCosetMatch : Prop :=
  ∃ e : Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ),
    ∀ i : Option (Fin ℓ), ∃ δ : Gamma0 N,
      HeckeAnalytic.repGL ℓ i = gammaToGL N δ * heckeCosetRep N ℓ (e i)

omit [NeZero N] in

theorem heckeSlashSum_eq_heckeQuotSlashSum (hmatch : HeckeCosetMatch N ℓ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    HeckeAnalytic.heckeSlashSum 2 ℓ f = heckeQuotSlashSum N ℓ f := by
  obtain ⟨e, he⟩ := hmatch
  rw [HeckeAnalytic.heckeSlashSum, heckeQuotSlashSum,
    ← Equiv.sum_comp e fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨δ, hδ⟩ := he i
  rw [hδ, SlashAction.slash_mul,
    hf (gammaToGL N δ) (Subgroup.mem_map.mpr ⟨(δ : SL(2, ℤ)), δ.2, rfl⟩)]

theorem periodChar_hecke_of_match (hmatch : HeckeCosetMatch N ℓ) {hℓ : ℓ.Prime}
    {hℓN : ¬ ℓ ∣ N} (f : CuspForm (Gamma0 N) 2) {Fprim Fprim' : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (CuspForm.hecke ℓ hℓ hℓN f τ) ↑τ) :
    hF'.periodChar = heckeOperator ℂ ℂ N ℓ hF.periodChar := by
  refine periodChar_heckeQuotSlashSum hF hFf hF' fun τ => ?_
  have heq : CuspForm.hecke ℓ hℓ hℓN f τ = heckeQuotSlashSum N ℓ (⇑f) τ := by
    show HeckeAnalytic.heckeSlashSum 2 ℓ (⇑f) τ = heckeQuotSlashSum N ℓ (⇑f) τ
    rw [heckeSlashSum_eq_heckeQuotSlashSum hmatch
      (SlashInvariantFormClass.slash_action_eq f)]
  rw [← heq]
  exact hF'f τ

end Bridge
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup HeckeAnalytic UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm

namespace ModularCurve
namespace Period

section Representatives

def unipotentUpper (N : ℕ) (t : ℤ) : Gamma0 N :=
  ⟨⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod N) = 0
    exact Int.cast_zero⟩

theorem unipotentUpper_mul (N : ℕ) (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t = unipotentUpper N (s + t) := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, t; 0, 1] = !![1, s + t; 0, 1]
  rw [Matrix.mul_fin_two]
  refine Matrix.ext fun x y => ?_
  fin_cases x <;> fin_cases y
  · show (1 * 1 + s * 0 : ℤ) = 1
    ring
  · show (1 * t + s * 1 : ℤ) = s + t
    ring
  · show (0 * 1 + 1 * 0 : ℤ) = 0
    ring
  · show (0 * t + 1 * 1 : ℤ) = 1
    ring

theorem unipotentUpper_zero (N : ℕ) : unipotentUpper N 0 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1
  rw [Matrix.one_fin_two]

theorem inv_unipotentUpper (N : ℕ) (t : ℤ) :
    (unipotentUpper N t)⁻¹ = unipotentUpper N (-t) :=
  inv_eq_of_mul_eq_one_right (by
    rw [unipotentUpper_mul, show t + -t = 0 by ring, unipotentUpper_zero])

variable {N ℓ : ℕ}

theorem hecke_bezout (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (ℓ : ℤ) * Nat.gcdA ℓ N + (N : ℤ) * Nat.gcdB ℓ N = 1 := by
  have h := Nat.gcd_eq_gcd_ab ℓ N
  rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)] at h
  exact_mod_cast h.symm

theorem not_dvd_gcdB (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : ¬ (ℓ : ℤ) ∣ Nat.gcdB ℓ N := by
  intro hdvd
  have h1 : (ℓ : ℤ) ∣ 1 := by
    rw [← hecke_bezout hℓ hℓN]
    exact dvd_add (dvd_mul_right _ _) (hdvd.mul_left _)
  have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  have h3 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
  omega

def bezoutRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Gamma0 N :=
  ⟨⟨!![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hecke_bezout hℓ hℓN⟩, by
    rw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    rw [Int.cast_natCast]
    exact ZMod.natCast_self N⟩

def cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none => bezoutRep hℓ hℓN
  | some j => unipotentUpper N (-(j : ℤ))

@[scoped simp]
theorem cosetRep_none (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    cosetRep hℓ hℓN (none : Option (Fin ℓ)) = bezoutRep hℓ hℓN :=
  rfl

@[scoped simp]
theorem cosetRep_some (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (j : Fin ℓ) :
    cosetRep hℓ hℓN (some j) = unipotentUpper N (-(j : ℤ)) :=
  rfl

def rawDelta (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none =>
    ⟨⟨!![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]
      linear_combination hecke_bezout hℓ hℓN⟩, by
      rw [Gamma0_mem]
      show ((N : ℤ) : ZMod N) = 0
      rw [Int.cast_natCast]
      exact ZMod.natCast_self N⟩
  | some _ => 1

theorem repMat_mul_cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repMat ℓ i * (((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * alphaMat ℓ := by
  match i with
  | none =>
    show !![(ℓ : ℤ), 0; 0, 1] * !![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)]
        = !![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show ((ℓ : ℤ) * Nat.gcdA ℓ N + 0 * (N : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 1 + -Nat.gcdB ℓ N * 0
      ring
    · show ((ℓ : ℤ) * -Nat.gcdB ℓ N + 0 * (ℓ : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 0 + -Nat.gcdB ℓ N * (ℓ : ℤ)
      ring
    · show (0 * Nat.gcdA ℓ N + 1 * (N : ℤ) : ℤ) = (N : ℤ) * 1 + 1 * 0
      ring
    · show (0 * -Nat.gcdB ℓ N + 1 * (ℓ : ℤ) : ℤ) = (N : ℤ) * 0 + 1 * (ℓ : ℤ)
      ring
  | some j =>
    show !![1, (j : ℤ); 0, (ℓ : ℤ)] * !![1, -(j : ℤ); 0, 1]
        = (1 : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.one_mul]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * 1 + (j : ℤ) * 0 : ℤ) = 1
      ring
    · show (1 * -(j : ℤ) + (j : ℤ) * 1 : ℤ) = 0
      ring
    · show (0 * 1 + (ℓ : ℤ) * 0 : ℤ) = 0
      ring
    · show (0 * -(j : ℤ) + (ℓ : ℤ) * 1 : ℤ) = (ℓ : ℤ)
      ring

end Representatives
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Bijection

variable {N ℓ : ℕ}

def cosetOfRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    Gamma0 N ⧸ heckeUpper N ℓ :=
  (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ)

theorem cosetOfRep_def (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    cosetOfRep hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

private theorem unipotentUpper_mul_mem_iff_FHCE (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (s + t) := by
  rw [unipotentUpper_mul, mem_heckeUpper]
  exact Iff.rfl

private theorem unipotentUpper_mul_bezoutRep_not_mem_FHCE (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (s : ℤ) :
    unipotentUpper N s * bezoutRep hℓ hℓN ∉ heckeUpper N ℓ := by
  intro hmem
  rw [mem_heckeUpper] at hmem

  have hentry : (((unipotentUpper N s * bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ))) 0 1
      = 1 * -Nat.gcdB ℓ N + s * (ℓ : ℤ) :=
    (Matrix.two_mul_expl
      (((unipotentUpper N s : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (((bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).2.1
  rw [hentry,
    show (1 : ℤ) * -Nat.gcdB ℓ N + s * (ℓ : ℤ) = s * (ℓ : ℤ) - Nat.gcdB ℓ N by ring] at hmem

  exact not_dvd_gcdB hℓ hℓN ((dvd_sub_right (dvd_mul_left _ _)).mp hmem)

theorem cosetOfRep_injective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Injective (cosetOfRep (N := N) hℓ hℓN) := by
  intro i i' h
  rw [cosetOfRep_def, cosetOfRep_def, QuotientGroup.eq] at h
  match i, i' with
  | none, none => rfl
  | some j, none =>

    exact absurd h (by
      rw [cosetRep_some, cosetRep_none, inv_unipotentUpper, neg_neg]
      exact unipotentUpper_mul_bezoutRep_not_mem_FHCE hℓ hℓN (j : ℤ))
  | none, some j' =>

    refine absurd ((heckeUpper N ℓ).inv_mem h) ?_
    rw [cosetRep_some, cosetRep_none, _root_.mul_inv_rev, inv_inv, inv_unipotentUpper, neg_neg]
    exact unipotentUpper_mul_bezoutRep_not_mem_FHCE hℓ hℓN (j' : ℤ)
  | some j, some j' =>

    rw [cosetRep_some, cosetRep_some, inv_unipotentUpper, neg_neg,
      unipotentUpper_mul_mem_iff_FHCE] at h

    have hj := j.isLt
    have hj' := j'.isLt
    have hzero : (j : ℤ) + -(j' : ℤ) = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
      rw [Int.natAbs_natCast]
      omega
    have hval : (j : ℕ) = (j' : ℕ) := by omega
    exact congrArg some (Fin.ext hval)

private theorem dvd_of_alphaMat_mul_eq_mul_alphaMat_FHCE {X Y : Matrix (Fin 2) (Fin 2) ℤ}
    (h : alphaMat ℓ * X = Y * alphaMat ℓ) : (ℓ : ℤ) ∣ X 0 1 := by
  have h01 : (alphaMat ℓ * X) 0 1 = (Y * alphaMat ℓ) 0 1 := by rw [h]
  rw [(Matrix.two_mul_expl (alphaMat ℓ) X).2.1, (Matrix.two_mul_expl Y (alphaMat ℓ)).2.1,
    alphaMat_apply_zero_zero, alphaMat_apply_zero_one, alphaMat_apply_one_one] at h01
  exact ⟨Y 0 1, by linear_combination h01⟩

private theorem repMat_some_zero_FHCE (hpos : 0 < ℓ) : repMat ℓ (some ⟨0, hpos⟩) = alphaMat ℓ := by
  rw [repMat_some]
  rfl

theorem cosetOfRep_surjective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Surjective (cosetOfRep (N := N) hℓ hℓN) := by
  intro q
  obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 N, (γ : Gamma0 N ⧸ heckeUpper N ℓ) = q :=
    ⟨Quotient.out q, QuotientGroup.out_eq' q⟩

  obtain ⟨δ, -, m, hm⟩ := exists_cocycle hℓ hℓN (γ⁻¹ : Gamma0 N).2 (some ⟨0, hℓ.pos⟩)
  refine ⟨m, ?_⟩
  rw [cosetOfRep_def, QuotientGroup.eq, ← (heckeUpper N ℓ).inv_mem_iff, _root_.mul_inv_rev,
    inv_inv, mem_heckeUpper]

  refine dvd_of_alphaMat_mul_eq_mul_alphaMat_FHCE
    (Y := (δ : Matrix (Fin 2) (Fin 2) ℤ)
      * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ?_
  have hcoe : (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    rfl
  calc alphaMat ℓ
      * (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (alphaMat ℓ * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hcoe, mul_assoc]
    _ = (repMat ℓ (some ⟨0, hℓ.pos⟩)
          * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [repMat_some_zero_FHCE hℓ.pos]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m)
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hm]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (repMat ℓ m
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [mul_assoc]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ)
          * ((((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
            * alphaMat ℓ) := by
        rw [repMat_mul_cosetRep]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ)
          * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * alphaMat ℓ := by
        rw [mul_assoc]

noncomputable def heckeCosetEquiv (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective (cosetOfRep hℓ hℓN)
    ⟨cosetOfRep_injective hℓ hℓN, cosetOfRep_surjective hℓ hℓN⟩
end Bijection
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
namespace ModularCurve
section IndexEq
variable {N ℓ : ℕ}
end IndexEq
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
namespace ModularCurve
namespace Period
section CosetMatch
variable {N ℓ : ℕ} [NeZero ℓ]

private theorem map_int_mul''_FHCE (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem repGL_eq_rawDelta_mul (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repGL ℓ i = gammaToGL N (rawDelta hℓ hℓN i)
      * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
  have key : repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i)
      = gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repMat ℓ i).map (algebraMap ℤ ℝ)
        * ((((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
      = ((((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
        * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
    rw [← map_int_mul''_FHCE, ← map_int_mul''_FHCE, repMat_mul_cosetRep]
  calc repGL ℓ i
      = (repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i))
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = (gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ)
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [key]
    _ = gammaToGL N (rawDelta hℓ hℓN i)
          * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
        rw [mul_assoc, map_inv]

theorem exists_heckeCosetRep_coe_eq (γ : Gamma0 N) :
    ∃ ε : Gamma0 N, heckeCosetRep N ℓ (γ : Gamma0 N ⧸ heckeUpper N ℓ)
      = gammaToGL N ε * (alphaGL ℓ * gammaToGL N γ⁻¹) := by
  obtain ⟨h, hout⟩ := QuotientGroup.mk_out_eq_mul (heckeUpper N ℓ) γ
  refine ⟨heckeConj N ℓ h⁻¹, ?_⟩
  rw [heckeCosetRep_def,
    show Quotient.out ((γ : Gamma0 N ⧸ heckeUpper N ℓ)) = γ * (h : Gamma0 N) from hout,
    _root_.mul_inv_rev, map_mul, ← mul_assoc, ← mul_assoc]
  congr 1

  exact (gammaToGL_heckeConj_mul_alphaGL N ℓ h⁻¹).symm

theorem heckeCosetMatch (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : HeckeCosetMatch N ℓ := by
  refine ⟨heckeCosetEquiv hℓ hℓN, fun i => ?_⟩
  obtain ⟨ε, hε⟩ := exists_heckeCosetRep_coe_eq (ℓ := ℓ) (cosetRep hℓ hℓN i)
  refine ⟨rawDelta hℓ hℓN i * ε⁻¹, ?_⟩
  rw [show heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) from rfl,
    hε, map_mul, map_inv, mul_assoc, ← mul_assoc ((gammaToGL N ε)⁻¹), inv_mul_cancel, one_mul]
  exact repGL_eq_rawDelta_mul hℓ hℓN i

end CosetMatch
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Cascade

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ]
end Cascade
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup

open scoped MatrixGroups

namespace ModularCurve
namespace Period

section UqCosets

private theorem exists_lt_natCast_add_dvd_FHBPCE {q : ℕ} (hq : q ≠ 0) (x : ℤ) :
    ∃ v : ℕ, v < q ∧ (q : ℤ) ∣ ((v : ℤ) + x) := by
  haveI : NeZero q := ⟨hq⟩
  refine ⟨((-x : ℤ) : ZMod q).val, ZMod.val_lt _, ?_⟩
  have h1 : ((((((-x : ℤ) : ZMod q).val : ℕ) : ℤ) + x : ℤ) : ZMod q) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h1

theorem unipotentUpper_mul_mem_heckeUpper_of_dvd (N q : ℕ) (hqN : q ∣ N) (γ : Gamma0 N)
    (t : ℤ)
    (ht : (q : ℤ) ∣ (t + ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) :
    unipotentUpper N t * γ ∈ heckeUpper N q := by

  have hc : (q : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (Int.natCast_dvd_natCast.mpr hqN).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp γ.2)

  have hdet : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (γ : SL(2, ℤ)).2

  have hentry : (((unipotentUpper N t * γ : Gamma0 N) : SL(2, ℤ))) 0 1
      = 1 * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        + t * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
    (Matrix.two_mul_expl
      (((unipotentUpper N t : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).2.1
  rw [mem_heckeUpper, hentry]

  have key : 1 * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + t * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (-(((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) *
            ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
        + ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
            (t + ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
              ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
    linear_combination (-(((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) * hdet
  rw [key]
  exact dvd_add (hc.mul_left _) (ht.mul_left _)

def uqCosetOfRep (N q : ℕ) (j : Fin q) : Gamma0 N ⧸ heckeUpper N q :=
  (unipotentUpper N (-(j : ℤ)) : Gamma0 N ⧸ heckeUpper N q)

theorem uqCosetOfRep_def (N q : ℕ) (j : Fin q) :
    uqCosetOfRep N q j = (unipotentUpper N (-(j : ℤ)) : Gamma0 N ⧸ heckeUpper N q) :=
  rfl

theorem uqCosetOfRep_injective (N q : ℕ) : Function.Injective (uqCosetOfRep N q) := by
  intro j j' h
  rw [uqCosetOfRep_def, uqCosetOfRep_def, QuotientGroup.eq, inv_unipotentUpper, neg_neg,
    unipotentUpper_mul, mem_heckeUpper] at h

  have h' : (q : ℤ) ∣ ((j : ℤ) + -(j' : ℤ)) := h
  have hj := j.isLt
  have hj' := j'.isLt
  have hzero : (j : ℤ) + -(j' : ℤ) = 0 := by
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h' ?_
    rw [Int.natAbs_natCast]
    omega
  have hval : (j : ℕ) = (j' : ℕ) := by omega
  exact Fin.ext hval

theorem uqCosetOfRep_surjective (N q : ℕ) (hq : q ≠ 0) (hqN : q ∣ N) :
    Function.Surjective (uqCosetOfRep N q) := by
  intro z
  obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 N, (γ : Gamma0 N ⧸ heckeUpper N q) = z :=
    ⟨Quotient.out z, QuotientGroup.out_eq' z⟩
  obtain ⟨v, hvlt, hvdvd⟩ := exists_lt_natCast_add_dvd_FHBPCE hq
    (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
  refine ⟨⟨v, hvlt⟩, ?_⟩
  rw [uqCosetOfRep_def, QuotientGroup.eq, inv_unipotentUpper, neg_neg]
  exact unipotentUpper_mul_mem_heckeUpper_of_dvd N q hqN γ _ hvdvd

noncomputable def uqCosetEquiv (N q : ℕ) (hq : q ≠ 0) (hqN : q ∣ N) :
    Fin q ≃ (Gamma0 N ⧸ heckeUpper N q) :=
  Equiv.ofBijective (uqCosetOfRep N q)
    ⟨uqCosetOfRep_injective N q, uqCosetOfRep_surjective N q hq hqN⟩
end UqCosets
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
namespace ModularCurve
section BadPrimeIndex
variable {N q : ℕ}
end BadPrimeIndex
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section DegreeZeroBadPrime
end DegreeZeroBadPrime
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section EisensteinBridgeDischarge
end EisensteinBridgeDischarge
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup HeckeAnalytic UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm

namespace ModularCurve
namespace Period

attribute [local instance]
  ModularCurve.Period.instFintypeQuotientSubtypeSpecialLinearGroupFinOfNatNatIntMemSubgroupGamma0HeckeUpperOfNeZero

section Statement

variable (N q : ℕ) [NeZero q]

def HeckeUCosetMatch : Prop :=
  ∃ e : Fin q ≃ (Gamma0 N ⧸ heckeUpper N q),
    ∀ j : Fin q, ∃ δ : Gamma0 N,
      HeckeAnalytic.repGL q (Option.some j) = gammaToGL N δ * heckeCosetRep N q (e j)

end Statement
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section MatrixIdentity

variable {q : ℕ}

private theorem map_int_mul_cast_FHUCM (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem alphaMat_mul_coe_unipotentUpper (N : ℕ) (j : Fin q) :
    alphaMat q
        * (((unipotentUpper N (j : ℤ) : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = repMat q (some j) := by
  show !![1, 0; 0, (q : ℤ)] * !![1, (j : ℤ); 0, 1] = !![1, (j : ℤ); 0, (q : ℤ)]
  rw [Matrix.mul_fin_two]
  refine Matrix.ext fun x y => ?_
  fin_cases x <;> fin_cases y
  · show (1 * 1 + 0 * 0 : ℤ) = 1
    ring
  · show (1 * (j : ℤ) + 0 * 1 : ℤ) = (j : ℤ)
    ring
  · show (0 * 1 + (q : ℤ) * 0 : ℤ) = 0
    ring
  · show (0 * (j : ℤ) + (q : ℤ) * 1 : ℤ) = (q : ℤ)
    ring

theorem repGL_some_eq_alphaGL_mul (N : ℕ) [NeZero q] (j : Fin q) :
    repGL q (some j) = alphaGL q * gammaToGL N (unipotentUpper N (j : ℤ)) := by
  apply Units.ext
  rw [Units.val_mul]
  show (repMat q (some j)).map (algebraMap ℤ ℝ)
      = (alphaMat q).map (algebraMap ℤ ℝ)
        * ((((unipotentUpper N (j : ℤ) : Gamma0 N) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))
  rw [← map_int_mul_cast_FHUCM, alphaMat_mul_coe_unipotentUpper]

end MatrixIdentity
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Discharge

variable {N q : ℕ} [NeZero q]

theorem heckeUCosetMatch (hqN : q ∣ N) : HeckeUCosetMatch N q := by
  refine ⟨uqCosetEquiv N q (NeZero.ne q) hqN, fun j => ?_⟩
  obtain ⟨ε, hε⟩ := exists_heckeCosetRep_coe_eq (ℓ := q) (unipotentUpper N (-(j : ℤ)))
  refine ⟨ε⁻¹, ?_⟩
  rw [show uqCosetEquiv N q (NeZero.ne q) hqN j
        = (unipotentUpper N (-(j : ℤ)) : Gamma0 N ⧸ heckeUpper N q) from rfl,
    hε, map_inv (gammaToGL N) ε, ← mul_assoc, inv_mul_cancel, one_mul, inv_unipotentUpper,
    neg_neg]
  exact repGL_some_eq_alphaGL_mul N j
end Discharge
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section SlashBridge
variable {N q : ℕ} [NeZero q]

theorem heckeUSlashSum_eq_heckeQuotSlashSum (hmatch : HeckeUCosetMatch N q) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    HeckeAnalytic.heckeUSlashSum 2 q f = heckeQuotSlashSum N q f := by
  obtain ⟨e, he⟩ := hmatch
  rw [HeckeAnalytic.heckeUSlashSum, heckeQuotSlashSum,
    ← Equiv.sum_comp e fun x => f ∣[(2 : ℤ)] heckeCosetRep N q x]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨δ, hδ⟩ := he j
  rw [hδ, SlashAction.slash_mul,
    hf (gammaToGL N δ) (Subgroup.mem_map.mpr ⟨(δ : SL(2, ℤ)), δ.2, rfl⟩)]

end SlashBridge
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Intertwining

variable {N : ℕ} [NeZero N] {q : ℕ} [NeZero q]

theorem periodChar_heckeU_of_match (hmatch : HeckeUCosetMatch N q) {hq : q.Prime}
    {hqN : q ∣ N} (f : CuspForm (Gamma0 N) 2) {Fprim Fprim' : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (CuspForm.heckeU q hq hqN f τ) ↑τ) :
    hF'.periodChar = heckeOperator ℂ ℂ N q hF.periodChar := by
  refine periodChar_heckeQuotSlashSum hF hFf hF' fun τ => ?_
  have heq : CuspForm.heckeU q hq hqN f τ = heckeQuotSlashSum N q (⇑f) τ := by
    show HeckeAnalytic.heckeUSlashSum 2 q (⇑f) τ = heckeQuotSlashSum N q (⇑f) τ
    rw [heckeUSlashSum_eq_heckeQuotSlashSum hmatch
      (SlashInvariantFormClass.slash_action_eq f)]
  rw [← heq]
  exact hF'f τ
end Intertwining
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve

section DimensionCount

end DimensionCount
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
namespace Period
open UpperHalfPlane Filter Topology
variable {Γ : Subgroup SL(2, ℤ)}

theorem IsEquivariantPrimitive.periodChar_eq_of_hasDerivAt {F G : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (hG : IsEquivariantPrimitive Γ G)
    (hFf : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hGf : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (f τ) ↑τ) :
    hF.periodChar = hG.periodChar := by

  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hFf hGf
  refine Subtype.ext (funext fun γ => ?_)
  exact hF.period_congr hG c (fun z => by simpa [ofComplex_apply] using hc z) γ

theorem IsEquivariantPrimitive.periodChar_smul {F : ℍ → ℂ} (c : ℂ)
    (hF : IsEquivariantPrimitive Γ F) :
    (hF.smul c).periodChar = c • hF.periodChar := by
  refine Subtype.ext (funext fun γ => ?_)
  simpa [periodChar_apply] using hF.period_smul c γ

theorem hasDerivAt_smul_comp_ofComplex {F : ℍ → ℂ} {f : ℍ → ℂ} (c : ℂ)
    (hFf : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt ((c • F) ∘ ofComplex) (c * f τ) ↑τ := by
  have h := (hFf τ).const_mul c
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  show (c • F) (ofComplex z) = c * F (ofComplex z)
  rw [Pi.smul_apply, smul_eq_mul]

end Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Injectivity

open Period UpperHalfPlane Filter Topology
end Injectivity
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

namespace ModularCurve
namespace Period

open UpperHalfPlane Filter Topology CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm Manifold Real

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

theorem IsEquivariantPrimitive.invariant_of_forall_period_eq_zero
    (hF : IsEquivariantPrimitive Γ F) (hzero : ∀ γ : Γ, hF.period γ = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : F (γ • z) = F z := by
  have h := hF.sub_eq_period ⟨γ, hγ⟩ z
  rw [hzero ⟨γ, hγ⟩] at h
  exact sub_eq_zero.mp h

theorem IsEquivariantPrimitive.periodChar_eq_zero_iff (hF : IsEquivariantPrimitive Γ F) :
    hF.periodChar = 0 ↔ ∀ γ : Γ, hF.period γ = 0 := by
  constructor
  · intro h γ
    have : (hF.periodChar : Γ → ℂ) γ = ((0 : addChars ℂ Γ ℂ) : Γ → ℂ) γ := by rw [h]
    simpa [periodChar_apply] using this
  · intro h
    refine Subtype.ext (funext fun γ => ?_)
    simpa [periodChar_apply] using h γ

section WeightZero

variable (Γ)

theorem slash_zero_apply (G : ℍ → ℂ) (δ : SL(2, ℤ)) (τ : ℍ) :
    (G ∣[(0 : ℤ)] δ) τ = G (δ • τ) := by
  rw [ModularForm.SL_slash_def]
  simp

variable [Γ.FiniteIndex]

noncomputable def weightZeroModularForm
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (F ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = F z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun := F
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    show F ∣[(0 : ℤ)] γ = F
    funext τ
    exact (slash_zero_apply F γ τ).trans (hinv γ hγ τ)
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    exact (hholo ⟨z, hz⟩).differentiableWithinAt
  bdd_at_cusps' := by
    intro c hc

    have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      rintro g ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
    rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
    obtain ⟨L, hL⟩ := hlim δ
    have hslash : F ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ)
        = fun w : ℍ => F (δ • w) := by
      funext τ
      exact slash_zero_apply F δ τ
    rw [hslash]
    exact hL.isBigO_one ℝ

theorem exists_const_of_invariant_of_tendsto
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (F ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = F z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    ∃ c : ℂ, F = Function.const ℍ c := by
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (weightZeroModularForm Γ hholo hinv hlim)
  exact ⟨c, hc⟩

end WeightZero
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Worker

variable {N : ℕ} [NeZero N]

theorem eq_zero_of_const_of_hasDerivAt {f : ℍ → ℂ} {c : ℂ}
    (hconst : F = Function.const ℍ c)
    (hderiv : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) : f τ = 0 := by
  have h1 : HasDerivAt (F ∘ ofComplex) (f τ) ↑τ := hderiv τ
  have h2 : HasDerivAt (F ∘ ofComplex) 0 ↑τ := by
    have : F ∘ ofComplex = fun _ : ℂ => c := by
      funext z
      simp [hconst]
    rw [this]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem CuspForm.eq_zero_of_periodChar_eq_zero_of_tendsto {f : CuspForm (Gamma0 N) 2}
    {Fprim : ℍ → ℂ} (hFprim : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L))
    (hzero : hFprim.periodChar = 0) : f = 0 := by

  have hinv : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, Fprim (γ • z) = Fprim z := fun γ hγ z =>
    hFprim.invariant_of_forall_period_eq_zero (hFprim.periodChar_eq_zero_iff.mp hzero) hγ z

  have hholo : ∀ τ : ℍ, DifferentiableAt ℂ (Fprim ∘ ofComplex) ↑τ := fun τ =>
    (hFf τ).differentiableAt

  obtain ⟨c, hc⟩ := exists_const_of_invariant_of_tendsto (Gamma0 N) hholo hinv hlim

  ext τ
  have := eq_zero_of_const_of_hasDerivAt hc hFf τ
  simpa using this

end Worker
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Headline

variable {N : ℕ} [NeZero N]

theorem CuspForm.eq_zero_of_periodChar_eq_zero_of_hasDerivAt {f : CuspForm (Gamma0 N) 2}
    {Fprim : ℍ → ℂ} (hFprim : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hzero : hFprim.periodChar = 0) : f = 0 := by

  obtain ⟨Fcan, hFcanf, -, hFcanequiv, hFcanlim⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f

  have hsame : hFprim.periodChar = hFcanequiv.periodChar :=
    hFprim.periodChar_eq_of_hasDerivAt hFcanequiv hFf hFcanf
  exact CuspForm.eq_zero_of_periodChar_eq_zero_of_tendsto hFcanequiv hFcanf hFcanlim
    (hsame ▸ hzero)

theorem CuspForm.periodChar_ne_zero_of_ne_zero {f : CuspForm (Gamma0 N) 2} (hf : f ≠ 0)
    {Fprim : ℍ → ℂ} (hFprim : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) :
    hFprim.periodChar ≠ 0 := fun hzero =>
  hf (CuspForm.eq_zero_of_periodChar_eq_zero_of_hasDerivAt hFprim hFf hzero)

end Headline
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Gates
end Gates
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve.Period
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

namespace ModularCurve

p2m_open "Subgroup CongruenceSubgroup Polynomial Real.Polynomial"

open scoped MatrixGroups

section TransferAlgebra

variable (N : ℕ) [NeZero N]

theorem isNoetherian_end_addChars_int :
    IsNoetherian ℤ (Module.End ℤ (addChars ℤ (Gamma0 N) ℤ)) :=
  isNoetherian_linearMap ℤ (addChars ℤ (Gamma0 N) ℤ) (addChars ℤ (Gamma0 N) ℤ)
end TransferAlgebra
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Intertwining
variable {N : ℕ} [NeZero N]
variable (N) in

noncomputable def ofIntChars : addChars ℤ (Gamma0 N) ℤ →+ addChars ℂ (Gamma0 N) ℂ where
  toFun ψ := ⟨fun γ => (ψ.1 γ : ℂ), fun γ δ => by
    show (ψ.1 (γ * δ) : ℂ) = (ψ.1 γ : ℂ) + (ψ.1 δ : ℂ)
    exact_mod_cast ψ.2 γ δ⟩
  map_zero' := by
    apply Subtype.ext
    funext γ
    show (((0 : addChars ℤ (Gamma0 N) ℤ) : Gamma0 N → ℤ) γ : ℂ)
      = ((0 : addChars ℂ (Gamma0 N) ℂ) : Gamma0 N → ℂ) γ
    simp
  map_add' ψ ψ' := by
    apply Subtype.ext
    funext γ
    show ((ψ.1 γ + ψ'.1 γ : ℤ) : ℂ) = (ψ.1 γ : ℂ) + (ψ'.1 γ : ℂ)
    push_cast
    ring
omit [NeZero N] in

theorem ofIntChars_heckeOperator (ℓ : ℕ) [NeZero ℓ] (ψ : addChars ℤ (Gamma0 N) ℤ) :
    ofIntChars N (heckeOperator ℤ ℤ N ℓ ψ) = heckeOperator ℂ ℂ N ℓ (ofIntChars N ψ) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  apply Subtype.ext
  funext g
  have hL : (ofIntChars N (heckeOperator ℤ ℤ N ℓ ψ)).1 g
      = ((heckeOperator ℤ ℤ N ℓ ψ).1 g : ℂ) := rfl
  rw [hL, heckeOperator_apply, heckeOperator_apply]
  push_cast
  rfl
end Intertwining
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section ConditionalExits
variable {N : ℕ} [NeZero N]
end ConditionalExits
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Gates
variable {N : ℕ} [NeZero N]
end Gates
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

namespace ModularCurve

open Subgroup CongruenceSubgroup

section CharModuleDef

variable (G : Type*) [Group G]

noncomputable def charRelations : Submodule ℤ (G →₀ ℤ) :=
  Submodule.span ℤ
    {x | ∃ γ δ : G, x = Finsupp.single (γ * δ) 1 - Finsupp.single γ 1 - Finsupp.single δ 1}

abbrev CharModule : Type _ := (G →₀ ℤ) ⧸ charRelations G

noncomputable def charGen (g : G) : CharModule G :=
  Submodule.Quotient.mk (Finsupp.single g 1)

variable {G}

theorem charGen_mul (γ δ : G) : charGen G (γ * δ) = charGen G γ + charGen G δ := by
  have hmem : Finsupp.single (γ * δ) (1 : ℤ) - Finsupp.single γ 1 - Finsupp.single δ 1
      ∈ charRelations G :=
    Submodule.subset_span ⟨γ, δ, rfl⟩
  have h0 : (Submodule.Quotient.mk (Finsupp.single (γ * δ) (1 : ℤ)
        - Finsupp.single γ 1 - Finsupp.single δ 1) : CharModule G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h0
  exact h0

theorem charGen_one : charGen G 1 = 0 := by
  have h := charGen_mul (G := G) 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem charGen_inv (γ : G) : charGen G γ⁻¹ = -charGen G γ := by
  have h := charGen_mul (G := G) γ⁻¹ γ
  rw [inv_mul_cancel, charGen_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem addSubgroup_closure_range_charGen :
    AddSubgroup.closure (Set.range (charGen G)) = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).mpr fun x => ?_
  obtain ⟨y, rfl⟩ := (charRelations G).mkQ_surjective x
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add f g hf hg => rw [map_add]; exact AddSubgroup.add_mem _ hf hg
  | single a b =>

      induction b using Int.induction_on with
      | zero => rw [Finsupp.single_zero, map_zero]; exact AddSubgroup.zero_mem _
      | succ n ih =>
          rw [Finsupp.single_add, map_add]
          exact AddSubgroup.add_mem _ ih (AddSubgroup.subset_closure ⟨a, rfl⟩)
      | pred n ih =>
          rw [Finsupp.single_sub, map_sub]
          exact AddSubgroup.sub_mem _ ih (AddSubgroup.subset_closure ⟨a, rfl⟩)

variable (G) in

theorem addGroup_fg_charModule [Group.FG G] : AddGroup.FG (CharModule G) := by
  classical
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  refine AddGroup.fg_def.mpr ⟨hSfin.toFinset.image (charGen G), ?_⟩
  rw [eq_top_iff, ← addSubgroup_closure_range_charGen]
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro _ ⟨g, rfl⟩

  have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
      exact AddSubgroup.subset_closure
        (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem (charGen G) (hSfin.mem_toFinset.mpr hs)))
  | one => rw [charGen_one]; exact AddSubgroup.zero_mem _
  | mul a b _ _ iha ihb => rw [charGen_mul]; exact AddSubgroup.add_mem _ iha ihb
  | inv a _ iha => rw [charGen_inv]; exact AddSubgroup.neg_mem _ iha

end CharModuleDef
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section UniversalProperty

variable {G : Type*} [Group G] {K : Type*} [CommRing K]

noncomputable def charOfHom (f : CharModule G →+ K) : addChars K G K :=
  ⟨fun g => f (charGen G g), fun γ δ => by
    show f (charGen G (γ * δ)) = f (charGen G γ) + f (charGen G δ)
    rw [charGen_mul, map_add]⟩

@[scoped simp]
theorem charOfHom_apply (f : CharModule G →+ K) (g : G) :
    (charOfHom f).1 g = f (charGen G g) :=
  rfl

noncomputable def homOfChar (φ : addChars K G K) : CharModule G →+ K :=
  (Submodule.liftQ _ (Finsupp.linearCombination ℤ (φ.1 : G → K))
    (Submodule.span_le.mpr (by
      rintro _ ⟨γ, δ, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
        Finsupp.linearCombination_single, one_smul]
      rw [addChars.apply_mul φ γ δ]
      ring))).toAddMonoidHom

@[scoped simp]
theorem homOfChar_charGen (φ : addChars K G K) (g : G) :
    homOfChar φ (charGen G g) = φ.1 g := by
  have h : homOfChar φ (charGen G g)
      = Finsupp.linearCombination ℤ (φ.1 : G → K) (Finsupp.single g 1) := rfl
  rw [h, Finsupp.linearCombination_single, one_smul]

theorem charOfHom_homOfChar (φ : addChars K G K) : charOfHom (homOfChar φ) = φ := by
  apply Subtype.ext
  funext g
  rw [charOfHom_apply, homOfChar_charGen]

end UniversalProperty
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section DualBasis

theorem exists_eq_sum_intCast_of_torsionFree {B : Type*} [AddCommGroup B] [Module ℤ B]
    [Module.Finite ℤ B] [Module.IsTorsionFree ℤ B] (g : B →ₗ[ℤ] ℂ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (h : Fin n → (B →ₗ[ℤ] ℤ)),
      ∀ y : B, g y = ∑ i, c i * ((h i y : ℤ) : ℂ) := by
  classical
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := B)
  refine ⟨n, fun i => g (b i), fun i => b.coord i, fun y => ?_⟩
  conv_lhs => rw [← b.linearCombination_repr y]
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g.map_smul, zsmul_eq_mul, Module.Basis.coord_apply]
  ring

variable {A : Type*} [AddCommGroup A]

theorem apply_eq_zero_of_mem_torsion (f : A →+ ℂ) {x : A}
    (hx : x ∈ Submodule.torsion ℤ A) : f x = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  rw [Submonoid.smul_def] at ha
  have h2 := congrArg f ha
  rw [map_zero, AddMonoidHom.map_zsmul, zsmul_eq_mul] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (Int.cast_eq_zero.mp h) (nonZeroDivisors.coe_ne_zero a)
  · exact h

theorem exists_eq_sum_smul_intCast (hfg : AddGroup.FG A) (f : A →+ ℂ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (h : Fin n → (A →+ ℤ)),
      ∀ x : A, f x = ∑ i, c i * ((h i x : ℤ) : ℂ) := by
  classical
  haveI : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr hfg

  have hker : Submodule.torsion ℤ A ≤ LinearMap.ker f.toIntLinearMap := fun x hx =>
    LinearMap.mem_ker.mpr (apply_eq_zero_of_mem_torsion f hx)

  haveI : Module.Finite ℤ (A ⧸ Submodule.torsion ℤ A) :=
    Module.Finite.of_surjective (M := A) ((Submodule.torsion ℤ A).mkQ)
      ((Submodule.torsion ℤ A).mkQ_surjective)

  obtain ⟨n, c, h, hsum⟩ :=
    exists_eq_sum_intCast_of_torsionFree
      ((Submodule.torsion ℤ A).liftQ f.toIntLinearMap hker)
  refine ⟨n, c, fun i => ((h i) ∘ₗ (Submodule.torsion ℤ A).mkQ).toAddMonoidHom,
    fun x => ?_⟩
  have hfact : f x = ((Submodule.torsion ℤ A).liftQ f.toIntLinearMap hker)
      ((Submodule.torsion ℤ A).mkQ x) := by
    rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]
    rfl
  rw [hfact]
  exact hsum _

end DualBasis
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Spanning

variable {G : Type*} [Group G]

theorem addChars.span_intCast_eq_top [Group.FG G]
    (F : addChars ℤ G ℤ → addChars ℂ G ℂ) (hF : ∀ ψ γ, (F ψ).1 γ = ((ψ.1 γ : ℤ) : ℂ)) :
    Submodule.span ℂ (Set.range F) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun φ => ?_

  obtain ⟨n, c, h, hsum⟩ :=
    exists_eq_sum_smul_intCast (addGroup_fg_charModule G) (homOfChar φ)

  set ψ : Fin n → addChars ℤ G ℤ := fun i => charOfHom (h i) with hψdef

  have hmem : (∑ i, c i • F (ψ i)) ∈ Submodule.span ℂ (Set.range F) :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ i, rfl⟩)

  suffices hφ : φ = ∑ i, c i • F (ψ i) by rw [hφ]; exact hmem
  apply Subtype.ext
  funext γ
  trans (∑ i, c i * ((h i (charGen G γ) : ℤ) : ℂ))
  ·
    conv_lhs => rw [← charOfHom_homOfChar φ]
    exact hsum (charGen G γ)
  ·
    symm
    calc (↑(∑ i, c i • F (ψ i)) : G → ℂ) γ
        = ((addChars ℂ G ℂ).subtype (∑ i, c i • F (ψ i))) γ := rfl
      _ = (∑ i, (addChars ℂ G ℂ).subtype (c i • F (ψ i))) γ := by rw [map_sum]
      _ = ∑ i, ((addChars ℂ G ℂ).subtype (c i • F (ψ i))) γ := by rw [Finset.sum_apply]
      _ = ∑ i, c i * ((h i (charGen G γ) : ℤ) : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            show c i * (F (ψ i)).1 γ = c i * ((h i (charGen G γ) : ℤ) : ℂ)
            rw [hF (ψ i) γ]
            rfl

end Spanning
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section Gamma0Instance

variable (N : ℕ) [NeZero N]

theorem span_range_ofIntChars : Submodule.span ℂ (Set.range (ofIntChars N)) = ⊤ :=
  addChars.span_intCast_eq_top (ofIntChars N) (fun _ _ => rfl)
end Gamma0Instance
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Gates

theorem gate_line_not_spanned_by_int_points :
    ∃ W : Submodule ℂ (ℂ × ℂ),
      Submodule.span ℂ ((W : Set (ℂ × ℂ)) ∩
        Set.range (fun p : ℤ × ℤ => ((p.1 : ℂ), (p.2 : ℂ)))) ≠ W := by
  classical
  refine ⟨Submodule.span ℂ {(1, Complex.I)}, fun hcontra => ?_⟩

  have hint : (Submodule.span ℂ {((1 : ℂ), Complex.I)} : Set (ℂ × ℂ)) ∩
      Set.range (fun p : ℤ × ℤ => ((p.1 : ℂ), (p.2 : ℂ))) ⊆ {0} := by
    rintro ⟨x, y⟩ ⟨hmem, ⟨⟨a, b⟩, hab⟩⟩
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at hk
    obtain ⟨hk1, hk2⟩ := hk
    simp only [Prod.mk.injEq] at hab
    obtain ⟨ha, hb⟩ := hab

    have hkim : k.im = 0 := by rw [hk1.trans ha.symm]; simp
    have hkre : k.re = 0 := by
      have him := congrArg Complex.im (hk2.trans hb.symm)
      simpa [Complex.mul_im, hkim] using him
    have hk0 : k = 0 := by
      apply Complex.ext <;> simp [hkre, hkim]
    have hx : x = 0 := by rw [← hk1, hk0]
    have hy : y = 0 := by rw [← hk2, hk0, zero_mul]
    simp [hx, hy, Prod.ext_iff]

  have hbot : Submodule.span ℂ ((Submodule.span ℂ {((1 : ℂ), Complex.I)} : Set (ℂ × ℂ)) ∩
      Set.range (fun p : ℤ × ℤ => ((p.1 : ℂ), (p.2 : ℂ)))) ≤ ⊥ := by
    rw [← Submodule.span_zero_singleton (R := ℂ) (M := ℂ × ℂ)]
    exact Submodule.span_mono hint
  rw [hcontra] at hbot
  have hmem : ((1 : ℂ), Complex.I) ∈ (⊥ : Submodule ℂ (ℂ × ℂ)) :=
    hbot (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_bot, Prod.ext_iff] at hmem
  exact one_ne_zero hmem.1
end Gates
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section AxiomAudit
end AxiomAudit
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

namespace ModularCurve

p2m_open "Subgroup CongruenceSubgroup Polynomial Real.Polynomial UpperHalfPlane P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

open scoped MatrixGroups

section PeriodHom

variable {N : ℕ} [NeZero N]

variable (N) in

noncomputable def periodMap (f : CuspForm (Gamma0 N) 2) : addChars ℂ (Gamma0 N) ℂ :=
  (CuspForm.exists_equivariantPrimitive_gamma0 f).choose_spec.2.2.1.periodChar

theorem periodMap_eq_periodChar {f : CuspForm (Gamma0 N) 2} {Fprim : ℍ → ℂ}
    (hFprim : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) :
    periodMap N f = hFprim.periodChar :=
  (CuspForm.exists_equivariantPrimitive_gamma0 f).choose_spec.2.2.1.periodChar_eq_of_hasDerivAt
    hFprim (CuspForm.exists_equivariantPrimitive_gamma0 f).choose_spec.1 hFf

theorem periodMap_add (f g : CuspForm (Gamma0 N) 2) :
    periodMap N (f + g) = periodMap N f + periodMap N g := by
  obtain ⟨F, hFf, -, hFe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨G, hGg, -, hGe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 g

  have hsum : ∀ τ : ℍ, HasDerivAt ((F + G) ∘ ofComplex) ((f + g) τ) ↑τ := by
    intro τ
    have h := (hFf τ).add (hGg τ)
    have hval : (f + g) τ = f τ + g τ := rfl
    rw [hval]
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    rfl
  rw [periodMap_eq_periodChar (hFe.add hGe) hsum, periodMap_eq_periodChar hFe hFf,
    periodMap_eq_periodChar hGe hGg]
  exact Subtype.ext (funext fun γ => hFe.period_add hGe γ)

theorem periodMap_smul (c : ℂ) (f : CuspForm (Gamma0 N) 2) :
    periodMap N (c • f) = c • periodMap N f := by
  obtain ⟨F, hFf, -, hFe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f
  have hsmul : ∀ τ : ℍ, HasDerivAt ((c • F) ∘ ofComplex) ((c • f) τ) ↑τ := by
    intro τ
    have h := hasDerivAt_smul_comp_ofComplex c hFf τ
    have hval : (c • f) τ = c * f τ := rfl
    rwa [hval]
  rw [periodMap_eq_periodChar (hFe.smul c) hsmul, periodMap_eq_periodChar hFe hFf]
  exact hFe.periodChar_smul c

variable (N) in

noncomputable def periodHom : CuspForm (Gamma0 N) 2 →ₗ[ℂ] addChars ℂ (Gamma0 N) ℂ where
  toFun := periodMap N
  map_add' := periodMap_add
  map_smul' := periodMap_smul

@[scoped simp]
theorem periodHom_apply (f : CuspForm (Gamma0 N) 2) : periodHom N f = periodMap N f :=
  rfl

theorem periodHom_injective : Function.Injective (periodHom N) := by
  intro f g hfg
  rw [← sub_eq_zero] at hfg ⊢
  rw [← map_sub] at hfg
  by_contra hne
  obtain ⟨F, hFf, -, hFe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 (f - g)
  exact CuspForm.periodChar_ne_zero_of_ne_zero hne hFe hFf
    ((periodMap_eq_periodChar hFe hFf).symm.trans hfg)

theorem periodHom_hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    periodHom N (CuspForm.heckeHom ℓ hℓ hℓN f) = heckeOperator ℂ ℂ N ℓ (periodHom N f) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨F, hFf, -, hFe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F', hF'f, -, hF'e, -⟩ :=
    CuspForm.exists_equivariantPrimitive_gamma0 (CuspForm.hecke ℓ hℓ hℓN f)
  have hHom : CuspForm.heckeHom ℓ hℓ hℓN f = CuspForm.hecke ℓ hℓ hℓN f := rfl
  rw [periodHom_apply, periodHom_apply, hHom, periodMap_eq_periodChar hF'e hF'f,
    periodMap_eq_periodChar hFe hFf]
  exact periodChar_hecke_of_match (heckeCosetMatch hℓ hℓN) f hFe hFf hF'e hF'f

end PeriodHom
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section TripleAlgebra

variable (N : ℕ) [NeZero N]

abbrev HeckeTripleCarrier : Type _ :=
  Module.End ℤ (addChars ℤ (Gamma0 N) ℤ) × Module.End ℂ (addChars ℂ (Gamma0 N) ℂ)
    × Module.End ℂ (CuspForm (Gamma0 N) 2)

def heckeTripleGens : Set (HeckeTripleCarrier N) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    T = (heckeOperator ℤ ℤ N ℓ, heckeOperator ℂ ℂ N ℓ, CuspForm.heckeHom ℓ hℓ hℓN)}
variable {N}

def IsCompatibleTriple (T : HeckeTripleCarrier N) : Prop :=
  (∀ ψ, ofIntChars N (T.1 ψ) = T.2.1 (ofIntChars N ψ)) ∧
    (∀ f, periodHom N (T.2.2 f) = T.2.1 (periodHom N f))

theorem snd_eq_of_fst_eq {x y : HeckeTripleCarrier N}
    (hx : IsCompatibleTriple x) (hy : IsCompatibleTriple y) (h1 : x.1 = y.1) :
    x.2.1 = y.2.1 := by
  refine LinearMap.ext_on (span_range_ofIntChars N) ?_
  rintro _ ⟨ψ, rfl⟩
  rw [← hx.1 ψ, ← hy.1 ψ, h1]

theorem trd_eq_of_snd_eq {x y : HeckeTripleCarrier N}
    (hx : IsCompatibleTriple x) (hy : IsCompatibleTriple y) (h2 : x.2.1 = y.2.1) :
    x.2.2 = y.2.2 := by
  refine LinearMap.ext fun f => periodHom_injective ?_
  rw [hx.2 f, hy.2 f, h2]
end TripleAlgebra
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Finiteness
variable (N : ℕ) [NeZero N]

noncomputable def heckeTripleTrdHom :
    HeckeTripleCarrier N →ₐ[ℤ] Module.End ℂ (CuspForm (Gamma0 N) 2) :=
  (AlgHom.snd ℤ _ _).comp (AlgHom.snd ℤ _ _)

theorem heckeTripleTrdHom_image_gens :
    heckeTripleTrdHom N '' heckeTripleGens N = CuspForm.heckeSet N 2 := by
  ext T
  constructor
  · rintro ⟨_, ⟨ℓ, hℓ, hℓN, rfl⟩, rfl⟩
    exact ⟨ℓ, hℓ, hℓN, rfl⟩
  · rintro ⟨ℓ, hℓ, hℓN, rfl⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ⟨(heckeOperator ℤ ℤ N ℓ, heckeOperator ℂ ℂ N ℓ, CuspForm.heckeHom ℓ hℓ hℓN),
      ⟨ℓ, hℓ, hℓN, rfl⟩, rfl⟩
end Finiteness
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Gates
end Gates
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section

set_option autoImplicit false

namespace ModularCurve

p2m_open "Subgroup CongruenceSubgroup Polynomial Real.Polynomial UpperHalfPlane P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

open scoped MatrixGroups

section PeriodHomHeckeU

variable {N : ℕ} [NeZero N]

theorem periodHom_heckeU (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (f : CuspForm (Gamma0 N) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    periodHom N (CuspForm.heckeUHom q hq hqN f) = heckeOperator ℂ ℂ N q (periodHom N f) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨F, hFf, -, hFe, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F', hF'f, -, hF'e, -⟩ :=
    CuspForm.exists_equivariantPrimitive_gamma0 (CuspForm.heckeU q hq hqN f)
  have hHom : CuspForm.heckeUHom q hq hqN f = CuspForm.heckeU q hq hqN f := rfl
  rw [periodHom_apply, periodHom_apply, hHom, periodMap_eq_periodChar hF'e hF'f,
    periodMap_eq_periodChar hFe hFf]
  exact periodChar_heckeU_of_match (heckeUCosetMatch hqN) f hFe hFf hF'e hF'f
end PeriodHomHeckeU
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section UTriple
variable {N : ℕ} [NeZero N]
end UTriple
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section FullTripleAlgebra
variable (N : ℕ) [NeZero N]

def heckeTripleUGens : Set (HeckeTripleCarrier N) :=
  {T | ∃ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
    haveI : NeZero q := ⟨hq.ne_zero⟩
    T = (heckeOperator ℤ ℤ N q, heckeOperator ℂ ℂ N q, CuspForm.heckeUHom q hq hqN)}

noncomputable def heckeTripleAlgebraFull : Subalgebra ℤ (HeckeTripleCarrier N) :=
  Algebra.adjoin ℤ (heckeTripleGens N ∪ heckeTripleUGens N)

variable {N}
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isCompatibleTriple_of_mem_heckeTripleAlgebraFull {T : HeckeTripleCarrier N}
    (hT : T ∈ heckeTripleAlgebraFull N) : IsCompatibleTriple T := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with hT | hT
    · obtain ⟨ℓ, hℓ, hℓN, rfl⟩ := hT
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact ⟨fun ψ => ofIntChars_heckeOperator ℓ ψ, fun f => periodHom_hecke ℓ hℓ hℓN f⟩
    · obtain ⟨q, hq, hqN, rfl⟩ := hT
      haveI : NeZero q := ⟨hq.ne_zero⟩
      exact ⟨fun ψ => ofIntChars_heckeOperator q ψ, fun f => periodHom_heckeU q hq hqN f⟩
  | algebraMap r =>
    refine ⟨fun ψ => ?_, fun f => ?_⟩
    · show ofIntChars N
          ((algebraMap ℤ (Module.End ℤ (addChars ℤ (Gamma0 N) ℤ)) r) ψ)
        = (algebraMap ℤ (Module.End ℂ (addChars ℂ (Gamma0 N) ℂ)) r) (ofIntChars N ψ)
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      exact map_zsmul (ofIntChars N) r ψ
    · show periodHom N
          ((algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 N) 2)) r) f)
        = (algebraMap ℤ (Module.End ℂ (addChars ℂ (Gamma0 N) ℂ)) r) (periodHom N f)
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      exact map_zsmul (periodHom N) r f
  | add x y _ _ ihx ihy =>
    refine ⟨fun ψ => ?_, fun f => ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
      rw [ihx.1 ψ, ihy.1 ψ]
    · simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
      rw [ihx.2 f, ihy.2 f]
  | mul x y _ _ ihx ihy =>
    refine ⟨fun ψ => ?_, fun f => ?_⟩
    · simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
      rw [ihx.1 (y.1 ψ), ihy.1 ψ]
    · simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
      rw [ihx.2 (y.2.2 f), ihy.2 f]

theorem eq_of_fst_eq_of_mem_heckeTripleAlgebraFull {x y : HeckeTripleCarrier N}
    (hx : x ∈ heckeTripleAlgebraFull N) (hy : y ∈ heckeTripleAlgebraFull N)
    (h1 : x.1 = y.1) : x = y := by
  have hcx := isCompatibleTriple_of_mem_heckeTripleAlgebraFull hx
  have hcy := isCompatibleTriple_of_mem_heckeTripleAlgebraFull hy
  have h2 := snd_eq_of_fst_eq hcx hcy h1
  have h3 := trd_eq_of_snd_eq hcx hcy h2
  exact Prod.ext h1 (Prod.ext h2 h3)

end FullTripleAlgebra
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

section FullFiniteness

variable (N : ℕ) [NeZero N]

set_option synthInstance.maxHeartbeats 800000 in

noncomputable def heckeTripleFstFull :
    heckeTripleAlgebraFull N →ₗ[ℤ] Module.End ℤ (addChars ℤ (Gamma0 N) ℤ) :=
  (LinearMap.fst ℤ _ _).comp (heckeTripleAlgebraFull N).val.toLinearMap

set_option synthInstance.maxHeartbeats 800000 in

theorem heckeTripleFstFull_injective : Function.Injective (heckeTripleFstFull N) := by
  intro x y hxy
  have hxy' : (x : HeckeTripleCarrier N).1 = (y : HeckeTripleCarrier N).1 := hxy
  exact Subtype.ext (eq_of_fst_eq_of_mem_heckeTripleAlgebraFull x.2 y.2 hxy')

set_option synthInstance.maxHeartbeats 800000 in

theorem module_finite_heckeTripleAlgebraFull :
    Module.Finite ℤ (heckeTripleAlgebraFull N) := by
  haveI := isNoetherian_end_addChars_int N
  exact Module.Finite.of_injective (heckeTripleFstFull N) (heckeTripleFstFull_injective N)

theorem heckeTripleTrdHom_image_ugens :
    heckeTripleTrdHom N '' heckeTripleUGens N = CuspForm.heckeUSet N 2 := by
  ext T
  constructor
  · rintro ⟨_, ⟨q, hq, hqN, rfl⟩, rfl⟩
    exact ⟨q, hq, hqN, rfl⟩
  · rintro ⟨q, hq, hqN, rfl⟩
    haveI : NeZero q := ⟨hq.ne_zero⟩
    exact ⟨(heckeOperator ℤ ℤ N q, heckeOperator ℂ ℂ N q, CuspForm.heckeUHom q hq hqN),
      ⟨q, hq, hqN, rfl⟩, rfl⟩

theorem heckeTripleAlgebraFull_map_trd :
    (heckeTripleAlgebraFull N).map (heckeTripleTrdHom N)
      = CuspForm.heckeAlgebraIntFull N := by
  rw [heckeTripleAlgebraFull, AlgHom.map_adjoin, Set.image_union,
    heckeTripleTrdHom_image_gens, heckeTripleTrdHom_image_ugens]
  rfl

theorem heckeTripleTrdHomFull_mem (x : heckeTripleAlgebraFull N) :
    heckeTripleTrdHom N (x : HeckeTripleCarrier N) ∈ CuspForm.heckeAlgebraIntFull N := by
  rw [← heckeTripleAlgebraFull_map_trd]
  exact Subalgebra.mem_map.mpr ⟨(x : HeckeTripleCarrier N), x.2, rfl⟩

set_option synthInstance.maxHeartbeats 800000 in

noncomputable def heckeTripleTrdFull :
    heckeTripleAlgebraFull N →ₐ[ℤ] CuspForm.heckeAlgebraIntFull N :=
  AlgHom.codRestrict ((heckeTripleTrdHom N).comp (heckeTripleAlgebraFull N).val)
    (CuspForm.heckeAlgebraIntFull N) (fun x => heckeTripleTrdHomFull_mem N x)

set_option synthInstance.maxHeartbeats 800000 in

theorem heckeTripleTrdFull_surjective : Function.Surjective (heckeTripleTrdFull N) := by
  rintro ⟨y, hy⟩
  rw [← heckeTripleAlgebraFull_map_trd] at hy
  obtain ⟨x, hx, hxy⟩ := Subalgebra.mem_map.mp hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  show heckeTripleTrdHom N x = y
  exact hxy

set_option synthInstance.maxHeartbeats 800000 in

theorem module_finite_heckeAlgebraIntFull_unconditional :
    Module.Finite ℤ (CuspForm.heckeAlgebraIntFull N) := by
  haveI := module_finite_heckeTripleAlgebraFull N
  exact Module.Finite.of_surjective (heckeTripleTrdFull N).toLinearMap
    (heckeTripleTrdFull_surjective N)
end FullFiniteness
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
section Gates
end Gates
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end ModularCurve
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"
end
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period"

end Fact1
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1"

namespace Fact1Bridge

open Fact1 Fact1.HeckeAnalytic
p2m_open_scoped "MatrixGroups ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm"

lemma repGL_some_eq (p : ℕ) [NeZero p] (j : Fin p) :
    Fact1.HeckeAnalytic.repGL p (some j) = ModularForm.heckeMatrix p j := by
  apply Units.ext
  rw [Fact1.HeckeAnalytic.repGL_coe, ModularForm.val_heckeMatrix (NeZero.ne p)]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Fact1.HeckeAnalytic.repMat]

lemma repGL_none_eq (p : ℕ) [NeZero p] : Fact1.HeckeAnalytic.repGL p none = ModularForm.heckeDiagMatrix p := by
  apply Units.ext
  rw [Fact1.HeckeAnalytic.repGL_coe, ModularForm.val_heckeDiagMatrix (NeZero.ne p)]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Fact1.HeckeAnalytic.repMat]

theorem heckeUSlashSum_eq_heckeU (k : ℤ) (p : ℕ) [NeZero p] (f : UpperHalfPlane → ℂ) :
    Fact1.HeckeAnalytic.heckeUSlashSum k p f = ModularForm.heckeU k p f := by
  unfold Fact1.HeckeAnalytic.heckeUSlashSum ModularForm.heckeU
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [repGL_some_eq]

theorem heckeSlashSum_eq_heckeT (k : ℤ) (p : ℕ) [NeZero p] (f : UpperHalfPlane → ℂ) :
    Fact1.HeckeAnalytic.heckeSlashSum k p f = ModularForm.heckeT k p f := by
  unfold Fact1.HeckeAnalytic.heckeSlashSum ModularForm.heckeT
  rw [Fintype.sum_option, add_comm, repGL_none_eq, ← heckeUSlashSum_eq_heckeU]
  rfl

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem heckeTLin_eq_heckeHom {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    CuspForm.heckeTLin k hp hpN = Fact1.CuspForm.heckeHom (N := N) p hp hpN := by
  apply LinearMap.ext; intro f
  apply DFunLike.coe_injective
  haveI : NeZero p := ⟨hp.ne_zero⟩
  change ⇑(CuspForm.heckeTLin k hp hpN f) = ⇑(Fact1.CuspForm.heckeHom p hp hpN f)
  rw [CuspForm.coe_heckeTLin_apply, Fact1.CuspForm.heckeHom_apply]
  show ModularForm.heckeT k p ⇑f = Fact1.HeckeAnalytic.heckeSlashSum k p ⇑f
  rw [heckeSlashSum_eq_heckeT]

theorem heckeULin_eq_heckeUHom {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    CuspForm.heckeULin k hpN = Fact1.CuspForm.heckeUHom (N := N) p hp hpN := by
  apply LinearMap.ext; intro f
  apply DFunLike.coe_injective
  haveI : NeZero p := ⟨hp.ne_zero⟩
  change ⇑(CuspForm.heckeULin k hpN f) = ⇑(Fact1.CuspForm.heckeUHom p hp hpN f)
  rw [CuspForm.coe_heckeULin_apply, Fact1.CuspForm.heckeUHom_apply]
  show ModularForm.heckeU k p ⇑f = Fact1.HeckeAnalytic.heckeUSlashSum k p ⇑f
  rw [heckeUSlashSum_eq_heckeU]

theorem heckeAlgebra_le_heckeAlgebraIntFull (S : Set ℕ) :
    CuspForm.heckeAlgebra N 2 S ≤ Fact1.CuspForm.heckeAlgebraIntFull N := by
  refine Algebra.adjoin_le ?_
  rintro T (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩)
  · rw [heckeTLin_eq_heckeHom]; exact Fact1.CuspForm.heckeHom_mem_heckeAlgebraIntFull ℓ hℓ hℓN
  · rw [heckeULin_eq_heckeUHom hq]; exact Fact1.CuspForm.heckeUHom_mem_heckeAlgebraIntFull q hq hqN

theorem moduleFinite_heckeAlgebra_two (hfin : Module.Finite ℤ (Fact1.CuspForm.heckeAlgebraIntFull N)) (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S) := by
  haveI := hfin
  haveI : IsNoetherian ℤ (Fact1.CuspForm.heckeAlgebraIntFull N) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  exact Module.Finite.of_injective
    (Subalgebra.inclusion (heckeAlgebra_le_heckeAlgebraIntFull S)).toLinearMap
    (Subalgebra.inclusion_injective (heckeAlgebra_le_heckeAlgebraIntFull S))

end Fact1Bridge
p2m_reactivate "P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.CuspForm P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.addChars P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.ModularCurve.Period P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1"

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S) :=
  Fact1Bridge.moduleFinite_heckeAlgebra_two (Fact1.ModularCurve.module_finite_heckeAlgebraIntFull_unconditional N) S

end S_CuspForm_moduleFinite_heckeAlgebra_two
end P2MW
export P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two (solution)
