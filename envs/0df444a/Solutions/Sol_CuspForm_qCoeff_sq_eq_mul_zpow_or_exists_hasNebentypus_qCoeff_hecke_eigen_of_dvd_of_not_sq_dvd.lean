-- Prove2me | solution 1 for CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3a391aa5-2934-5f03-aafb-bb1b08ceb1fd

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_ModularForm_mdifferentiable_alSlash
import Theorems.Thm_ModularForm_isZeroAt_alSlash
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups

noncomputable section

namespace ALDich

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section API

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem map_int_mul (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

theorem SL_slash_apply' (k : ℤ) (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have h := ModularForm.SL_slash_apply (f := F) (k := k) γ τ
  rw [ModularGroup.denom_apply] at h
  exact h

theorem denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero _ τ

theorem isUnit_entry {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_entries γ)
  push_cast at this
  rw [hc, mul_zero, sub_zero] at this
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)

end API

section Neb

variable {M : ℕ} {k : ℤ}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.HasNebentypus ε g) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by
  funext τ
  rw [SL_slash_apply', hg γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hne := denom_SL_ne_zero γ τ
  have hk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k ≠ 0 := zpow_ne_zero k hne
  rw [zpow_neg]
  field_simp

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ)) :
    CuspForm.HasNebentypus ε g := by
  intro γ hγ τ
  have h := congrFun (hg γ hγ) τ
  rw [SL_slash_apply', Pi.smul_apply, smul_eq_mul] at h
  have hne := denom_SL_ne_zero γ τ
  have h2 : g (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod M) * g τ *
      (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k := by
    have := congrArg (fun z => z * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) h
    rwa [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [h2]
  ring

theorem changeLevel_apply_entry {R : ℕ} (hR : R ∣ M) (ε' : DirichletCharacter ℂ R)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    DirichletCharacter.changeLevel hR ε' ((γ 1 1 : ℤ) : ZMod M) = ε' ((γ 1 1 : ℤ) : ZMod R) := by
  have hu := isUnit_entry hγ
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' hR, hu.unit_spec,
    ZMod.cast_intCast hR]

theorem changeLevel_apply_prime {R : ℕ} [NeZero M] (hR : R ∣ M) (ε' : DirichletCharacter ℂ R)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    DirichletCharacter.changeLevel hR ε' (p : ZMod M) = ε' (p : ZMod R) := by
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hu : ((ZMod.unitOfCoprime p hcop : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) :=
    ZMod.coe_unitOfCoprime p hcop
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' hR, hu, ZMod.cast_natCast hR]

def IsOfType (M : ℕ) (k : ℤ) {R : ℕ} (ε' : DirichletCharacter ℂ R) (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
    F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε' ((γ 1 1 : ℤ) : ZMod R) • F

theorem isOfType_of_hasNebentypus [NeZero M] {R : ℕ} (hR : R ∣ M) (ε' : DirichletCharacter ℂ R)
    {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.HasNebentypus (DirichletCharacter.changeLevel hR ε') g) :
    IsOfType M k ε' (⇑g) := by
  intro γ hγ
  rw [slash_eq_smul_of_hasNebentypus hg hγ, changeLevel_apply_entry hR ε' hγ]

end Neb

section Datum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

theorem cast_q_mul_a : (q : ZMod W.R) * (W.a : ZMod W.R) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod W.R) W.bezout
  push_cast at this
  rwa [ZMod.natCast_self, zero_mul, sub_zero] at this

theorem not_dvd_b (hq : 1 < q) : ¬ (q : ℤ) ∣ W.b := by
  intro hdvd
  have h1 : (q : ℤ) ∣ 1 := by
    have h2 : (q : ℤ) ∣ (q : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_left _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

theorem not_dvd_R (hq : 1 < q) : ¬ (q : ℤ) ∣ (W.R : ℤ) := by
  intro hdvd
  have h1 : (q : ℤ) ∣ 1 := by
    have h2 : (q : ℤ) ∣ (q : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_right _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

theorem cast_qR_mul (x : ℤ) : (((q : ℤ) * (W.R : ℤ) * x : ℤ) : ZMod M) = 0 := by
  rw [← W.hM_int]
  push_cast
  simp

end Datum

section Reps

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] theorem repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] theorem repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

theorem repMat_unique {ℓ : ℕ} (hℓ : 1 < ℓ) {E : Matrix (Fin 2) (Fin 2) ℤ} {m m' : Option (Fin ℓ)}
    (h : repMat ℓ m' = E * repMat ℓ m) : m' = m := by
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

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

def traceRepMat : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => repMat q (some j)

@[scoped simp] theorem traceRepMat_none : traceRepMat W none = W.mat := rfl

@[scoped simp] theorem traceRepMat_some (j : Fin q) :
    traceRepMat W (some j) = !![1, (j : ℤ); 0, (q : ℤ)] := rfl

theorem traceRepMat_unique (hq : 1 < q) {E : Matrix (Fin 2) (Fin 2) ℤ}
    {i i' : Option (Fin q)} (h : traceRepMat W i' = E * traceRepMat W i) : i' = i := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>
      exfalso
      rw [traceRepMat_some, traceRepMat_none, AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * ((q : ℤ) * W.a) + E 0 1 * ((q : ℤ) * (W.R : ℤ)) :=
        congrFun (congrFun h 0) 0
      have hdvd : (q : ℤ) ∣ 1 :=
        ⟨E 0 0 * W.a + E 0 1 * (W.R : ℤ), by linear_combination h00⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases i' with
    | none =>
      exfalso
      rw [traceRepMat_some, traceRepMat_none, AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (q : ℤ) * W.a = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : W.b = E 0 0 * (j : ℤ) + E 0 1 * (q : ℤ) := congrFun (congrFun h 0) 1
      exact not_dvd_b W hq ⟨W.a * (j : ℤ) + E 0 1, by linear_combination h01 - (j : ℤ) * h00⟩
    | some j' =>
      exact repMat_unique hq h

end Reps

section TraceCocycle

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

theorem exists_fin_dvd_sub_mul (hq : q.Prime) {p : ℤ} (t : ℤ) (hp : ¬ (q : ℤ) ∣ p) :
    ∃ j' : Fin q, (q : ℤ) ∣ t - p * (j' : ℤ) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hcop : IsCoprime (q : ℤ) p :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hp
  obtain ⟨u, v, huv⟩ := hcop
  have hmod := Int.emod_add_mul_ediv (v * t) (q : ℤ)
  have hnonneg : 0 ≤ (v * t) % (q : ℤ) := Int.emod_nonneg _ hq0
  have hlt : (v * t) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqpos
  have hcoe : ((((v * t) % (q : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (q : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  refine ⟨⟨((v * t) % (q : ℤ)).toNat, by omega⟩,
    ⟨t * u + p * ((v * t) / (q : ℤ)), ?_⟩⟩
  show t - p * ((((v * t) % (q : ℤ)).toNat : ℕ) : ℤ) = (q : ℤ) * (t * u + p * ((v * t) / (q : ℤ)))
  rw [hcoe]
  linear_combination (-t) * huv + (-p) * hmod

theorem mat_mul_normalizes (α β c δ : ℤ)
    (hdet : α * δ - β * ((q : ℤ) * (W.R : ℤ) * c) = 1) :
    ∃ p r s t : ℤ, p * t - r * ((q : ℤ) * (W.R : ℤ) * s) = 1 ∧
      W.mat * !![α, β; (q : ℤ) * (W.R : ℤ) * c, δ]
        = !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] * W.mat ∧
      (t : ZMod W.R) = (δ : ZMod W.R) := by
  refine ⟨(q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
        - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ),
      -(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β + W.a * W.b * δ,
      α + (q : ℤ) * c - (W.R : ℤ) * β - δ,
      -((W.R : ℤ) * W.b) * (α + (q : ℤ) * c) + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ),
      ?_, ?_, ?_⟩
  · linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b) ^ 2 * hdet
      + ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout
  · rw [AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ) * c)
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * ((q : ℤ) * W.a)
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * W.b * c * (q : ℤ) + W.a * α * (q : ℤ))) * W.bezout
    · show (q : ℤ) * W.a * β + W.b * δ
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * W.b
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * (q : ℤ)
      linear_combination (-(W.a * β * (q : ℤ) + W.b * δ)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * α + (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * c)
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * ((q : ℤ) * W.a)
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * α * (q : ℤ) + (W.R : ℤ) * c * (q : ℤ) ^ 2)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * W.b
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * (q : ℤ)
      linear_combination (-((W.R : ℤ) * β * (q : ℤ) + δ * (q : ℤ))) * W.bezout
  · have h1 := cast_q_mul_a W
    push_cast
    rw [ZMod.natCast_self]
    linear_combination (δ : ZMod W.R) * h1

theorem exists_traceRep_cocycle (hq : q.Prime) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 W.R) (i : Option (Fin q)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧ ((δ 1 1 : ℤ) : ZMod W.R) = ((g 1 1 : ℤ) : ZMod W.R) ∧
      ∃ i' : Option (Fin q),
      traceRepMat W i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * traceRepMat W i' := by
  have hq1 : 1 < q := hq.one_lt
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
  have hqa := cast_q_mul_a W
  have hg11 : ((g 1 1 : ℤ) : ZMod W.R) = (d : ZMod W.R) := rfl
  cases i with
  | none =>
    by_cases hqc : (q : ℤ) ∣ c
    ·
      obtain ⟨c', rfl⟩ := hqc
      obtain ⟨p, r, s, t, hdet1, hmat, ht⟩ := mat_mul_normalizes W α β c' d
        (by linear_combination hdet')
      have hdetδ : Matrix.det !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination hdet1
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W s
      · rw [hg11, ← ht]; rfl
      · rw [traceRepMat_none, hgmat,
          show (W.R : ℤ) * ((q : ℤ) * c') = (q : ℤ) * (W.R : ℤ) * c' by ring]
        exact hmat
    ·
      have hqRc : ¬ (q : ℤ) ∣ (W.R : ℤ) * c :=
        fun hdvd => hqc ((Int.Prime.dvd_mul' hq hdvd).resolve_left (not_dvd_R W hq1))
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hq d hqRc
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![(W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α, -(W.a * α * (j' : ℤ)) + W.a * β + W.b * e;
             (q : ℤ) * (W.R : ℤ) * (α + c), -((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β
               + (q : ℤ) * e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b) * hdet' + W.bezout
          + ((W.R : ℤ) * α * W.b - W.a * α * (q : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W (α + c)
      · rw [hg11]
        show (((-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (q : ℤ) * e : ℤ)) : ZMod W.R) = _
        have he' := congrArg (Int.cast : ℤ → ZMod W.R) he
        push_cast at he' ⊢
        rw [ZMod.natCast_self] at he' ⊢
        linear_combination -he'
      · rw [traceRepMat_none, traceRepMat_some, hgmat]
        show W.mat * _ = _
        rw [AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (q : ℤ) * W.a * α + W.b * ((W.R : ℤ) * c)
            = ((W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α) * 1
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * 0
          ring
        · show (q : ℤ) * W.a * β + W.b * d
            = ((W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α) * (j' : ℤ)
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * (q : ℤ)
          linear_combination W.b * he
        · show (q : ℤ) * (W.R : ℤ) * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * (α + c) * 1
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (q : ℤ) * e) * 0
          ring
        · show (q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * (α + c) * (j' : ℤ)
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (q : ℤ) * e) * (q : ℤ)
          linear_combination (q : ℤ) * he
  | some j =>
    by_cases hpiv : (q : ℤ) ∣ (α + (j : ℤ) * ((W.R : ℤ) * c))
    ·
      obtain ⟨e, he⟩ := hpiv
      have hdetδ : Matrix.det
          !![-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e,
             W.a * β + W.a * d * (j : ℤ) - W.b * e;
             (q : ℤ) * (W.R : ℤ) * (c - d), -((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet'
          + (-((W.R : ℤ) * β * c) - (W.R : ℤ) * c * d * (j : ℤ) + d * e * (q : ℤ)) * W.bezout
          + (-d) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W (c - d)
      · rw [hg11]
        show (((-((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d : ℤ)) : ZMod W.R) = _
        push_cast
        rw [ZMod.natCast_self]
        linear_combination (d : ZMod W.R) * hqa
      · rw [traceRepMat_some, traceRepMat_none, hgmat]
        show _ = _ * W.mat
        rw [AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e) * ((q : ℤ) * W.a)
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * ((q : ℤ) * (W.R : ℤ))
          linear_combination he + (-((q : ℤ) * e)) * W.bezout
        · show 1 * β + (j : ℤ) * d
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e) * W.b
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * (q : ℤ)
          linear_combination (-(β + d * (j : ℤ))) * W.bezout
        · show 0 * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * (c - d) * ((q : ℤ) * W.a)
              + (-((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d) * ((q : ℤ) * (W.R : ℤ))
          linear_combination (-((q : ℤ) * (W.R : ℤ) * c)) * W.bezout
        · show 0 * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * (c - d) * W.b
              + (-((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d) * (q : ℤ)
          linear_combination (-((q : ℤ) * d)) * W.bezout
    ·
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hq (β + (j : ℤ) * d) hpiv
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![α + (j : ℤ) * ((W.R : ℤ) * c), e;
             (q : ℤ) * (W.R : ℤ) * c, d - (W.R : ℤ) * c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet' + ((W.R : ℤ) * c) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W c
      · rw [hg11]
        show (((d - (W.R : ℤ) * c * (j' : ℤ) : ℤ)) : ZMod W.R) = _
        push_cast
        rw [ZMod.natCast_self]
        ring
      · rw [traceRepMat_some, traceRepMat_some, hgmat]
        rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * 1 + e * 0
          ring
        · show 1 * β + (j : ℤ) * d
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * (j' : ℤ) + e * (q : ℤ)
          linear_combination he
        · show 0 * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * c * 1 + (d - (W.R : ℤ) * c * (j' : ℤ)) * 0
          ring
        · show 0 * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * c * (j' : ℤ) + (d - (W.R : ℤ) * c * (j' : ℤ)) * (q : ℤ)
          ring

end TraceCocycle

section HeckeCocycle

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

def wt {R : ℕ} (ε' : DirichletCharacter ℂ R) (ℓ : ℕ) : Option (Fin ℓ) → ℂ
  | none => ε' (ℓ : ZMod R)
  | some _ => 1

@[scoped simp] theorem wt_none {R : ℕ} (ε' : DirichletCharacter ℂ R) (ℓ : ℕ) :
    wt ε' ℓ none = ε' (ℓ : ZMod R) := rfl

@[scoped simp] theorem wt_some {R : ℕ} (ε' : DirichletCharacter ℂ R) (ℓ : ℕ) (j : Fin ℓ) :
    wt ε' ℓ (some j) = 1 := rfl

theorem exists_cocycle_hecke_al {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (ε' : DirichletCharacter ℂ W.R) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * W.mat = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (W.mat * repMat ℓ m) ∧
      wt ε' ℓ i * ε' ((δ 1 1 : ℤ) : ZMod W.R) = wt ε' ℓ m := by
  have hℓq : ¬ ℓ ∣ q := fun h => hℓM (W.hM ▸ h.mul_right W.R)
  have hℓR : ¬ ℓ ∣ W.R := fun h => hℓM (W.hM ▸ h.mul_left q)
  have hℓqZ : ¬ (ℓ : ℤ) ∣ (q : ℤ) := fun h => hℓq (Int.natCast_dvd_natCast.mp h)
  have hℓRZ : ¬ (ℓ : ℤ) ∣ (W.R : ℤ) := fun h => hℓR (Int.natCast_dvd_natCast.mp h)
  have hqa := cast_q_mul_a W
  cases i with
  | none =>
    obtain ⟨j', e, he⟩ := exists_fin_dvd_sub_mul hℓ (1 : ℤ) hℓRZ

    have hdetδ : Matrix.det
        !![W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1,
             -((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ));
           (q : ℤ) * (W.R : ℤ) * (1 - e),
             W.a * (q : ℤ) * e - (W.R : ℤ) * W.b] = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination
        ((W.R : ℤ) * W.a * (j' : ℤ) * (q : ℤ) + (W.R : ℤ) * (j' : ℤ)
            + W.a * e * (ℓ : ℤ) * (q : ℤ) - W.a * e * (q : ℤ) + e * (ℓ : ℤ)) * W.bezout
          + (-(W.R : ℤ) * W.b - 1) * he
    refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_, ?_⟩
    · rw [Gamma0_mem]; exact cast_qR_mul W (1 - e)
    · show repMat ℓ none * W.mat
        = !![W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1,
               -((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ));
             (q : ℤ) * (W.R : ℤ) * (1 - e),
               W.a * (q : ℤ) * e - (W.R : ℤ) * W.b] * (W.mat * repMat ℓ (some j'))
      rw [repMat_none, repMat_some, AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      refine Matrix.ext fun x y => ?_
      fin_cases x <;> fin_cases y
      · show ((ℓ : ℤ) * ((q : ℤ) * W.a) + 0 * ((q : ℤ) * (W.R : ℤ)) : ℤ)
          = (W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1)
                * ((q : ℤ) * W.a * 1 + W.b * 0)
            + (-((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ)))
                * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
        linear_combination (-(W.a * (q : ℤ) * ((ℓ : ℤ) - 1))) * W.bezout
      · show ((ℓ : ℤ) * W.b + 0 * (q : ℤ) : ℤ)
          = (W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1)
                * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
            + (-((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ)))
                * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
        linear_combination (W.a * (j' : ℤ) * (q : ℤ)) * W.bezout
      · show (0 * ((q : ℤ) * W.a) + 1 * ((q : ℤ) * (W.R : ℤ)) : ℤ)
          = (q : ℤ) * (W.R : ℤ) * (1 - e) * ((q : ℤ) * W.a * 1 + W.b * 0)
            + (W.a * (q : ℤ) * e - (W.R : ℤ) * W.b)
                * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
        linear_combination (-(W.R : ℤ) * (q : ℤ)) * W.bezout
      · show (0 * W.b + 1 * (q : ℤ) : ℤ)
          = (q : ℤ) * (W.R : ℤ) * (1 - e) * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
            + (W.a * (q : ℤ) * e - (W.R : ℤ) * W.b)
                * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
        linear_combination (-(q : ℤ) * ((W.R : ℤ) * (j' : ℤ) + e * (ℓ : ℤ))) * W.bezout
          + (q : ℤ) * he
    ·
      rw [wt_none, wt_some, ← map_mul]
      show ε' ((ℓ : ZMod W.R) * (((W.a * (q : ℤ) * e - (W.R : ℤ) * W.b : ℤ)) : ZMod W.R)) = 1
      have he' := congrArg (Int.cast : ℤ → ZMod W.R) he
      push_cast at he' ⊢
      rw [ZMod.natCast_self] at he' ⊢
      have : (ℓ : ZMod W.R) * ((W.a : ZMod W.R) * (q : ZMod W.R) * (e : ZMod W.R) - 0 * (W.b : ZMod W.R)) = 1 := by
        linear_combination (-((q : ZMod W.R) * (W.a : ZMod W.R))) * he' + hqa
      rw [this, map_one]
  | some j =>
    by_cases hdvd : (ℓ : ℤ) ∣ (W.a + (j : ℤ) * (W.R : ℤ))
    · obtain ⟨e, he⟩ := hdvd

      have hdetδ : Matrix.det
          !![(q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ),
               W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e;
             (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)),
               (ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination
          (-(W.R : ℤ) * W.b - (W.R : ℤ) * (j : ℤ) * (q : ℤ) + e * (ℓ : ℤ) * (q : ℤ) + 1)
              * W.bezout
            + (-(q : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_, ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W (1 - (ℓ : ℤ))
      · show repMat ℓ (some j) * W.mat
          = !![(q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ),
                 W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e;
               (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)),
                 (ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b] * (W.mat * repMat ℓ none)
        rw [repMat_some, repMat_none, AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * ((q : ℤ) * W.a) + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = ((q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ))
                  * ((q : ℤ) * W.a * (ℓ : ℤ) + W.b * 0)
              + (W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e)
                  * ((q : ℤ) * (W.R : ℤ) * (ℓ : ℤ) + (q : ℤ) * 0)
          linear_combination (-e * (ℓ : ℤ) * (q : ℤ)) * W.bezout + (q : ℤ) * he
        · show (1 * W.b + (j : ℤ) * (q : ℤ) : ℤ)
            = ((q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ))
                  * ((q : ℤ) * W.a * 0 + W.b * 1)
              + (W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e)
                  * ((q : ℤ) * (W.R : ℤ) * 0 + (q : ℤ) * 1)
          linear_combination (-W.b - (j : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * ((q : ℤ) * W.a) + (ℓ : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)) * ((q : ℤ) * W.a * (ℓ : ℤ) + W.b * 0)
              + ((ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (ℓ : ℤ) + (q : ℤ) * 0)
          linear_combination (-(W.R : ℤ) * (ℓ : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * W.b + (ℓ : ℤ) * (q : ℤ) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)) * ((q : ℤ) * W.a * 0 + W.b * 1)
              + ((ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 0 + (q : ℤ) * 1)
          linear_combination (-(ℓ : ℤ) * (q : ℤ)) * W.bezout
      ·
        rw [wt_none, wt_some, one_mul]
        show ε' ((((ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b : ℤ)) : ZMod W.R) = _
        congr 1
        push_cast
        rw [ZMod.natCast_self]
        linear_combination (ℓ : ZMod W.R) * hqa
    · have hpu : ¬ (ℓ : ℤ) ∣ (q : ℤ) * (W.a + (j : ℤ) * (W.R : ℤ)) := by
        intro h
        rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_mul.mp h with h' | h'
        · exact hℓqZ h'
        · exact hdvd h'
      obtain ⟨j', e, he⟩ := exists_fin_dvd_sub_mul hℓ (W.b + (j : ℤ) * (q : ℤ)) hpu

      have hdetδ : Matrix.det
          !![(q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e,
               W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b;
             (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1),
               (q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                 - (ℓ : ℤ) * (W.R : ℤ) * W.b] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination
          (-(W.R : ℤ) * e * (ℓ : ℤ) + (W.R : ℤ) * (j : ℤ) * (q : ℤ)
              - (W.R : ℤ) * (j' : ℤ) * (q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)
              + W.a * (q : ℤ) + 1) * W.bezout
            + (W.R : ℤ) * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_, ?_⟩
      · rw [Gamma0_mem]; exact cast_qR_mul W ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1)
      · show repMat ℓ (some j) * W.mat
          = !![(q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e,
                 W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b;
               (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1),
                 (q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                   - (ℓ : ℤ) * (W.R : ℤ) * W.b] * (W.mat * repMat ℓ (some j'))
        rw [repMat_some, repMat_some, AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * ((q : ℤ) * W.a) + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = ((q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e)
                  * ((q : ℤ) * W.a * 1 + W.b * 0)
              + (W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
          linear_combination (-(q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)) * W.bezout
        · show (1 * W.b + (j : ℤ) * (q : ℤ) : ℤ)
            = ((q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e)
                  * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
              + (W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
          linear_combination
            (-e * (ℓ : ℤ) - (j' : ℤ) * (q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)) * W.bezout + he
        · show (0 * ((q : ℤ) * W.a) + (ℓ : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1)
                  * ((q : ℤ) * W.a * 1 + W.b * 0)
              + ((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                  - (ℓ : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
          linear_combination (-(W.R : ℤ) * (ℓ : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * W.b + (ℓ : ℤ) * (q : ℤ) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1)
                  * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
              + ((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                  - (ℓ : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
          linear_combination (-(ℓ : ℤ) * (q : ℤ)) * W.bezout
      ·
        rw [wt_some, wt_some, one_mul]
        show ε' ((((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
            - (ℓ : ℤ) * (W.R : ℤ) * W.b : ℤ)) : ZMod W.R) = 1
        have : ((((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
            - (ℓ : ℤ) * (W.R : ℤ) * W.b : ℤ)) : ZMod W.R) = 1 := by
          push_cast
          rw [ZMod.natCast_self]
          linear_combination hqa
        rw [this, map_one]

end HeckeCocycle

section GLReps

variable {M q : ℕ} {k : ℤ}

theorem smul_slash_pos (k : ℤ) {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) (c : ℂ) (F : ℍ → ℂ) :
    (c • F) ∣[k] A = c • F ∣[k] A := by
  rw [ModularForm.smul_slash]
  congr 1
  rw [UpperHalfPlane.σ, if_pos hA]
  rfl

def repGL (ℓ : ℕ) : Option (Fin ℓ) → GL (Fin 2) ℝ
  | none => heckeDiagMatrix ℓ
  | some j => heckeMatrix ℓ j

@[scoped simp] theorem repGL_none (ℓ : ℕ) : repGL ℓ none = heckeDiagMatrix ℓ := rfl
@[scoped simp] theorem repGL_some (ℓ : ℕ) (j : Fin ℓ) : repGL ℓ (some j) = heckeMatrix ℓ j := rfl

theorem repGL_coe {ℓ : ℕ} (hℓ : ℓ ≠ 0) (i : Option (Fin ℓ)) :
    (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat ℓ i).map (algebraMap ℤ ℝ) := by
  cases i with
  | none =>
    rw [repGL_none, val_heckeDiagMatrix hℓ, repMat_none]
    ext x y; fin_cases x <;> fin_cases y <;> simp
  | some j =>
    rw [repGL_some, val_heckeMatrix hℓ, repMat_some]
    ext x y; fin_cases x <;> fin_cases y <;> simp

theorem det_repGL_pos (ℓ : ℕ) (i : Option (Fin ℓ)) : 0 < ((repGL ℓ i).det : ℝ) := by
  cases i with
  | none => exact det_heckeDiagMatrix_pos ℓ
  | some j => exact det_heckeMatrix_pos ℓ j

variable (W : AtkinLehnerDatum M q)

def traceRepGL [NeZero M] : Option (Fin q) → GL (Fin 2) ℝ
  | none => W.alGL
  | some j => heckeMatrix q j

@[scoped simp] theorem traceRepGL_none [NeZero M] : traceRepGL W none = W.alGL := rfl
@[scoped simp] theorem traceRepGL_some [NeZero M] (j : Fin q) : traceRepGL W (some j) = heckeMatrix q j :=
  rfl

theorem traceRepGL_coe [NeZero M] (i : Option (Fin q)) :
    (traceRepGL W i : Matrix (Fin 2) (Fin 2) ℝ) = (traceRepMat W i).map (algebraMap ℤ ℝ) := by
  cases i with
  | none => rw [traceRepGL_none, W.alGL_coe, traceRepMat_none]
  | some j =>
    rw [traceRepGL_some, val_heckeMatrix W.q_pos.ne', traceRepMat_some]
    ext x y; fin_cases x <;> fin_cases y <;> simp

def phi (k : ℤ) (p : ℕ) (c : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + c • (F ∣[k] heckeDiagMatrix p)

theorem phi_add (k : ℤ) (p : ℕ) (c : ℂ) (F G : ℍ → ℂ) :
    phi k p c (F + G) = phi k p c F + phi k p c G := by
  simp only [phi, heckeU_add, SlashAction.add_slash, smul_add]
  abel

theorem phi_smul (k : ℤ) (p : ℕ) (c a : ℂ) (F : ℍ → ℂ) :
    phi k p c (a • F) = a • phi k p c F := by
  rw [phi, phi, heckeU_smul, smul_slash_pos k (det_heckeDiagMatrix_pos p), smul_comm, smul_add]

theorem phi_eq_sum {R : ℕ} (ε' : DirichletCharacter ℂ R) (ℓ : ℕ) (F : ℍ → ℂ) :
    phi k ℓ (ε' (ℓ : ZMod R)) F = ∑ i : Option (Fin ℓ), wt ε' ℓ i • (F ∣[k] repGL ℓ i) := by
  rw [Fintype.sum_option, phi, heckeU_def, Finset.sum_range, add_comm]
  simp

theorem trace_eq_sum [NeZero M] (F : ℍ → ℂ) :
    alSlash W k F + heckeU k q F = ∑ i : Option (Fin q), F ∣[k] traceRepGL W i := by
  rw [Fintype.sum_option, alSlash_def, heckeU_def, Finset.sum_range]
  simp

end GLReps

section Commute

variable {M q : ℕ} {k : ℤ} [NeZero M] (W : AtkinLehnerDatum M q)

theorem alSlash_phi {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (ε' : DirichletCharacter ℂ W.R)
    {F : ℍ → ℂ} (hF : IsOfType M k ε' F) :
    alSlash W k (phi k p (ε' (p : ZMod W.R)) F) = phi k p (ε' (p : ZMod W.R)) (alSlash W k F) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  choose δ hδ m hm hwt using exists_cocycle_hecke_al W hp hpM ε'

  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have hδ₁ : (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁
    have hWm : W.mat * repMat p (m i₂)
        = (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (repMat p i₁ * W.mat) := by
      rw [h₁, ← mul_assoc, hδ₁, one_mul]
    have hcomb : repMat p i₂ * W.mat
        = ((δ i₂ * (δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat p i₁ * W.mat := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      calc repMat p i₂ * W.mat
          = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ) * (W.mat * repMat p (m i₂)) := h₂
        _ = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ)
              * ((((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
                  * (repMat p i₁ * W.mat)) := by rw [hWm]
        _ = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ)
              * (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat p i₁ * W.mat := by
            simp only [mul_assoc]
    have hadj := congrArg (· * W.mat.adjugate) hcomb
    simp only [mul_assoc, Matrix.mul_adjugate, AtkinLehnerDatum.det_mat, Matrix.mul_smul,
      mul_one] at hadj
    have hXY : repMat p i₂
        = ((δ i₂ * (δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat p i₁ := by
      refine Matrix.ext fun x y => mul_left_cancel₀ hq0 ?_
      have hxy := congrFun (congrFun hadj x) y
      simpa [Matrix.smul_apply, smul_eq_mul, mul_assoc] using hxy
    exact (repMat_unique hp.one_lt hXY).symm
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, repGL p i * W.alGL
      = Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * (W.alGL * repGL p (m i)) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, repGL_coe hp.ne_zero,
      repGL_coe hp.ne_zero, W.alGL_coe, mapGL_coe_eq, ← map_int_mul, ← map_int_mul,
      ← map_int_mul, hm i]

  set e := ε' (p : ZMod W.R) with he
  calc alSlash W k (phi k p e F)
      = ∑ i : Option (Fin p), wt ε' p i • ((F ∣[k] repGL p i) ∣[k] W.alGL) := by
        rw [he, phi_eq_sum, alSlash_def, SlashAction.sum_slash]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_slash_pos k W.det_alGL_pos]
    _ = ∑ i : Option (Fin p), wt ε' p i •
          (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * (W.alGL * repGL p (m i)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← SlashAction.slash_mul, hmGL i]
    _ = ∑ i : Option (Fin p), (wt ε' p i * ε' ((δ i 1 1 : ℤ) : ZMod W.R)) •
          ((F ∣[k] W.alGL) ∣[k] repGL p (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [SlashAction.slash_mul, SlashAction.slash_mul, hF (δ i) (hδ i),
          smul_slash_pos k W.det_alGL_pos, smul_slash_pos k (det_repGL_pos p _), smul_smul]
    _ = ∑ i : Option (Fin p), wt ε' p (m i) • ((F ∣[k] W.alGL) ∣[k] repGL p (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hwt i]
    _ = ∑ i : Option (Fin p), wt ε' p i • ((F ∣[k] W.alGL) ∣[k] repGL p i) :=
        hbij.sum_comp fun i => wt ε' p i • ((F ∣[k] W.alGL) ∣[k] repGL p i)
    _ = phi k p e (alSlash W k F) := by rw [he, phi_eq_sum, alSlash_def]

end Commute

section Trace

variable {M q : ℕ} {k : ℤ} [NeZero M] (W : AtkinLehnerDatum M q)

theorem trace_slash (hq : q.Prime) (ε' : DirichletCharacter ℂ W.R) {F : ℍ → ℂ}
    (hF : IsOfType M k ε' F) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 W.R) :
    (alSlash W k F + heckeU k q F) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε' ((γ 1 1 : ℤ) : ZMod W.R) • (alSlash W k F + heckeU k q F) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  choose δ hδ hd m hm using exists_traceRep_cocycle W hq hγ

  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁
    have hg_inv : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hδ₂ : (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcomb : traceRepMat W i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * traceRepMat W i₂ := by
      have step : traceRepMat W i₁ * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (traceRepMat W i₂ * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc traceRepMat W i₁ * (γ : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * traceRepMat W (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                    traceRepMat W (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (traceRepMat W i₂ * (γ : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (traceRepMat W i₂ * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact traceRepMat_unique W hq.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, traceRepGL W i * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * traceRepGL W (m i) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, traceRepGL_coe, traceRepGL_coe, mapGL_coe_eq,
      mapGL_coe_eq, ← map_int_mul, ← map_int_mul, hm i]
  have hdetT : ∀ i, 0 < ((traceRepGL W i).det : ℝ) := by
    intro i; cases i with
    | none => exact W.det_alGL_pos
    | some j => exact det_heckeMatrix_pos q j
  rw [trace_eq_sum W F, SlashAction.sum_slash]
  calc ∑ i : Option (Fin q),
        (F ∣[k] traceRepGL W i) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ∑ i : Option (Fin q),
          F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * traceRepGL W (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← SlashAction.slash_mul, hmGL i]
    _ = ∑ i : Option (Fin q), ε' ((γ 1 1 : ℤ) : ZMod W.R) • (F ∣[k] traceRepGL W (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [SlashAction.slash_mul, hF (δ i) (hδ i), smul_slash_pos k (hdetT _), hd i]
    _ = ∑ i : Option (Fin q), ε' ((γ 1 1 : ℤ) : ZMod W.R) • (F ∣[k] traceRepGL W i) :=
        hbij.sum_comp fun i => ε' ((γ 1 1 : ℤ) : ZMod W.R) • (F ∣[k] traceRepGL W i)
    _ = ε' ((γ 1 1 : ℤ) : ZMod W.R) • ∑ i : Option (Fin q), F ∣[k] traceRepGL W i := by
        rw [Finset.smul_sum]

end Trace

section Square

variable {M q : ℕ} {k : ℤ} (W : AtkinLehnerDatum M q)

def scalarGL (q : ℕ) (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] theorem scalarGL_coe (hq : 0 < q) :
    (scalarGL q hq : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

theorem val_det_scalarGL (hq : 0 < q) : ((scalarGL q hq).det : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]
  ring

theorem det_scalarGL_pos (hq : 0 < q) : 0 < ((scalarGL q hq).det : ℝ) := by
  rw [val_det_scalarGL]
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  positivity

theorem scalarGL_smul (hq : 0 < q) (τ : ℍ) : scalarGL q hq • τ = τ := by
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hq.ne' : ((q : ℝ)) ≠ 0)
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_scalarGL_pos hq)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, scalarGL_coe, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, add_zero, zero_mul, zero_add]
  rw [mul_div_cancel_left₀ _ hqC]

theorem slash_scalarGL (k : ℤ) (hq : 0 < q) (f : ℍ → ℂ) :
    f ∣[k] scalarGL q hq = ((q : ℂ) ^ (k - 2)) • f := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL q hq) (f (scalarGL q hq • τ)) = f (scalarGL q hq • τ) := by
    rw [UpperHalfPlane.σ, if_pos (det_scalarGL_pos hq)]
    rfl
  have hden : denom (scalarGL q hq) τ = (q : ℝ) := by
    simp [UpperHalfPlane.denom, scalarGL_coe]
  rw [hσ, scalarGL_smul, val_det_scalarGL, hden,
    abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℕ) := by push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← zpow_natCast ((q : ℂ)) 2, ← zpow_mul, mul_assoc, ← zpow_add₀ hqC]
  rw [show (2 : ℕ) * (k - 1) + -k = k - 2 by push_cast; ring]
  ring

theorem alGL_mul_alGL [NeZero M] :
    W.alGL * W.alGL = scalarGL q W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, W.alGL_coe, scalarGL_coe, mapGL_coe_eq,
    AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul, W.mat_sq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, AtkinLehnerDatum.sqUnit]

theorem alSlash_alSlash [NeZero M] (ε' : DirichletCharacter ℂ W.R) {F : ℍ → ℂ}
    (hF : IsOfType M k ε' F) :
    alSlash W k (alSlash W k F) = (ε' (q : ZMod W.R) * (q : ℂ) ^ (k - 2)) • F := by
  have hFu : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) = ε' (q : ZMod W.R) • F := by
    rw [hF _ W.sqUnitSL_mem]
    congr 2
    show (((W.sqUnit 1 1 : ℤ)) : ZMod W.R) = _
    have : W.sqUnit 1 1 = (W.R : ℤ) * W.b + (q : ℤ) := by rw [AtkinLehnerDatum.sqUnit]; simp
    rw [this]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  calc alSlash W k (alSlash W k F)
      = F ∣[k] (W.alGL * W.alGL) := by
        rw [alSlash_def, alSlash_def, SlashAction.slash_mul]
    _ = (F ∣[k] scalarGL q W.q_pos) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [alGL_mul_alGL, SlashAction.slash_mul]
    _ = ((q : ℂ) ^ (k - 2)) • (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL)) := by
        rw [slash_scalarGL, smul_slash_pos k (by simp)]
    _ = (ε' (q : ZMod W.R) * (q : ℂ) ^ (k - 2)) • F := by rw [hFu, smul_smul, mul_comm]

end Square

section TraceForm

variable {M q : ℕ} {k : ℤ} [NeZero M] (W : AtkinLehnerDatum M q)

scoped instance neZero_R : NeZero W.R := ⟨W.R_pos.ne'⟩

def trForm (hq : q.Prime) (ε' : DirichletCharacter ℂ W.R) (g : CuspForm (Γ₁ℝ M) k)
    (hg : IsOfType M k ε' (⇑g)) : CuspForm (Γ₁ℝ W.R) k where
  toFun := alSlash W k ⇑g + heckeU k q ⇑g
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have hγ0 : γ ∈ Gamma0 W.R := by
      rw [Gamma0_mem]; exact (Gamma1_mem _ _ |>.mp hγ).2.2
    have hd : ((γ 1 1 : ℤ) : ZMod W.R) = 1 := (Gamma1_mem _ _ |>.mp hγ).2.1
    rw [trace_slash W hq ε' hg hγ0, hd, map_one, one_smul]
  holo' := (ModularForm.mdifferentiable_alSlash W k g.holo').add
    (ModularForm.mdifferentiable_heckeU g.holo' k q)
  zero_at_cusps' := by
    intro c hc
    have hcM1 : IsCusp c (Γ₁ℝ M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢; exact hc
    have hcM0 : IsCusp c (Γ₀ℝ M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢; exact hc
    refine OnePoint.IsZeroAt.add ?_ (CuspFormClass.isZeroAt_heckeU g q hcM1)
    refine ModularForm.isZeroAt_alSlash W k (fun c' hc' => ?_) hcM0
    refine CuspFormClass.zero_at_cusps g ?_
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc' ⊢
    exact hc'

theorem hasNebentypus_trForm (hq : q.Prime) (ε' : DirichletCharacter ℂ W.R)
    (g : CuspForm (Γ₁ℝ M) k) (hg : IsOfType M k ε' (⇑g)) :
    CuspForm.HasNebentypus ε' (trForm W hq ε' g hg) :=
  hasNebentypus_of_slash_eq_smul fun _ hγ => trace_slash W hq ε' hg hγ

end TraceForm

section Phi

variable {L : ℕ} {k : ℤ} {p : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N :=
  pow_mem (T_mem_Gamma1 N) n

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hF.slash k (by simp [val_heckeMatrix hp])).add ih

theorem periodic_add_smul {F G : ℍ → ℂ} (hF : Periodic (F ∘ ofComplex) 1)
    (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((F + c • G) ∘ ofComplex) 1 := by
  intro w
  have h1 := hF w
  have h2 := hG w
  simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

variable (F : CuspForm (Γ₁ℝ L) k)

theorem cusp_slash_T_pow (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 L n))

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 :=
  periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) := ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularFormClass.bdd_at_infty F

theorem qCoeff_smul (c : ℂ) (n : ℕ) : qCoeff (c • (⇑F : ℍ → ℂ)) n = c * qCoeff (⇑F) n := by
  have hang := analyticAt_cuspFunction_zero one_pos (cusp_periodic F) F.holo' (cusp_bdd F)
  rw [qCoeff, qCoeff, qExpansion_smul hang, map_smul, smul_eq_mul]

theorem phi_props (hp : p ≠ 0) (c : ℂ) :
    Periodic (phi k p c ⇑F ∘ ofComplex) 1 ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (phi k p c ⇑F) ∧
    IsBoundedAtImInfty (phi k p c ⇑F) ∧
    ∀ n : ℕ, qCoeff (phi k p c ⇑F) n =
      qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  set U : ℍ → ℂ := heckeU k p (⇑F) with hU
  set D : ℍ → ℂ := (⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  have hUper : Periodic (U ∘ ofComplex) 1 := ModularForm.periodic_heckeU_comp_ofComplex hFper k p
  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp (cusp_slash_T_pow F p)
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    ModularForm.mdifferentiable_heckeU hFhol k p
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hFhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp hFbdd
  have hDbdd : IsBoundedAtImInfty D := hFbdd.slash k (by simp [val_heckeDiagMatrix hp])
  have hφ : phi k p c ⇑F = U + c • D := rfl
  refine ⟨hφ ▸ periodic_add_smul hUper hDper c, hφ ▸ hUhol.add (hDhol.const_smul c),
    hφ ▸ hUbdd.add (hDbdd.smul c), fun n => ?_⟩
  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hancD : AnalyticAt ℂ (cuspFunction 1 (c • D)) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_smul hDper c) (hDhol.const_smul c) (hDbdd.smul c)
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  set G : ℍ → ℂ := fun τ => F (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : qCoeff D n = (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
    rw [qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hFper hFhol hFbdd hp n
  have hqU : qCoeff U n = qCoeff (⇑F) (p * n) := by
    rw [hU, UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hp n, coeffHeckeU_apply, mul_comm]
  rw [hφ, qCoeff, qExpansion_add hanU hancD, qExpansion_smul hanD, map_add, map_smul, smul_eq_mul]
  have h1 := hqU
  have h2 := hqD
  simp only [qCoeff] at h1 h2 ⊢
  rw [h1, h2, mul_assoc]

theorem phi_eq_smul_of_qCoeff (hp : p ≠ 0) (c lam : ℂ)
    (hrel : ∀ n : ℕ, qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = lam * qCoeff (⇑F) n) :
    phi k p c ⇑F = lam • (⇑F : ℍ → ℂ) := by
  obtain ⟨hper, hhol, hbdd, hq⟩ := phi_props F hp c
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq hper hhol hbdd (periodic_smul (cusp_periodic F) lam)
    (hFhol.const_smul lam) ((cusp_bdd F).smul lam) (fun n => ?_)
  rw [hq n, hrel n, qCoeff_smul]

theorem qCoeff_of_phi_eq_smul (hp : p ≠ 0) (c μ : ℂ) (hfun : phi k p c ⇑F = μ • (⇑F : ℍ → ℂ))
    (n : ℕ) :
    qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = μ * qCoeff (⇑F) n := by
  obtain ⟨-, -, -, hq⟩ := phi_props F hp c
  rw [← hq n, hfun, qCoeff_smul]

theorem heckeU_eq_smul_of_qCoeff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (a : ℂ)
    (ha : ∀ n : ℕ, qCoeff (⇑F) (ℓ * n) = a * qCoeff (⇑F) n) :
    heckeU k ℓ ⇑F = a • (⇑F : ℍ → ℂ) := by
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq (ModularForm.periodic_heckeU_comp_ofComplex hFper k ℓ)
    (ModularForm.mdifferentiable_heckeU hFhol k ℓ) (isBoundedAtImInfty_heckeU hℓ hFbdd)
    (periodic_smul hFper a) (hFhol.const_smul a) (hFbdd.smul a) (fun n => ?_)
  rw [UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hℓ n, coeffHeckeU_apply, mul_comm n ℓ, ha n,
    qCoeff_smul]

end Phi

section Main

variable {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ}

def datum (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) : AtkinLehnerDatum M p :=
  have hcop : Nat.Coprime p (M / p) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hp2 ?_
    rw [sq]
    exact Nat.mul_dvd_of_dvd_div hpM h
  have hint : IsCoprime (p : ℤ) ((M / p : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  { R := M / p
    hM := (Nat.mul_div_cancel' hpM).symm
    a := Classical.choose hint
    b := -Classical.choose (Classical.choose_spec hint)
    bezout := by
      have h := Classical.choose_spec (Classical.choose_spec hint)
      linear_combination h }

theorem main (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (Γ₁ℝ M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, qCoeff (⇑f) (p * n) = qCoeff (⇑f) p * qCoeff (⇑f) n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        qCoeff (⇑f) (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then qCoeff (⇑f) (n / ℓ) else 0) =
          qCoeff (⇑f) ℓ * qCoeff (⇑f) n) :
    qCoeff (⇑f) p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (Γ₁ℝ (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        qCoeff (⇑g) (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then qCoeff (⇑g) (n / ℓ) else 0) =
          qCoeff (⇑f) ℓ * qCoeff (⇑g) n := by
  set W : AtkinLehnerDatum M p := datum hp hpM hp2 with hW
  have hp0 : p ≠ 0 := hp.ne_zero

  have hF : IsOfType M k ε' (⇑f) := isOfType_of_hasNebentypus (Nat.div_dvd_of_dvd hpM) ε' hε
  have hFW : IsOfType M k (show DirichletCharacter ℂ W.R from ε') (⇑f) := hF

  set ap : ℂ := qCoeff (⇑f) p with hap
  have hUf : heckeU k p ⇑f = ap • (⇑f : ℍ → ℂ) := heckeU_eq_smul_of_qCoeff f hp0 ap hU

  set g : CuspForm (Γ₁ℝ (M / p)) k := trForm W hp ε' f hFW with hg
  have hcoe : (⇑g : ℍ → ℂ) = alSlash W k ⇑f + heckeU k p ⇑f := rfl
  have hneb : CuspForm.HasNebentypus ε' g := hasNebentypus_trForm W hp ε' f hFW

  have hTg : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑g = qCoeff (⇑f) ℓ • (⇑g : ℍ → ℂ) := by
    intro ℓ hℓ hℓM
    have hΦf : phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑f = qCoeff (⇑f) ℓ • (⇑f : ℍ → ℂ) :=
      phi_eq_smul_of_qCoeff f hℓ.ne_zero _ _ (hT ℓ hℓ hℓM)
    have hΦW : alSlash W k (phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑f)
        = phi k ℓ (ε' (ℓ : ZMod (M / p))) (alSlash W k ⇑f) := alSlash_phi W hℓ hℓM ε' hFW
    rw [hcoe, phi_add, ← hΦW, hΦf, alSlash_smul, hUf, phi_smul, hΦf, smul_add, smul_comm]
  by_cases hg0 : g = 0
  ·
    left
    have hh0 : (⇑g : ℍ → ℂ) = 0 := by rw [hg0]; rfl
    have hWf : alSlash W k ⇑f = (-ap) • (⇑f : ℍ → ℂ) := by
      have := hh0
      rw [hcoe, hUf] at this
      exact (eq_neg_of_add_eq_zero_left this).trans (neg_smul ap _).symm
    have hsq : (ap * ap) • (⇑f : ℍ → ℂ) = (ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) := by
      have h2 : alSlash W k (alSlash W k ⇑f) = (ap * ap) • (⇑f : ℍ → ℂ) := by
        rw [hWf, alSlash_smul, hWf, smul_smul, neg_mul_neg]
      rw [← h2]
      exact alSlash_alSlash W ε' hFW
    have hf0' : (⇑f : ℍ → ℂ) ≠ 0 := fun h0 => hf0 (DFunLike.ext' (by rw [h0]; rfl))
    obtain ⟨τ, hτ⟩ : ∃ τ, f τ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf0' (funext hall)
    have := congrFun hsq τ
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [sq]
    exact mul_right_cancel₀ hτ this
  ·
    right
    refine ⟨g, hg0, hneb, fun ℓ hℓ hℓM n => ?_⟩
    exact qCoeff_of_phi_eq_smul g hℓ.ne_zero _ _ (hTg ℓ hℓ hℓM) n

end Main

end ALDich
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.ALDich"

end
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.ALDich"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, ModularFormClass.qCoeff f (p * n) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ModularFormClass.qCoeff f p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff g (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff g n :=
  ALDich.main M k hp hpM hp2 ε' f hf0 hε hU hT

end S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
end P2MW
export P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd (solution)
