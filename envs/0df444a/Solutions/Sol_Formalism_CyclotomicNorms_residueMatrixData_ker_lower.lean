-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.ker_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:19.779864+00:00
-- url     : https://prove2.me/submissions/599c6545-5a8a-4e1e-8cbf-ef026289af80

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_ge
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_linIndep
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_mul_eq_inv_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hk : ∀ i, k i ≤ n) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    ∑ i, k i ≤ Module.finrank K' ↥(LinearMap.ker (Matrix.toLin' Φ)) := by
  classical
  let f : ∀ i, Fin (k i) → Fin n := fun i j => ⟨n - 1 - j, by have := hk i; have := j.2; omega⟩
  let v : ∀ i, Fin (k i) → TruncK K' n := fun i => (fun l : Fin n => (TT) ^ (l : ℕ)) ∘ f i
  have hv : ∀ i, LinearIndependent K' (v i) := by
    intro i
    have hinj : Function.Injective (f i) := by
      intro j j' hjj
      simp only [f, Fin.mk.injEq] at hjj
      have := hk i
      have := j.2
      have := j'.2
      ext; omega
    exact tt_linIndep.comp (f i) hinj
  have hS := Pi.linearIndependent_single v hv
  have hmem : ∀ s : (Σ i, Fin (k i)),
      Q *ᵥ Pi.single s.1 (v s.1 s.2) ∈ LinearMap.ker (Matrix.toLin' Φ) := by
    rintro ⟨i, j⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, mul_eq_inv_mul Φ P Q hP, hD,
      ← mulVec_mulVec]
    have h0 : diagonal (fun i => (TT) ^ k i) *ᵥ Pi.single (M := fun _ => TruncK K' n) i (v i j) = 0 := by
      funext l
      rw [mulVec_diagonal]
      by_cases hl : l = i
      · subst hl
        simp only [Pi.single_eq_same, v, f, Function.comp_apply, Pi.zero_apply]
        rw [← pow_add]
        exact tt_pow_ge (by have := j.2; omega)
      · simp [hl]
    rw [h0, mulVec_zero]
  have hker : LinearMap.ker ((Matrix.toLin' Q).restrictScalars K') = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z1 z2 hz
    simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at hz
    have := congrArg (fun z => Q⁻¹ *ᵥ z) hz
    simpa only [mulVec_mulVec, nonsing_inv_mul _ hQ, one_mulVec] using this
  have hw : LinearIndependent K' (fun s : (Σ i, Fin (k i)) => Q *ᵥ Pi.single s.1 (v s.1 s.2)) :=
    hS.map' ((Matrix.toLin' Q).restrictScalars K') hker
  have hw' : LinearIndependent K' (fun s : (Σ i, Fin (k i)) =>
      (⟨_, hmem s⟩ : ↥(LinearMap.ker (Matrix.toLin' Φ)))) :=
    LinearIndependent.of_comp ((LinearMap.ker (Matrix.toLin' Φ)).subtype.restrictScalars K') hw
  have := hw'.fintype_card_le_finrank
  simpa [Fintype.card_sigma, Fintype.card_fin] using this
end Formalism.CyclotomicNorms.residueMatrixData
