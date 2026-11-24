-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.cnt_bad_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:59.425911+00:00
-- url     : https://prove2.me/submissions/a0f892d4-459b-4a1d-8824-6d2e7cf93684

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lower_right_block_is_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_exists_latZ_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lamTil_k_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_Lam_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_msk_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_det_mul
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_latZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_triple_form_recursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det)
    (p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (hp' : IsPP R k p')
    (hZ : IsInt R (Z₀ * p)) (hfin : Finite (coker R (Z₀ * p)))
    (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀')
    (hC : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
    (hT : InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ) (D : Matrix (Fin n) (Fin n) K)
    (hL : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      abelian₂ R k Z₀' y = D *ᵥ abelian₂ R k Z₀ x) :
    ¬ InTT R k (Z₀ * p) (Z₀' * p') φ ↔
      ∃ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
        abelian₂ R k Z₀ x = 0 ∧ lamTil R Z₀' k y - lamTil R Z₀ k x ∉ R := by
  have hdZ := cnt_det_mul R k Z₀ p hd hp
  have hdZ' := cnt_det_mul R k Z₀' p' hd' hp'
  have hstep := Formalism.FourierDecayAlt.P.triple_form_recursion K R ψ hsd n (Z₀ * p) (Z₀' * p') hdZ hdZ' hfin φ k
    (by omega) hT
  rw [hstep]
  constructor
  · intro h
    push Not at h
    obtain ⟨v, v', hv, hker, hne⟩ := h
    have hint : ∀ j, abelian₂ R k (Z₀ * p) v j ∈ R := by
      intro j
      rw [cnt_Lam_coord]
      split_ifs with hj
      · exact (A5x3.mk_eq_zero R _).1 (hker j.val hj)
      · exact R.zero_mem
    have hint0 : ∀ j, abelian₂ R k Z₀ v j ∈ R := by
      rw [Lam_mul' R k Z₀ p hp v]
      exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.1) hint
    obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀ p hd hp hZ _ hint0 (cnt_msk_Lam R k Z₀ v)
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk (v - z)))
    have hx0 : abelian₂ R k Z₀ (v - z) = 0 := by rw [map_sub, hzL, sub_self]
    have hy0 : abelian₂ R k Z₀' y = 0 := by rw [hL _ _ hy.symm, hx0, Matrix.mulVec_zero]
    refine ⟨v - z, y, hy.symm, hx0, ?_⟩
    intro hmem
    apply hne
    have e1 : φ (Submodule.Quotient.mk (v - z)) = Submodule.Quotient.mk y := hC _ _ hy.symm
    have e2 : (Submodule.Quotient.mk (v - z) : coker R (Z₀ * p)) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hz, sub_zero]
    rw [e2, hv] at e1
    have e3 : v' - y ∈ latZ R (Z₀' * p') := (Submodule.Quotient.eq _).1 e1
    have e4 : lamN R (Z₀' * p') k v' = lamN R (Z₀' * p') k y := by
      have := A5x2.lamN_latZ R _ hdZ' k e3
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    have e5 : lamN R (Z₀ * p) k v = lamN R (Z₀ * p) k (v - z) := by
      have := A5x2.lamN_latZ R _ hdZ k hz
      rw [LinearMap.mem_ker] at this
      rw [map_sub, this, sub_zero]
    rw [e4, e5]
    show (Submodule.Quotient.mk (lamTil R (Z₀' * p') k y) : KR R) =
      Submodule.Quotient.mk (lamTil R (Z₀ * p) k (v - z))
    rw [lamTil_k_mul R k Z₀' p' hp' y hy0, lamTil_k_mul R k Z₀ p hp _ hx0]
    exact (A5x3.mk_eq_mk R _ _).2 hmem
  · rintro ⟨x, y, hxy, hx0, hnot⟩ h
    apply hnot
    have hy0 : abelian₂ R k Z₀' y = 0 := by rw [hL _ _ hxy, hx0, Matrix.mulVec_zero]
    have hker : ∀ j, k < j → lamN R (Z₀ * p) j x = 0 := by
      intro j hj
      by_cases hjn : j < n
      · have h1 : abelian₂ R k (Z₀ * p) x = 0 := by
          rw [Lam_mul R k Z₀ p hp, hx0, Matrix.mulVec_zero]
        have h2 := congrFun h1 ⟨j, hjn⟩
        rw [cnt_Lam_coord, if_pos hj] at h2
        show (Submodule.Quotient.mk (lamTil R (Z₀ * p) j x) : KR R) = 0
        rw [(A5x3.mk_eq_zero R _)]
        simp only at h2
        rw [h2]; exact R.zero_mem
      · rw [A5x2.lamN_big R _ j (by omega)]; rfl
    have h3 : (Submodule.Quotient.mk (lamTil R (Z₀' * p') k y) : KR R) =
        Submodule.Quotient.mk (lamTil R (Z₀ * p) k x) := h x y (hC _ _ hxy) hker
    rw [lamTil_k_mul R k Z₀' p' hp' y hy0, lamTil_k_mul R k Z₀ p hp _ hx0] at h3
    exact (A5x3.mk_eq_mk R _ _).1 h3
end Formalism.FourierDecayAlt.P.A5x9
