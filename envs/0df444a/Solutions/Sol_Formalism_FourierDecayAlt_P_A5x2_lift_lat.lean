-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.lift_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:20.779801+00:00
-- url     : https://prove2.me/submissions/df5ba724-f1ab-4349-b348-7716395a54ca

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_add_single_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_smul_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_liftRel_sub_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (hv : LiftRel R c.val Z Z' φ v v')
    (hl : v ∈ latZ R (Z + vecMulVec (coeLin R m) (Pi.single c 1))) :
    v' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by
  rw [mem_latZ] at hl ⊢
  obtain ⟨y, hy⟩ := hl
  rw [add_single_mulVec] at hy
  have hw := liftRel_sub_smul hv hm (y c)
  have e1 : coeLin R (v - y c • m) = Z *ᵥ coeLin R y := by
    rw [map_sub, map_smul, ← hy, smul_coe, coeLin_apply]; abel
  have hmk : (Submodule.Quotient.mk (v - y c • m) : coker R Z) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_latZ]; exact ⟨y, e1.symm⟩
  have h0 : (Submodule.Quotient.mk (v' - y c • m') : coker R Z') = 0 := by
    rw [← hw.1, hmk, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, mem_latZ] at h0
  obtain ⟨y', hy'⟩ := h0
  have e2 := hw.2 c.val le_rfl
  rw [lamTil_fin, lamTil_fin, e1, ← hy', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd',
    Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec] at e2
  refine ⟨y', ?_⟩
  rw [add_single_mulVec, hy', e2, map_sub, map_smul, smul_coe, coeLin_apply]; abel
end Formalism.FourierDecayAlt.P.A5x2
