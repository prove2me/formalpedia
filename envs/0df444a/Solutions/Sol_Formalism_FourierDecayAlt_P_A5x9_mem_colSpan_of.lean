-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.mem_colSpan_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:56.453811+00:00
-- url     : https://prove2.me/submissions/e6ffdcec-0cea-4570-9de4-158017e1aaf1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_colSpan_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_det_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_Lam_mulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (x : Fin n → R) (hx : x ∈ latZ R (Z₀ * p)) (h0 : abelian₂ R k Z₀ x = 0) : x ∈ colSpan R k Z₀ := by
  obtain ⟨t, e⟩ := (mem_latZ R _ x).1 hx
  have h1 : abelian₂ R k (Z₀ * p) x = 0 := by rw [Lam_mul R k Z₀ p hp, h0, Matrix.mulVec_zero]
  rw [mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) x t e] at h1
  rw [← colSpan_mul R k Z₀ p hp, mem_colSpan]
  refine ⟨t, fun j hj => ?_, e⟩
  have h2 := congrFun h1 j
  simp only [msk, if_pos hj, Pi.zero_apply, coeLin_apply] at h2
  exact Subtype.ext h2
end Formalism.FourierDecayAlt.P.A5x9
