-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.colSpan_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:26.245443+00:00
-- url     : https://prove2.me/submissions/e062f9c8-a1f6-4428-b7cd-df78038d98c8

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) :
    colSpan R k (Z₀ * p) = colSpan R k Z₀ := by
  ext x
  rw [mem_colSpan, mem_colSpan]
  constructor
  · rintro ⟨t, ht, e⟩
    obtain ⟨s, hs, es⟩ := mat_low R k hp.1 t ht
    exact ⟨s, hs, by rw [es, Matrix.mulVec_mulVec]; exact e⟩
  · rintro ⟨t, ht, e⟩
    obtain ⟨s, hs, es⟩ := mat_low R k hp.2 t ht
    refine ⟨s, hs, ?_⟩
    rw [es, Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_inv_one_up hp.1.1, Matrix.mul_one]
    exact e
end Formalism.FourierDecayAlt.P.A5x9
