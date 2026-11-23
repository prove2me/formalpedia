-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.colSpan_le_latZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:56.29006+00:00
-- url     : https://prove2.me/submissions/05d8cd5f-4147-4f11-9a65-742f569f7b95

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_colSpan_mul

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
    colSpan R k Z₀ ≤ latZ R (Z₀ * p) := by
  intro x hx
  rw [← colSpan_mul R k Z₀ p hp, mem_colSpan] at hx
  obtain ⟨t, _, e⟩ := hx
  exact (mem_latZ R _ x).2 ⟨t, e⟩
end Formalism.FourierDecayAlt.P.A5x9
