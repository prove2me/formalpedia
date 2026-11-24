-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:13:57.220803+00:00
-- url     : https://prove2.me/submissions/e77c6f0e-d418-4a97-ba97-a3dae7188467

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = WeylGroupFacts.sgn k r i * u (WeylGroupFacts.tau k r i) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (WeylGroupFacts.tau k r i)]
  · rw [WeylGroupFacts.hpk_row, if_pos rfl]
  · intro m _ hm
    rw [WeylGroupFacts.hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.B2x6
