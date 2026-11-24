-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:34:46.698645+00:00
-- url     : https://prove2.me/submissions/2fe89a27-ac30-41e0-baf0-a8255dd416e3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution (c : ℂ) : PolyClass 0 (fun _ : Mat k r => c) := by
  refine ⟨ckOn_const' c, fun a _ => ?_⟩
  obtain ⟨c', hc', he⟩ := W_const c a
  exact ⟨‖c‖, norm_nonneg _, fun g _ => by rw [he]; simpa using hc'⟩
end Formalism.FourierDecayAlt.P.ListSumSplittings
