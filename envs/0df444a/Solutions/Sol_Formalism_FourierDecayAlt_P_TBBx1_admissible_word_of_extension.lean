-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.admissible_word_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:39.508174+00:00
-- url     : https://prove2.me/submissions/d2adb6fc-86a9-43a2-9c1a-362e3fc591d0

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
variable {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution {m : ℕ} {w w' : List C.Letter} (hw : AdmW P l0 Y w) (h : IsExt P l0 Y N m w w') :
    AdmW P l0 Y w' := by
  obtain ⟨hc, -, L, rfl, -, hL⟩ := h
  refine ⟨hc, fun l hl => ?_⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hL l hl
  · exact hw.2 l hl
end Formalism.FourierDecayAlt.P.TBBx1
