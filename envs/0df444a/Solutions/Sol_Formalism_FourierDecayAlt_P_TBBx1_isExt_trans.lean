-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.isExt_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:43.103714+00:00
-- url     : https://prove2.me/submissions/edf882c8-9653-4ea1-b73e-10b3f8e3fcc1

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
theorem _root_.solution {m₁ m₂ : ℕ} {w w' w'' : List C.Letter} (h1 : IsExt P l0 Y N m₁ w w')
    (h2 : IsExt P l0 Y N m₂ w' w'') : IsExt P l0 Y N (m₁ + m₂) w w'' := by
  obtain ⟨-, -, L1, rfl, hL1, hY1⟩ := h1
  obtain ⟨hc, hN, L2, rfl, hL2, hY2⟩ := h2
  refine ⟨hc, hN, L2 ++ L1, by simp, by simp only [List.length_append]; omega, fun l hl => ?_⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hY2 l hl
  · exact hY1 l hl
end Formalism.FourierDecayAlt.P.TBBx1
