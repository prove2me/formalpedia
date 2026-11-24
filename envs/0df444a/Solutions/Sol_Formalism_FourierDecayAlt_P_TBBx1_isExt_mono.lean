-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.isExt_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:43.513801+00:00
-- url     : https://prove2.me/submissions/0891b6d1-a590-4d07-89bc-26d6b059f56f

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
theorem _root_.solution {m m' : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') (hm : m ≤ m') :
    IsExt P l0 Y N m' w w' := by
  obtain ⟨hc, hN, L, hL, hLm, hY⟩ := h
  exact ⟨hc, hN, L, hL, hLm.trans hm, hY⟩
end Formalism.FourierDecayAlt.P.TBBx1
