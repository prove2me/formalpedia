-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.exists_max_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:11.616618+00:00
-- url     : https://prove2.me/submissions/e0a4cef9-c905-45b4-b019-8cb93d4b1ba0

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_finite

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
theorem _root_.solution (m : ℕ) (w : List C.Letter) (f : List C.Letter → ℝ) (hw : IsExt P l0 Y N m w w) :
    ∃ w', IsExt P l0 Y N m w w' ∧ ∀ w'', IsExt P l0 Y N m w w'' → f w'' ≤ f w' := by
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ f (isExt_finite m w) ⟨w, hw⟩
  exact ⟨a, ha, fun b hb => hmax b hb⟩
end Formalism.FourierDecayAlt.P.TBBx1
