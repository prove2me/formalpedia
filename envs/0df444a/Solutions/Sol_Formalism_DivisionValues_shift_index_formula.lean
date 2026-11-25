-- Prove2me | solution 1 for Formalism.DivisionValues.shift_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:57.763716+00:00
-- url     : https://prove2.me/submissions/ce89cb36-5e18-4428-bad3-190e395fb6eb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_idx_smulLat
import Theorems.Thm_Formalism_DivisionValues_StepBAux_lidx_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution : ShiftIndex := by
  intro K _ _ _ d N N' hN w s hsh
  obtain ⟨a, ha, hva, hloc⟩ := hsh
  have e : idx w N N' = idx w N (smulLat a N) := by
    unfold idx
    exact Formalism.DivisionValues.StepBAux.lidx_congr w.asIdeal N N N' (smulLat a N) rfl hloc
  rw [e, shift_idx_smulLat w N hN a ha, hva]
  ring
end Formalism.DivisionValues
