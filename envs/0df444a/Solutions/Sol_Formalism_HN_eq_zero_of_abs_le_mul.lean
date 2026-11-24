-- Prove2me | solution 1 for Formalism.HN.eq_zero_of_abs_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:21.446379+00:00
-- url     : https://prove2.me/submissions/348fb951-0ebf-40bf-9818-ba5f8295a69b

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (a : ℝ) (n : ℕ) (h : ∀ t : ℝ, 0 < t → |a| ≤ t * n) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.mpr ha
  obtain ⟨t, ht⟩ : ∃ t, t = |a| / (2 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  have h1 := h t htpos
  have hm : t * (2 * ((n : ℝ) + 1)) = |a| := by
    rw [ht]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_nonneg htpos.le (Nat.cast_nonneg n)]
end Formalism.HN
