-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.levelsChain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:13.274884+00:00
-- url     : https://prove2.me/submissions/2cbe88a8-aea7-49b9-bd8f-23c84d1ef73d

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_BCount
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_levelsSum
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_poleOrderBad
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_poleOrderGood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith
end Formalism.LatticeBaseChangeAlt
