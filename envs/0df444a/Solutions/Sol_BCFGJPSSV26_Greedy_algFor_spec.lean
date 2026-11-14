-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.algFor_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:18:30.569416+00:00
-- url     : https://prove2.me/submissions/13726df3-6b14-40a7-903c-48a7bfb9c096

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants
import all Definitions.Def_BCFGJPSSV26_Greedy_Constants
public import Theorems.Thm_BCFGJPSSV26_Greedy_algLS_spec
public import Theorems.Thm_BCFGJPSSV26_Greedy_algMain_spec
public import Theorems.Thm_BCFGJPSSV26_Greedy_bcomp_le
public import Theorems.Thm_BCFGJPSSV26_Greedy_sixR_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- **The guarantee of the algorithm for `ε`.** -/
theorem algFor_spec {ε : ℝ} (hε : 0 < ε) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algFor ε (toRaw I)) ∧
      ((algFor ε (toRaw I)).length : ℝ) ≤ I.k + Cthm * Real.log I.n / ε ^ 2 ∧
      I.cost (I.centers (algFor ε (toRaw I))) ≤ (1.9499 + ε) * I.opt I.k := by
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hlog := log_div_nonneg ε I.n
  unfold algFor
  split_ifs with h4
  · obtain ⟨hc, hlen, hcost⟩ := algLS_spec hI
    refine ⟨hc, ?_, hcost.trans ?_⟩
    · have : ((algLS (toRaw I)).length : ℝ) ≤ I.k := by exact_mod_cast hlen
      linarith
    · nlinarith
  · push Not at h4
    obtain ⟨hc, hlen, hcost⟩ := algMain_spec (constsOf_good hε) hI
    refine ⟨hc, ?_, hcost.trans (mul_le_mul_of_nonneg_right (ratio_le hε h4) hopt0)⟩
    rcases hlen with hlen | ⟨hbn, hn2, hlen⟩
    · have h := bcomp_le hε h4 I.n
      have : ((algMain (constsOf ε) (toRaw I)).length : ℝ) ≤ I.k + bcomp (constsOf ε) I.n := by
        exact_mod_cast hlen
      linarith
    · have h := sixR_le hε h4 hbn hn2
      have : ((algMain (constsOf ε) (toRaw I)).length : ℝ) ≤
          I.k + ((6 * Rof (constsOf ε) I.n : ℕ) : ℝ) := by
        exact_mod_cast hlen
      linarith

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.algFor_spec := @BCFGJPSSV26.Greedy.algFor_spec
