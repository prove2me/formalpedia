-- Prove2me | solution 1 for Formalism.IncomingBounds.contentShift_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:11.777405+00:00
-- url     : https://prove2.me/submissions/5f28e040-cc94-46a6-b6b2-cab50cc2f0a3

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
import Theorems.Thm_Formalism_IncomingBounds_cor_gam_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    ContentShift := by
  intro l d inst hl hd hev th D' E hth hD' hE hED
  classical
  obtain ⟨⟨sig, hsig, -, hFsig⟩, -⟩ := hA l d hl hd hev D' hD'
  have hopt : IsOptDual l d D' sig := ⟨hsig, hFsig⟩
  have h1 := (hc l d hl hd hev D' E sig hD' hE hopt).1
  have hinc := hI l d hl hd hev D' sig hD' hopt
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hg := cor_gam_nonneg hl
  have hpt : ∀ a, E a * max (sig a - gam l) 0 ≤
      4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0) := by
    intro a
    have hs0 := (hsig.1 a).1
    have hs1 := (hsig.1 a).2
    have hEa := hE a
    have hDa := hD' a
    have hEDa := hED a
    have hm : max (sig a - gam l) 0 ≤ sig a := max_le (by linarith) hs0
    have hm0 : 0 ≤ max (sig a - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * th * D' a / l := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hth) hDa) hl0.le
    split_ifs with hcase
    · calc E a * max (sig a - gam l) 0 ≤ E a * 1 := mul_le_mul_of_nonneg_left (hm.trans hs1) hEa
        _ ≤ 2 * th * D' a := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      calc E a * max (sig a - gam l) 0 ≤ (2 * th * D' a) * (2 / l) :=
            mul_le_mul hEDa (hm.trans hcase.le) hm0 (mul_nonneg (mul_nonneg (by norm_num) hth) hDa)
        _ = 4 * th * D' a / l + 2 * th * 0 := by ring
  have hsum : ∑ a, E a * max (sig a - gam l) 0 ≤ 6 * th * (∑ a, D' a) / l := by
    calc ∑ a, E a * max (sig a - gam l) 0
        ≤ ∑ a, (4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0)) :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = 4 * th * (∑ a, D' a) / l +
            2 * th * ∑ a ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D' a := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum]
      _ ≤ 4 * th * (∑ a, D' a) / l + 2 * th * ((∑ a, D' a) / l) := by
          have : 0 ≤ 2 * th := by linarith
          nlinarith
      _ = 6 * th * (∑ a, D' a) / l := by ring
  linarith
end Formalism.IncomingBounds
