-- Prove2me | solution 1 for Formalism.IncomingBounds.cor_tsum_cmp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:12.31581+00:00
-- url     : https://prove2.me/submissions/15c5c75c-13fe-4eab-b500-a1d2d89bf8d0

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm

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
theorem _root_.solution {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by
  have hf : Summable f := Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgf hf
  exact hg.tsum_le_tsum hgf hf
end Formalism.IncomingBounds
