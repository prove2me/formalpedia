-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.norm_sub_tens_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:27.60277+00:00
-- url     : https://prove2.me/submissions/1a314dbc-6170-4ec6-8978-c950f5c0bd02

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}
namespace Formalism.L2.SG.Pf.WuDec
theorem _root_.solution (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x y : ∀ v, V v) :
    ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ v, ⟪x v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) +
      (∏ v, ⟪y v, y v⟫_ℂ)) := by
  have e := inner_self_eq_norm_sq (𝕜 := ℂ) (tens x - tens y)
  rw [← e, inner_sub_left, inner_sub_right, inner_sub_right, hi, hi, hi, hi]
  congr 1
  ring
end Formalism.L2.SG.Pf.WuDec
