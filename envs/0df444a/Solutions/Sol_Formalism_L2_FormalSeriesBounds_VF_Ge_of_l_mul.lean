-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.of_l_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:37.742394+00:00
-- url     : https://prove2.me/submissions/bea8e365-eee9-485e-ab16-91e04b3d730e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C]
open Formalism.L2.FormalSeriesBounds.VF
variable (V : VF C)
variable {V}
namespace Formalism.L2.FormalSeriesBounds.VF
namespace Ge
theorem _root_.solution {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) * a)) : V.Ge (w - 1) a := by
  have h0 : ((w : ℝ) : WithTop ℝ) ≤ 1 + V.v a := by
    have h2 : ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a) := h
    rwa [AddValuation.map_mul, V.v_l] at h2
  show (((w - 1) : ℝ) : WithTop ℝ) ≤ V.v a
  by_cases hva : V.v a = ⊤
  · rw [hva]; exact le_top
  · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hva
    rw [← hx] at h0 ⊢
    have h' : w ≤ 1 + x := by exact_mod_cast h0
    exact WithTop.coe_le_coe.mpr (by linarith)
end Ge
end Formalism.L2.FormalSeriesBounds.VF
