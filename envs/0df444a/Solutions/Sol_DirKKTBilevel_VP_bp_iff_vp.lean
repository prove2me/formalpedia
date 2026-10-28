-- Prove2me | solution 1 for DirKKTBilevel.VP.bp_iff_vp
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:45:17.000743+00:00
-- url     : https://prove2.me/submissions/0a946ec0-0809-4721-9326-65304f58711b

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

open DirKKTBilevel.VP in
theorem solution {n m p q : ℕ} (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (x : E n) (y : E m) :
    (y ∈ solMap f g x ∧ ∀ j, G (WithLp.toLp 2 (x, y)) j ≤ 0) ↔
      ((f (WithLp.toLp 2 (x, y)) : EReal) - valueFn f g x ≤ 0 ∧
        (∀ i, g (WithLp.toLp 2 (x, y)) i ≤ 0) ∧ ∀ j, G (WithLp.toLp 2 (x, y)) j ≤ 0) := by
  have hle : ∀ y' ∈ feasLL g x, valueFn f g x ≤ ((f (WithLp.toLp 2 (x, y')) : ℝ) : EReal) := by
    intro y' hy'
    unfold valueFn
    exact iInf₂_le y' hy'
  constructor
  · rintro ⟨⟨hfeas, hmin⟩, hG⟩
    have hV : valueFn f g x = ((f (WithLp.toLp 2 (x, y)) : ℝ) : EReal) := by
      apply le_antisymm (hle y hfeas)
      unfold valueFn
      exact le_iInf₂ (fun y' hy' => EReal.coe_le_coe_iff.mpr (hmin y' hy'))
    refine ⟨?_, hfeas, hG⟩
    rw [hV, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  · rintro ⟨h1, hfeas, hG⟩
    have key : ((f (WithLp.toLp 2 (x, y)) : ℝ) : EReal) ≤ valueFn f g x := by
      generalize valueFn f g x = V at h1
      induction V using EReal.rec with
      | bot =>
        exfalso
        rw [EReal.coe_sub_bot] at h1
        exact absurd h1 (by simp)
      | top => exact le_top
      | coe v =>
        rw [← EReal.coe_sub] at h1
        have := EReal.coe_nonpos.mp h1
        exact EReal.coe_le_coe_iff.mpr (by linarith)
    refine ⟨⟨hfeas, fun y' hy' => ?_⟩, hG⟩
    exact EReal.coe_le_coe_iff.mp (le_trans key (hle y' hy'))
