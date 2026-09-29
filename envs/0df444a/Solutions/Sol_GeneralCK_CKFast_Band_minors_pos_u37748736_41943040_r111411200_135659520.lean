-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:44:19.28676+00:00
-- url     : https://prove2.me/submissions/e323ad10-5876-4d5a-9e06-4ffd2920bfd2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 1/20]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 37748736 38797312 111411200 117473280 ⟨⟨175988041324, 175988041340⟩, ⟨163764044711, 188692056787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 38797312 39845888 111411200 117473280 ⟨⟨173597216864, 173597216872⟩, ⟨161579639612, 186081423103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 38797312 117473280 123535360 ⟨⟨182650215589, 182650215604⟩, ⟨170467527521, 195296795060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38797312 39845888 117473280 123535360 ⟨⟨180219015845, 180219015852⟩, ⟨168238453823, 192650880615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 39845888 40894464 111411200 117473280 ⟨⟨171271059469, 171271059484⟩, ⟨159452915792, 183543012366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 40894464 41943040 111411200 117473280 ⟨⟨169006749745, 169006749759⟩, ⟨157381404718, 181073622048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 39845888 40894464 117473280 123535360 ⟨⟨177852123889, 177852123903⟩, ⟨166066983269, 190076499657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 40894464 41943040 117473280 123535360 ⟨⟨175546788437, 175546788451⟩, ⟨163950695013, 187570541808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 37748736 38797312 123535360 129597440 ⟨⟨189150818138, 189150818152⟩, ⟨177011600218, 201738501935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 38797312 39845888 123535360 129597440 ⟨⟨186682825813, 186682825817⟩, ⟨174741498630, 199060778985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 37748736 38797312 129597440 135659520 ⟨⟨195498624648, 195498624667⟩, ⟨183404696489, 208026257871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 38797312 39845888 129597440 135659520 ⟨⟨192997098303, 192997098310⟩, ⟨181096892705, 205319869299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 40894464 123535360 129597440 ⟨⟨184278703072, 184278703088⟩, ⟨172528831427, 196453837189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 40894464 41943040 123535360 129597440 ⟨⟨181935767002, 181935767017⟩, ⟨170371227041, 193914656831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 39845888 40894464 129597440 135659520 ⟨⟨190558937647, 190558937666⟩, ⟨178846277324, 202683459309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 40894464 41943040 129597440 135659520 ⟨⟨188181527865, 188181527884⟩, ⟨176650529045, 200114096979⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 41943040 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 39845888) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 38797312) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 38797312) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 40894464) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 40894464) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 39845888) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 38797312) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 38797312) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 40894464) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 40894464) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
