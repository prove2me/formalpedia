-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:44:02.073297+00:00
-- url     : https://prove2.me/submissions/ef7326f6-2af6-47c6-886d-6d442ed597e3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 9/200]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 34603008 111411200 117473280 ⟨⟨186261108198, 186261108218⟩, ⟨173133619854, 199928611779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 34603008 35651584 111411200 117473280 ⟨⟨183579536791, 183579536807⟩, ⟨170690463913, 196992579414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 34603008 117473280 123535360 ⟨⟨193079549941, 193079549961⟩, ⟨180013834327, 206665372781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 34603008 35651584 117473280 123535360 ⟨⟨190359883469, 190359883488⟩, ⟨177526919934, 203697949830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 35651584 36700160 111411200 117473280 ⟨⟨180975894816, 180975894835⟩, ⟨168316569509, 194143870475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 36700160 37748736 111411200 117473280 ⟨⟨178446534297, 178446534312⟩, ⟨166008756315, 191378325780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 35651584 36700160 117473280 123535360 ⟨⟨187717431367, 187717431387⟩, ⟨175108936061, 200816683805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 36700160 37748736 117473280 123535360 ⟨⟨185148649024, 185148649043⟩, ⟨172756776369, 198017553528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 34603008 123535360 129597440 ⟨⟨199721306902, 199721306918⟩, ⟨186719143488, 213224634556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 34603008 35651584 123535360 129597440 ⟨⟨196967439200, 196967439219⟩, ⟨184192486372, 210229518043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 33554432 34603008 129597440 135659520 ⟨⟨206196594527, 206196594548⟩, ⟨193259388050, 219616929094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 34603008 35651584 129597440 135659520 ⟨⟨203412036913, 203412036933⟩, ⟨190696628773, 216597432374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 35651584 36700160 123535360 129597440 ⟨⟨194289994599, 194289994615⟩, ⟨181734333578, 207319341221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 36700160 37748736 123535360 129597440 ⟨⟨191685530463, 191685530479⟩, ⟨179341653525, 204490216744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 35651584 36700160 129597440 135659520 ⟨⟨200703050331, 200703050346⟩, ⟨188201868504, 213661621450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 36700160 37748736 129597440 135659520 ⟨⟨198066292199, 198066292218⟩, ⟨185772150506, 210805738311⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 37748736 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 35651584) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 34603008) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 34603008) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 36700160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 36700160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 35651584) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 34603008) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 34603008) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 36700160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 36700160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
