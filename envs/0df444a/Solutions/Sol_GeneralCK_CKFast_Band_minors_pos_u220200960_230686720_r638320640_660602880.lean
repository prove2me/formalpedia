-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r638320640_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:00:20.521485+00:00
-- url     : https://prove2.me/submissions/095feb15-d304-4212-a4e1-df97d5f25660

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [487/640, 63/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 638320640 643891200 ⟨⟨211563922304, 211563922313⟩, ⟨203165053754, 220125356533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 643891200 649461760 ⟨⟨213249125930, 213249125938⟩, ⟨204823405621, 221837364765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 638320640 643891200 ⟨⟨208384035057, 208384035065⟩, ⟨200049866344, 216880106905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 643891200 649461760 ⟨⟨210048230912, 210048230921⟩, ⟨201687230842, 218571109914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 649461760 655032320 ⟨⟨214932775598, 214932775606⟩, ⟨206480219209, 223547798902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 655032320 660602880 ⟨⟨216614893776, 216614893785⟩, ⟨208135516611, 225256681772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 649461760 655032320 ⟨⟨211710933164, 211710933173⟩, ⟨203323115507, 220260601200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 655032320 660602880 ⟨⟨213372163292, 213372163301⟩, ⟨204957541462, 221948602584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 638320640 643891200 ⟨⟨205221134786, 205221134795⟩, ⟨196951052312, 213652453432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 643891200 649461760 ⟨⟨206864250059, 206864250068⟩, ⟨198567365548, 215322368817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 638320640 643891200 ⟨⟨202074850334, 202074850338⟩, ⟨193868251382, 210442014404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 643891200 649461760 ⟨⟨203696814775, 203696814780⟩, ⟨195463451773, 212090762599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 649461760 655032320 ⟨⟨208505930562, 208505930571⟩, ⟨200182255909, 216990833302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 655032320 660602880 ⟨⟨210146196823, 210146196831⟩, ⟨201795743591, 218657867729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 649461760 655032320 ⟨⟨205317401776, 205317401780⟩, ⟨197057284784, 213738119170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 655032320 660602880 ⟨⟨206936630939, 206936630942⟩, ⟨198649769707, 215384104017⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 638320640 660602880 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 649461760) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 643891200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 655032320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 655032320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 649461760) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 643891200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 655032320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 655032320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (487/640 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
