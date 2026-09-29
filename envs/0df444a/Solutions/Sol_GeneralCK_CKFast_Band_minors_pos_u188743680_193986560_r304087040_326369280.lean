-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:40:10.352547+00:00
-- url     : https://prove2.me/submissions/3ff3d4ef-6d28-41b8-adc1-d3b2e650e8bf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 304087040 309657600 ⟨⟨129867989736, 129867989744⟩, ⟨125322869792, 134480045862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 190054400 191365120 304087040 309657600 ⟨⟨128857071423, 128857071431⟩, ⟨124337698023, 133442866814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 190054400 309657600 315228160 ⟨⟨132031187389, 132031187398⟩, ⟨127469612965, 136659614464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 309657600 315228160 ⟨⟨131006160797, 131006160805⟩, ⟨126470362895, 135608303017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192675840 304087040 309657600 ⟨⟨127852196802, 127852196810⟩, ⟨123358323960, 132411983510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192675840 193986560 304087040 309657600 ⟨⟨126853279636, 126853279639⟩, ⟨122384665063, 131387305913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 192675840 309657600 315228160 ⟨⟨129987205316, 129987205322⟩, ⟨125476939423, 134563313110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193986560 309657600 315228160 ⟨⟨128974234753, 128974234757⟩, ⟨124489260003, 133524554811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 190054400 315228160 320798720 ⟨⟨134188980970, 134188980976⟩, ⟨129611020861, 138833708560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 191365120 315228160 320798720 ⟨⟨133149954308, 133149954317⟩, ⟨128597798798, 137768374841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 320798720 326369280 ⟨⟨136341436651, 136341436659⟩, ⟨131747158649, 141002395346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 191365120 320798720 326369280 ⟨⟨135288516418, 135288516427⟩, ⟨130720069215, 139923147732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 315228160 320798720 ⟨⟨132117024424, 132117024433⟩, ⟨127590430494, 136709386683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193986560 315228160 320798720 ⟨⟨131090105194, 131090105199⟩, ⟨126588833433, 135656654270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 320798720 326369280 ⟨⟨134241716915, 134241716923⟩, ⟨129698859023, 138850267956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 320798720 326369280 ⟨⟨133200952111, 133200952114⟩, ⟨128683445599, 137783666348⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 190054400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 192675840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 191365120) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 190054400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 192675840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
