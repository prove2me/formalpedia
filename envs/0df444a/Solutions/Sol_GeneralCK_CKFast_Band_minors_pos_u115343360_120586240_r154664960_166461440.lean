-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:28:19.004808+00:00
-- url     : https://prove2.me/submissions/040ca1b4-d98a-4037-b76d-11e225c79842

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 154664960 157614080 ⟨⟨111939928997, 111939929007⟩, ⟨107031828836, 116934786116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 116654080 157614080 160563200 ⟨⟨113810791782, 113810791790⟩, ⟨108891908840, 118816168633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 116654080 117964800 154664960 157614080 ⟨⟨110915587650, 110915587658⟩, ⟨106047319958, 115869435513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 157614080 160563200 ⟨⟨112772978156, 112772978166⟩, ⟨107893920732, 117737363877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 116654080 160563200 163512320 ⟨⟨115674432531, 115674432541⟩, ⟨110744874970, 120690220692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 116654080 163512320 166461440 ⟨⟨117530929911, 117530929919⟩, ⟨112590804134, 122557022734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117964800 160563200 163512320 ⟨⟨114623301952, 114623301962⟩, ⟨109733560298, 119598119718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 116654080 117964800 163512320 166461440 ⟨⟨116466635207, 116466635215⟩, ⟨111566313136, 121451780910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 119275520 154664960 157614080 ⟨⟨109904556788, 109904556796⟩, ⟨105075417698, 114818126001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 119275520 157614080 160563200 ⟨⟨111748568839, 111748568849⟩, ⟨106908636108, 116672690570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 119275520 120586240 154664960 157614080 ⟨⟨108906528142, 108906528150⟩, ⟨104115832386, 113780529885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 119275520 120586240 157614080 160563200 ⟨⟨110737254854, 110737254862⟩, ⟨105935764429, 115621820492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 117964800 119275520 160563200 163512320 ⟨⟨113585666047, 113585666057⟩, ⟨108735042570, 118520237045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 117964800 119275520 163512320 166461440 ⟨⟨115415922173, 115415922183⟩, ⟨110554709230, 120360840823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 120586240 160563200 163512320 ⟨⟨112561215221, 112561215231⟩, ⟨107749030471, 117456244011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119275520 120586240 163512320 166461440 ⟨⟨114378480679, 114378480689⟩, ⟨109555700395, 119283873453⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 117964800) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 116654080) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 160563200) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 119275520) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
