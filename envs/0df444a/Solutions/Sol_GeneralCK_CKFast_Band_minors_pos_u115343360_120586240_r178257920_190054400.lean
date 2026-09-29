-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:33:51.931636+00:00
-- url     : https://prove2.me/submissions/d8585d6d-a689-44c4-9ccb-fb2b65811582

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [17/80, 29/128]` by 15 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 178257920 181207040 ⟨⟨126708943126, 126708943134⟩, ⟨121717513334, 131785019337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 116654080 181207040 184156160 ⟨⟨128524171644, 128524171653⟩, ⟨123522777097, 133609948047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 116654080 117964800 178257920 181207040 ⟨⟨125581036291, 125581036301⟩, ⟨120629312653, 130616317546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 181207040 184156160 ⟨⟨127383967925, 127383967933⟩, ⟨122422253147, 132428986520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 116654080 184156160 190054400 ⟨⟨131234619076, 131234619084⟩, ⟨124898555478, 137705125683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 116654080 117964800 184156160 187105280 ⟨⟨129180413622, 129180413632⟩, ⟨124208800592, 134235076519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117964800 187105280 190054400 ⟨⟨130970441610, 130970441620⟩, ⟨125989021761, 136034657231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117964800 119275520 178257920 181207040 ⟨⟨124467098369, 124467098377⟩, ⟨119554402732, 129462286298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 119275520 181207040 184156160 ⟨⟨126257801550, 126257801558⟩, ⟨121335091797, 131262760177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 119275520 120586240 178257920 181207040 ⟨⟨123366817679, 123366817687⟩, ⟨118492489189, 128322595937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 119275520 120586240 181207040 184156160 ⟨⟨125145360742, 125145360750⟩, ⟨120260998400, 130110939441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 119275520 184156160 187105280 ⟨⟨128042152625, 128042152633⟩, ⟨123109519522, 133056790978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 117964800 119275520 187105280 190054400 ⟨⟨129820217745, 129820217755⟩, ⟨124877750669, 134844446264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119275520 120586240 184156160 187105280 ⟨⟨126917682754, 126917682764⟩, ⟨122023375246, 131892972959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 120586240 187105280 190054400 ⟨⟨128683847867, 128683847877⟩, ⟨123779682537, 133668762001⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 117964800) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 116654080) (by decide) (leaf_ok cell4) (join_sr (m := 187105280) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 184156160) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 181207040) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 119275520) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 187105280) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
