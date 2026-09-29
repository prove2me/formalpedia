-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:33:38.479472+00:00
-- url     : https://prove2.me/submissions/c7797ab1-2637-4b98-bf91-f42c93587f6b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 201850880 207749120 ⟨⟨146996126727, 146996126737⟩, ⟨140374582914, 153756290848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 111411200 112721920 201850880 207749120 ⟨⟨145706751623, 145706751634⟩, ⟨139142481783, 152407777476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 111411200 207749120 213647360 ⟨⟨150602315320, 150602315331⟩, ⟨143961640695, 157380442612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 111411200 112721920 207749120 213647360 ⟨⟨149290306482, 149290306493⟩, ⟨142706727582, 156009515420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 114032640 201850880 207749120 ⟨⟨144433180481, 144433180491⟩, ⟨137925232710, 151076059021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 114032640 115343360 201850880 207749120 ⟨⟨143175063272, 143175063274⟩, ⟨136722509643, 149760760369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 112721920 114032640 207749120 213647360 ⟨⟨147994187858, 147994187869⟩, ⟨141466764798, 154655455924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114032640 115343360 207749120 213647360 ⟨⟨146713610665, 146713610669⟩, ⟨140241427006, 153317890852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 111411200 213647360 219545600 ⟨⟨154182559378, 154182559388⟩, ⟨147523211236, 160978198522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 111411200 112721920 213647360 219545600 ⟨⟨152848426127, 152848426137⟩, ⟨146245986675, 159585375012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 111411200 219545600 225443840 ⟨⟨157737412798, 157737412808⟩, ⟨151059832822, 164550128174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 111411200 112721920 219545600 225443840 ⟨⟨156381648382, 156381648392⟩, ⟨149760781802, 163135909253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112721920 114032640 213647360 219545600 ⟨⟨151530259618, 151530259628⟩, ⟨144983801056, 158209482231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114032640 115343360 213647360 219545600 ⟨⟨150227712501, 150227712505⟩, ⟨143736329954, 156850148915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 114032640 219545600 225443840 ⟨⟨155041918001, 155041918012⟩, ⟨148476849156, 161738674839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114032640 115343360 219545600 225443840 ⟨⟨153717875909, 153717875914⟩, ⟨147207711544, 160358055844⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 111411200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 114032640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 112721920) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 111411200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 114032640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
