-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_112721920_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:07:21.823774+00:00
-- url     : https://prove2.me/submissions/802a90e2-f18d-43ea-a52c-042b1b04f08f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 43/320]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 110755840 95682560 98631680 ⟨⟨76049890140, 76049890150⟩, ⟨72938131753, 79202020232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110755840 111411200 95682560 98631680 ⟨⟨75665361441, 75665361451⟩, ⟨72568446539, 78802301789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 110755840 98631680 101580800 ⟨⟨78158815940, 78158815948⟩, ⟨75039278019, 81318568435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110755840 111411200 98631680 101580800 ⟨⟨77765256239, 77765256248⟩, ⟨74660576063, 80909808107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 111411200 112066560 95682560 98631680 ⟨⟨75283826916, 75283826926⟩, ⟨72201608993, 78405728717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112066560 112721920 95682560 98631680 ⟨⟨74905246209, 74905246217⟩, ⟨71837580984, 78012258344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 111411200 112066560 98631680 101580800 ⟨⟨77374741057, 77374741066⟩, ⟨74284772501, 80504243036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112066560 112721920 98631680 101580800 ⟨⟨76987229583, 76987229590⟩, ⟨73911828735, 80101830114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 110755840 101580800 104529920 ⟨⟨80257684648, 80257684658⟩, ⟨77130481893, 83424944928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110755840 111411200 101580800 104529920 ⟨⟨79855216730, 79855216740⟩, ⟨76742884268, 83007267191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 110755840 104529920 107479040 ⟨⟨82346620077, 82346620085⟩, ⟨79211864951, 85521275766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 110755840 111411200 104529920 107479040 ⟨⟨81935364477, 81935364487⟩, ⟨78815490535, 85094802796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 111411200 112066560 101580800 104529920 ⟨⟨79455842006, 79455842013⟩, ⟨76358234120, 82592832901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112066560 112721920 101580800 104529920 ⟨⟨79059519230, 79059519240⟩, ⟨75976492406, 82181598543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 111411200 112066560 104529920 107479040 ⟨⟨81527249118, 81527249125⟩, ⟨78422111076, 84671619817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112066560 112721920 104529920 107479040 ⟨⟨81122232351, 81122232361⟩, ⟨78031687113, 84251682924⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 112721920 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 111411200) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 110755840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112066560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 111411200) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 110755840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112066560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (43/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
