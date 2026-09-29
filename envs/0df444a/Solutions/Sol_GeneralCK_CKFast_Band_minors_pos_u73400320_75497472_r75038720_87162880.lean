-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u73400320_75497472_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:28.747108+00:00
-- url     : https://prove2.me/submissions/a82b3f47-c3e3-4fe9-be9e-1257cce19298

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/80, 9/100]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 73400320 73924608 75038720 78069760 ⟨⟨84573385978, 84573385988⟩, ⟨80743883773, 88464587143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 73924608 74448896 75038720 78069760 ⟨⟨84129650499, 84129650511⟩, ⟨80321686112, 87998680049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 73400320 73924608 78069760 81100800 ⟨⟨87521458968, 87521458977⟩, ⟨83683895907, 91420198876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 73924608 74448896 78069760 81100800 ⟨⟨87065441092, 87065441104⟩, ⟨83249390874, 90942044933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 74448896 74973184 75038720 78069760 ⟨⟨83690147554, 83690147563⟩, ⟨79903469705, 87537266868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 74973184 75497472 75038720 78069760 ⟨⟨83254810864, 83254810876⟩, ⟨79489172740, 87080276643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 74448896 74973184 78069760 81100800 ⟨⟨86613734250, 86613734260⟩, ⟨82818947300, 90468461444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 74973184 75497472 78069760 81100800 ⟨⟨86166271473, 86166271482⟩, ⟨82392502621, 89999376831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 73924608 81100800 84131840 ⟨⟨90444504401, 90444504411⟩, ⟨86599204860, 94350462756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 73924608 74448896 81100800 84131840 ⟨⟨89976498935, 89976498947⟩, ⟨86152682835, 93860361043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 73400320 73924608 84131840 87162880 ⟨⟨93343008538, 93343008548⟩, ⟨89490285620, 97255876336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 73924608 74448896 84131840 87162880 ⟨⟨92863301477, 92863301489⟩, ⟨89032028422, 96754116875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 74448896 74973184 81100800 84131840 ⟨⟨89512878752, 89512878764⟩, ⟨85710298286, 93374902021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 74973184 75497472 81100800 84131840 ⟨⟨89053576266, 89053576275⟩, ⟨85271987969, 92894013558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 74448896 74973184 84131840 87162880 ⟨⟨92388049885, 92388049897⟩, ⟨88577980705, 96257068226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74973184 75497472 84131840 87162880 ⟨⟨91917185627, 91917185637⟩, ⟨88128078620, 95764657780⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 73400320 75497472 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 74448896) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 73924608) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 73924608) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 74973184) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 74973184) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 74448896) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 73924608) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 73924608) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 74973184) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 74973184) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/80 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
