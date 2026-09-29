-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:19.848018+00:00
-- url     : https://prove2.me/submissions/70d528f5-0e26-473f-8f2e-effb79cc756a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [23/40, 77/128]` by 15 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 482344960 487915520 ⟨⟨219523792532, 219523792541⟩, ⟨210408692370, 228829677304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 487915520 493486080 ⟨⟨221717936496, 221717936504⟩, ⟨212575809550, 231050324769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 482344960 487915520 ⟨⟨216484317859, 216484317869⟩, ⟨207454214235, 225703609802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 487915520 493486080 ⟨⟨218656207553, 218656207562⟩, ⟨209598930712, 227902190520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 493486080 504627200 ⟨⟨225000334148, 225000334156⟩, ⟨214058648784, 236214519325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 170393600 173015040 493486080 499056640 ⟨⟨220823537902, 220823537912⟩, ⟨211739177925, 230096116524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 499056640 504627200 ⟨⟨222986372667, 222986372677⟩, ⟨213875018173, 232285453048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 173015040 175636480 482344960 487915520 ⟨⟨213474747850, 213474747859⟩, ⟨204528281131, 222608824222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 487915520 493486080 ⟨⟨215624300874, 215624300882⟩, ⟨206650531116, 224785237729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 178257920 482344960 487915520 ⟨⟨210494324699, 210494324705⟩, ⟨201630169824, 219544528189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 487915520 493486080 ⟨⟨212621464050, 212621464053⟩, ⟨203729892243, 221698680150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 173015040 175636480 493486080 499056640 ⟨⟨217769445917, 217769445927⟩, ⟨208768459479, 226957151578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 499056640 504627200 ⟨⟨219910244062, 219910244071⟩, ⟨210882125916, 229124628243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 493486080 499056640 ⟨⟨214744343323, 214744343329⟩, ⟨205825437239, 223848484051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 178257920 499056640 504627200 ⟨⟨216863021019, 216863021024⟩, ⟨207916861998, 225993999698⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 482344960 504627200 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 493486080) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 487915520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (leaf_ok cell4) (join_sr (m := 499056640) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 493486080) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 487915520) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 175636480) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 499056640) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
