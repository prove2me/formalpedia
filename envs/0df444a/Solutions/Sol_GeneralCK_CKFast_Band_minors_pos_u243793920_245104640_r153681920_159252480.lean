-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:49.647204+00:00
-- url     : https://prove2.me/submissions/90da3dba-40f2-43db-9e96-3bb16e4a0fc2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 153681920 155074560 ⟨⟨47387848270, 47387848276⟩, ⟨46571439731, 48207230800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 153681920 155074560 ⟨⟨47277692815, 47277692820⟩, ⟨46462289307, 48096064483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244121600 155074560 156467200 ⟨⟨47804659497, 47804659504⟩, ⟨46987325035, 48624969361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244121600 244449280 155074560 156467200 ⟨⟨47693581707, 47693581712⟩, ⟨46877253684, 48512879304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244449280 244776960 153681920 155074560 ⟨⟨47167683101, 47167683106⟩, ⟨46353282423, 47985046129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244776960 245104640 153681920 155074560 ⟨⟨47057818589, 47057818592⟩, ⟨46244418550, 47874175186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 155074560 156467200 ⟨⟨47582650577, 47582650582⟩, ⟨46767326792, 48400938134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 155074560 156467200 ⟨⟨47471865565, 47471865568⟩, ⟨46657543824, 48289145290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244121600 156467200 157859840 ⟨⟨48221295914, 48221295919⟩, ⟨47403035801, 49042532835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244121600 244449280 156467200 157859840 ⟨⟨48109296930, 48109296936⟩, ⟨47292044661, 48929520188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244121600 157859840 159252480 ⟨⟨48637757921, 48637757927⟩, ⟨47818572429, 49459921626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244121600 244449280 157859840 159252480 ⟨⟨48524838885, 48524838890⟩, ⟨47706662637, 49345987531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 244776960 156467200 157859840 ⟨⟨47997445520, 47997445527⟩, ⟨47181198893, 48816657339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 244776960 245104640 156467200 157859840 ⟨⟨47885741139, 47885741142⟩, ⟨47070497957, 48703943729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244449280 244776960 157859840 159252480 ⟨⟨48412068329, 48412068334⟩, ⟨47594899120, 49232204143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244776960 245104640 157859840 159252480 ⟨⟨48299445705, 48299445708⟩, ⟨47483281339, 49118570897⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244121600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 244776960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 244449280) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244121600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 244776960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
