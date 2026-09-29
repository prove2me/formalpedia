-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u65011712_67108864_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:05:45.401021+00:00
-- url     : https://prove2.me/submissions/a8e1f2d8-e1d1-4035-a5bc-b8df27b44950

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/400, 2/25]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 65011712 65536000 75038720 78069760 ⟨⟨92308960415, 92308960428⟩, ⟨88096566132, 96594772313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 65536000 66060288 75038720 78069760 ⟨⟨91787177265, 91787177276⟩, ⟨87601049457, 96045891936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 65011712 65536000 78069760 81100800 ⟨⟨95464806641, 95464806651⟩, ⟨91245040445, 99757257755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 65536000 66060288 78069760 81100800 ⟨⟨94929388291, 94929388304⟩, ⟨90735826240, 99194820366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 66060288 66584576 75038720 78069760 ⟨⟨91270914352, 91270914365⟩, ⟨87110712841, 95502886567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 66584576 67108864 75038720 78069760 ⟨⟨90760076602, 90760076615⟩, ⟨86625467881, 94965654096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 66060288 66584576 78069760 81100800 ⟨⟨94399580127, 94399580137⟩, ⟨90231885048, 98638344503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 66584576 67108864 78069760 81100800 ⟨⟨93875286349, 93875286360⟩, ⟨89733127650, 98087727454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 65011712 65536000 81100800 84131840 ⟨⟨98590261193, 98590261206⟩, ⟨94363527368, 102888954731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 65536000 66060288 81100800 84131840 ⟨⟨98041582314, 98041582325⟩, ⟨93840984774, 102313340241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 65011712 65536000 84131840 87162880 ⟨⟨101685981186, 101685981197⟩, ⟨97452667836, 105990536522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 65536000 66060288 84131840 87162880 ⟨⟨101124403871, 101124403884⟩, ⟨96917153798, 105402111899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 66060288 66584576 81100800 84131840 ⟨⟨97498597835, 97498597849⟩, ⟨93323802504, 101743768002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 66584576 67108864 81100800 84131840 ⟨⟨96961211354, 96961211367⟩, ⟨92811890612, 101180134816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 66060288 66584576 84131840 87162880 ⟨⟨100568599738, 100568599748⟩, ⟨96387082014, 104819804763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 66584576 67108864 84131840 87162880 ⟨⟨100018471868, 100018471878⟩, ⟨95862361920, 104243511528⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 65011712 67108864 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 66060288) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 65536000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 65536000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 66584576) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 66584576) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 66060288) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 65536000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 65536000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 66584576) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 66584576) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/400 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((65011712 : ℤ) : ℝ) / (D : ℝ)) = (31/400 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
