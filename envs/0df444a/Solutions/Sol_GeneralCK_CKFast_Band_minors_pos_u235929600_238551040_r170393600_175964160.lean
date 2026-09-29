-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:42:41.094231+00:00
-- url     : https://prove2.me/submissions/3f3886ed-fe26-43d6-ae04-9b1bb3cc2864

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [13/64, 537/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 170393600 171786240 ⟨⟨55271592205, 55271592211⟩, ⟨53821256726, 56730697680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 236584960 171786240 173178880 ⟨⟨55707940221, 55707940226⟩, ⟨54255842465, 57168813422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 236584960 237240320 170393600 171786240 ⟨⟨55021772843, 55021772849⟩, ⟨53574463539, 56477822955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 171786240 173178880 ⟨⟨55456262735, 55456262742⟩, ⟨54007195729, 56914076031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 236584960 173178880 174571520 ⟨⟨56144090529, 56144090534⟩, ⟨54690230967, 57606730978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 236584960 174571520 175964160 ⟨⟨56580043605, 56580043610⟩, ⟨55124422702, 58044450823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 237240320 173178880 174571520 ⟨⟨55890557410, 55890557415⟩, ⟨54439733154, 57350133426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236584960 237240320 174571520 175964160 ⟨⟨56324657331, 56324657336⟩, ⟨54872076276, 57785995607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 170393600 171786240 ⟨⟨54772633267, 54772633270⟩, ⟨53328335573, 56225642764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 237895680 171786240 173178880 ⟨⟨55205268665, 55205268667⟩, ⟨53759217837, 56660036809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238551040 170393600 171786240 ⟨⟨54524168443, 54524168450⟩, ⟨53082867907, 55974151975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237895680 238551040 171786240 173178880 ⟨⟨54954952954, 54954952960⟩, ⟨53511903844, 56406690601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 173178880 174571520 ⟨⟨55637711307, 55637711309⟩, ⟨54189907781, 57094237651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237240320 237895680 174571520 175964160 ⟨⟨56069961651, 56069961654⟩, ⟨54620405861, 57528245749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238551040 173178880 174571520 ⟨⟨55385547146, 55385547151⟩, ⟨53940749882, 56839038476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 174571520 175964160 ⟨⟨55815951467, 55815951474⟩, ⟨54369406473, 57271196053⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 170393600 175964160 t = true :=
  ⟨_, (join_su (m := 237240320) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 171786240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 236584960) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 174571520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 173178880) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 171786240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 237895680) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 174571520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
