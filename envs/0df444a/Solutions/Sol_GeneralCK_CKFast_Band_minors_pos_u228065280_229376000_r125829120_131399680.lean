-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_229376000_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:56:36.180777+00:00
-- url     : https://prove2.me/submissions/1bdcc038-bf96-4cd1-8ba7-749dc32ad38c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 35/128]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228392960 125829120 127221760 ⟨⟨43562700834, 43562700839⟩, ⟨42715313228, 44413342872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228392960 228720640 125829120 127221760 ⟨⟨43464581370, 43464581373⟩, ⟨42618283822, 44314126371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228392960 127221760 128614400 ⟨⟨44029796459, 44029796465⟩, ⟨43181402704, 44881445824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228392960 228720640 127221760 128614400 ⟨⟨43930676623, 43930676625⟩, ⟨43083374532, 44781227352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228720640 229048320 125829120 127221760 ⟨⟨43366613522, 43366613527⟩, ⟨42521403433, 44215064116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229048320 229376000 125829120 127221760 ⟨⟨43268796703, 43268796710⟩, ⟨42424671486, 44116155501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228720640 229048320 127221760 128614400 ⟨⟨43831709628, 43831709633⟩, ⟨42985496599, 44681164355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229048320 229376000 127221760 128614400 ⟨⟨43732894886, 43732894891⟩, ⟨42887768328, 44581256223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228392960 128614400 130007040 ⟨⟨44496642625, 44496642630⟩, ⟨43647243285, 45349298750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228392960 228720640 128614400 130007040 ⟨⟨44396523980, 44396523983⟩, ⟨43548217903, 45248079880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228392960 130007040 131399680 ⟨⟨44963239950, 44963239956⟩, ⟨44112835584, 45816902272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228392960 228720640 130007040 131399680 ⟨⟨44862124060, 44862124062⟩, ⟨44012814547, 45714684572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228720640 229048320 128614400 130007040 ⟨⟨44296559397, 44296559402⟩, ⟨43449343976, 45147017705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229048320 229376000 128614400 130007040 ⟨⟨44196748279, 44196748284⟩, ⟨43350620924, 45046111611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228720640 229048320 130007040 131399680 ⟨⟨44761163438, 44761163444⟩, ⟨43912946173, 45612624778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229048320 229376000 130007040 131399680 ⟨⟨44660357489, 44660357495⟩, ⟨43813229877, 45510722273⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 229376000 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 228720640) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229048320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228720640) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228392960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229048320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (35/128 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
