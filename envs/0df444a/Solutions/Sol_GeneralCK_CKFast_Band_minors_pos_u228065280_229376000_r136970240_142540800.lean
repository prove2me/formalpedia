-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_229376000_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:59:10.452982+00:00
-- url     : https://prove2.me/submissions/40a17643-1c72-48e2-926e-f498a2e60703

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 35/128]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228392960 136970240 138362880 ⟨⟨47292515550, 47292515556⟩, ⟨46437094399, 48151200444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228392960 228720640 136970240 138362880 ⟨⟨47186436659, 47186436662⟩, ⟨46332118221, 48044011923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228392960 138362880 139755520 ⟨⟨47757632759, 47757632764⟩, ⟨46901209910, 48617320495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228392960 228720640 138362880 139755520 ⟨⟨47650565880, 47650565882⟩, ⟨46795247295, 48509142442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228720640 229048320 136970240 138362880 ⟨⟨47080518963, 47080518969⟩, ⟨46227300622, 47936987244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229048320 229376000 136970240 138362880 ⟨⟨46974761847, 46974761853⟩, ⟨46122640996, 47830125769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228720640 229048320 138362880 139755520 ⟨⟨47543661357, 47543661362⟩, ⟨46689444420, 48401129393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229048320 229376000 138362880 139755520 ⟨⟨47436918571, 47436918577⟩, ⟨46583800672, 48293280708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228392960 139755520 141148160 ⟨⟨48222505420, 48222505426⟩, ⟨47365081423, 49083195446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228392960 228720640 139755520 141148160 ⟨⟨48114452080, 48114452082⟩, ⟨47258133892, 48974029394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228392960 141148160 142540800 ⟨⟨48687134144, 48687134150⟩, ⟨47828709546, 49548825907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228392960 228720640 141148160 142540800 ⟨⟨48578095863, 48578095866⟩, ⟨47720778613, 49438673382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228720640 229048320 139755520 141148160 ⟨⟨48006562249, 48006562254⟩, ⟨47151347251, 48865029500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229048320 229376000 139755520 141148160 ⟨⟨47898835303, 47898835308⟩, ⟨47044720887, 48756195121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228720640 229048320 141148160 142540800 ⟨⟨48469222236, 48469222241⟩, ⟨47613009714, 49328688164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229048320 229376000 141148160 142540800 ⟨⟨48360512635, 48360512641⟩, ⟨47505402230, 49218869603⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 229376000 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 228720640) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229048320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228720640) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228392960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229048320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (35/128 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
