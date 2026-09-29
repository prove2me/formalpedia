-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:57.523295+00:00
-- url     : https://prove2.me/submissions/72646ae4-dedf-4e3a-b3cc-d7f2941cac67

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [571/2560, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 187105280 188497920 ⟨⟨63816542431, 63816542437⟩, ⟨62306950141, 65335329901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228065280 228720640 188497920 189890560 ⟨⟨64272760710, 64272760716⟩, ⟨62761358838, 65793362641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228720640 229376000 187105280 188497920 ⟨⟨63535501107, 63535501112⟩, ⟨62029172841, 65050993428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 188497920 189890560 ⟨⟨63989849182, 63989849188⟩, ⟨62481715755, 65507151586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 228720640 189890560 191283200 ⟨⟨64728756130, 64728756136⟩, ⟨63215545333, 66251171851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 228065280 228720640 191283200 192675840 ⟨⟨65184529247, 65184529254⟩, ⟨63669510184, 66708758090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228720640 229376000 189890560 191283200 ⟨⟨64443977108, 64443977114⟩, ⟨62934039158, 65963088941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 228720640 229376000 191283200 192675840 ⟨⟨64897885432, 64897885438⟩, ⟨63386143597, 66418806044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 229376000 230031360 187105280 188497920 ⟨⟨63255248158, 63255248163⟩, ⟨61752167955, 64767461496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229376000 230031360 188497920 189890560 ⟨⟨63707729593, 63707729599⟩, ⟨62202848644, 65221748636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230031360 230686720 187105280 188497920 ⟨⟨62975777771, 62975777777⟩, ⟨61475929787, 64484728172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 230031360 230686720 188497920 189890560 ⟨⟨63426396107, 63426396112⟩, ⟨61924751790, 64937147837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 189890560 191283200 ⟨⟨64159993560, 64159993565⟩, ⟨62653312486, 65675817672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230031360 191283200 192675840 ⟨⟨64612040597, 64612040603⟩, ⟨63103560021, 66129669148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 230031360 230686720 189890560 191283200 ⟨⟨63876799628, 63876799635⟩, ⟨62373359584, 65389352072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 191283200 192675840 ⟨⟨64326988869, 64326988874⟩, ⟨62821753698, 65841341409⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 229376000) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 228720640) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 188497920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 228720640) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 191283200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 189890560) (by decide) (join_su (m := 230031360) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 188497920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 230031360) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 191283200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
