-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:51:57.10642+00:00
-- url     : https://prove2.me/submissions/60c3566e-6349-4a7b-b294-95fd4bfa9b19

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [71/256, 49/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 232652800 238714880 ⟨⟨222852195808, 222852195822⟩, ⟨210504121164, 235585570470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 69206016 238714880 244776960 ⟨⟨227094018052, 227094018066⟩, ⟨214742565727, 239824475842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 71303168 232652800 238714880 ⟨⟨219343244352, 219343244363⟩, ⟨207208457664, 231853836680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 238714880 244776960 ⟨⟨223554077609, 223554077623⟩, ⟨211413640858, 236064385923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 69206016 244776960 250839040 ⟨⟨231291576664, 231291576678⟩, ⟨218937458344, 244018517728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 69206016 250839040 256901120 ⟨⟨235446174669, 235446174683⟩, ⟨223090056935, 248169041637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69206016 71303168 244776960 250839040 ⟨⟨227721866095, 227721866106⟩, ⟨215576500558, 240231269626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 69206016 71303168 250839040 256901120 ⟨⟨231847855180, 231847855194⟩, ⟨219698238579, 244355774509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 73400320 232652800 238714880 ⟨⟨215925511269, 215925511282⟩, ⟨203996634860, 228221062507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71303168 73400320 238714880 244776960 ⟨⟨220104886918, 220104886931⟩, ⟨208168258272, 232402594278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 73400320 75497472 232652800 238714880 ⟨⟨212594889808, 212594889821⟩, ⟨200864927993, 224682741409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 73400320 75497472 238714880 244776960 ⟨⟨216742402038, 216742402052⟩, ⟨205002743163, 228834671682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 73400320 244776960 250839040 ⟨⟨224242411011, 224242411022⟩, ⟨212298757310, 236541637579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 71303168 73400320 250839040 256901120 ⟨⟨228339273796, 228339273810⟩, ⟨216389280237, 240639422780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 73400320 75497472 244776960 250839040 ⟨⟨220849229875, 220849229886⟩, ⟨209100603802, 232945268687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 73400320 75497472 250839040 256901120 ⟨⟨224916510872, 224916510883⟩, ⟨213159607062, 237015708817⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 71303168) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 238714880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 69206016) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 250839040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 244776960) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 238714880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 73400320) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 250839040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
