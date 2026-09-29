-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r128614400_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:42:48.984374+00:00
-- url     : https://prove2.me/submissions/1e4a7423-c15b-4c7f-9de1-b89e4a1e8807

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [157/1024, 401/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 128614400 129310720 ⟨⟨38640771093, 38640771100⟩, ⟨37965900629, 39317665454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 248053760 129310720 130007040 ⟨⟨38845199789, 38845199795⟩, ⟨38169906740, 39522517508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 248053760 248381440 128614400 129310720 ⟨⟨38549155871, 38549155873⟩, ⟨37874948269, 39225384025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 129310720 130007040 ⟨⟨38753118631, 38753118633⟩, ⟨38078489050, 39429769537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248053760 130007040 131399680 ⟨⟨39151763887, 39151763892⟩, ⟨38362761463, 39943646130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248053760 248381440 130007040 131399680 ⟨⟨39058984354, 39058984357⟩, ⟨38270936769, 39849906065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 128614400 129310720 ⟨⟨38457662838, 38457662843⟩, ⟨37784116520, 39133226381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248381440 248709120 129310720 130007040 ⟨⟨38661160159, 38661160165⟩, ⟨37987192470, 39337145849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 248709120 249036800 128614400 129310720 ⟨⟨38366291538, 38366291543⟩, ⟨37693404934, 39041192049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248709120 249036800 129310720 130007040 ⟨⟨38569323918, 38569323923⟩, ⟨37896016545, 39244645971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 248709120 130007040 131399680 ⟨⟨38966328251, 38966328258⟩, ⟨38179233428, 39756291534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248709120 249036800 130007040 130703360 ⟨⟨38772315027, 38772315032⟩, ⟨38098586914, 39448058595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248709120 249036800 130703360 131399680 ⟨⟨38975264911, 38975264917⟩, ⟨38301116085, 39651429969⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 128614400 131399680 t = true :=
  ⟨_, (join_su (m := 248381440) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 248053760) (by decide) (join_sr (m := 129310720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 129310720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 248053760) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 130007040) (by decide) (join_su (m := 248709120) (by decide) (join_sr (m := 129310720) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 129310720) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 248709120) (by decide) (leaf_ok cell10) (join_sr (m := 130703360) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (157/1024 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
