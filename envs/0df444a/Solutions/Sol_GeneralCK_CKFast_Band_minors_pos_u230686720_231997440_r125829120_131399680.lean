-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_231997440_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:15:46.212514+00:00
-- url     : https://prove2.me/submissions/39fe06b1-fbad-4c3f-b939-df0e6cdb043b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 177/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231014400 125829120 127221760 ⟨⟨42781957610, 42781957615⟩, ⟨41943218228, 43623896296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231014400 231342080 125829120 127221760 ⟨⟨42685034739, 42685034744⟩, ⟨41847364894, 43525897104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231014400 127221760 128614400 ⟨⟨43241084362, 43241084368⟩, ⟨42401351612, 44084017653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231014400 231342080 127221760 128614400 ⟨⟨43143170815, 43143170821⟩, ⟨42304509190, 43985026205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231342080 231669760 125829120 127221760 ⟨⟨42588258843, 42588258850⟩, ⟨41751656014, 43428047434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231669760 231997440 125829120 127221760 ⟨⟨42491629359, 42491629362⟩, ⟨41656091035, 43330346704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231669760 127221760 128614400 ⟨⟨43045405439, 43045405445⟩, ⟨42207812414, 43886185476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231669760 231997440 127221760 128614400 ⟨⟨42947787663, 42947787666⟩, ⟨42111260727, 43787494878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231014400 128614400 130007040 ⟨⟨43699973949, 43699973955⟩, ⟨42859248341, 44543901333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231014400 231342080 128614400 130007040 ⟨⟨43601071226, 43601071232⟩, ⟨42761418324, 44443919135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231014400 130007040 131399680 ⟨⟨44158626949, 44158626956⟩, ⟨43316908989, 45003547915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231014400 231342080 130007040 131399680 ⟨⟨44058736547, 44058736554⟩, ⟨43218092868, 44902576469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231342080 231669760 128614400 130007040 ⟨⟨43502317861, 43502317867⟩, ⟨42663735138, 44344088843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231669760 231997440 128614400 130007040 ⟨⟨43403713278, 43403713281⟩, ⟨42566198220, 44244409868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231342080 231669760 130007040 131399680 ⟨⟨43958996680, 43958996686⟩, ⟨43119424752, 44801758109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 231669760 231997440 130007040 131399680 ⟨⟨43859406770, 43859406773⟩, ⟨43020904079, 44701092241⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 231997440 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231014400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 231669760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231342080) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231014400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 231669760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (177/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
