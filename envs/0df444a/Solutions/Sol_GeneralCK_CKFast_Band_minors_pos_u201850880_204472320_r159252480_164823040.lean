-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:52:45.199313+00:00
-- url     : https://prove2.me/submissions/1d208899-5b4f-4cd8-86e0-cd54d8398fde

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [243/1280, 503/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 159252480 160645120 ⟨⟨65017865809, 65017865815⟩, ⟨63403188547, 66643114077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 202506240 160645120 162037760 ⟨⟨65559401219, 65559401225⟩, ⟨63942704037, 67186672489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 202506240 203161600 159252480 160645120 ⟨⟨64741357199, 64741357205⟩, ⟨63130600251, 66362642826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 160645120 162037760 ⟨⟨65280778909, 65280778916⟩, ⟨63668007053, 66904082596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 202506240 162037760 164823040 ⟨⟨66370996704, 66370996710⟩, ⟨64428553662, 68329056619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 202506240 203161600 162037760 164823040 ⟨⟨66089211975, 66089211980⟩, ⟨64152255631, 68041713799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 203161600 203816960 159252480 160645120 ⟨⟨64465819427, 64465819433⟩, ⟨62858960950, 66083164568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 203816960 160645120 162037760 ⟨⟨65003132699, 65003132704⟩, ⟨63394264322, 66622490960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 203816960 204472320 159252480 160645120 ⟨⟨64191244743, 64191244748⟩, ⟨62588263078, 65804671368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203816960 204472320 160645120 162037760 ⟨⟨64726454803, 64726454810⟩, ⟨63121468244, 66341889611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 203816960 162037760 164823040 ⟨⟨65808411152, 65808411158⟩, ⟨63876912616, 67755384297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203816960 204472320 162037760 163430400 ⟨⟨65261300164, 65261300170⟩, ⟨63654310321, 66878741522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203816960 204472320 163430400 164823040 ⟨⟨65795781861, 65795781867⟩, ⟨64186790340, 67415228141⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 203161600) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 202506240) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 202506240) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 162037760) (by decide) (join_su (m := 203816960) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 203816960) (by decide) (leaf_ok cell10) (join_sr (m := 163430400) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
