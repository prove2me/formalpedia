-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:17:49.237907+00:00
-- url     : https://prove2.me/submissions/ce8ab408-8185-4edd-847f-383b4ebe486f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [73/640, 31/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 95682560 97157120 ⟨⟨52841789930, 52841789938⟩, ⟨51007273703, 54691015341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 160563200 97157120 98631680 ⟨⟨53612354447, 53612354454⟩, ⟨51775087827, 55464326801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 160563200 161218560 95682560 97157120 ⟨⟨52607452045, 52607452053⟩, ⟨50778598645, 54450931835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 97157120 98631680 ⟨⟨53374887133, 53374887139⟩, ⟨51543292061, 55221105342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 160563200 98631680 100106240 ⟨⟨54381891499, 54381891506⟩, ⟨52541881319, 56236603913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159907840 160563200 100106240 101580800 ⟨⟨55150405297, 55150405304⟩, ⟨53307658355, 57007850923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 161218560 98631680 100106240 ⟨⟨54141306676, 54141306682⟩, ⟨52306976661, 55990256529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160563200 161218560 100106240 101580800 ⟨⟨54906714818, 54906714824⟩, ⟨53069656553, 56758389572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 95682560 97157120 ⟨⟨52374343371, 52374343379⟩, ⟨50551112088, 54212119059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 161873920 97157120 98631680 ⟨⟨53138662173, 53138662180⟩, ⟨51312697923, 54979167776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162529280 95682560 97157120 ⟨⟨52142451568, 52142451571⟩, ⟨50324802140, 53974564217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161873920 162529280 97157120 98631680 ⟨⟨52903667125, 52903667127⟩, ⟨51083293409, 54738501197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 98631680 100106240 ⟨⟨53901977216, 53901977222⟩, ⟨52073286619, 55745206061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 161873920 100106240 101580800 ⟨⟨54664292573, 54664292580⟩, ⟨52832882216, 56510238026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162529280 98631680 100106240 ⟨⟨53663890568, 53663890571⟩, ⟨51840799083, 55501439501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 100106240 101580800 ⟨⟨54423125906, 54423125909⟩, ⟨52597323133, 56263383168⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 161218560) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 160563200) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 97157120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161873920) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
