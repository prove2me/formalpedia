-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:55:59.584844+00:00
-- url     : https://prove2.me/submissions/3e56863f-6ada-4e00-b94f-48fcd838eaaa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 571473920 577044480 ⟨⟨186108823297, 186108823299⟩, ⟨181497588863, 190774999268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 571473920 577044480 ⟨⟨184660693683, 184660693692⟩, ⟨180071169631, 189304941833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 577044480 582615040 ⟨⟨187776268176, 187776268180⟩, ⟨183150770662, 192456686724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 577044480 582615040 ⟨⟨186317193981, 186317193989⟩, ⟨181713422212, 190975673050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 571473920 577044480 ⟨⟨183216871437, 183216871446⟩, ⟨178648938742, 187839311292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229376000 230686720 571473920 577044480 ⟨⟨181777307562, 181777307571⟩, ⟨177230848303, 186378057564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228065280 229376000 577044480 582615040 ⟨⟨184862414930, 184862414938⟩, ⟨180280251127, 189499072740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 577044480 582615040 ⟨⟨183411882312, 183411882321⟩, ⟨178851209777, 188026836018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226754560 582615040 588185600 ⟨⟨189442005604, 189442005608⟩, ⟨184802257985, 194136652536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 228065280 582615040 588185600 ⟨⟨187972021815, 187972021823⟩, ⟨183354014679, 192644718257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226754560 588185600 593756160 ⟨⟨191106057759, 191106057763⟩, ⟨186452072782, 195814919115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226754560 228065280 588185600 593756160 ⟨⟨189625198845, 189625198854⟩, ⟨184992968470, 194312099337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 582615040 588185600 ⟨⟨186506320467, 186506320476⟩, ⟨181909937288, 191157183323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 582615040 588185600 ⟨⟨185044853136, 185044853145⟩, ⟨180469978441, 189673998264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 229376000 588185600 593756160 ⟨⟨188148609199, 188148609207⟩, ⟨183538018155, 192813664402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 588185600 593756160 ⟨⟨186676240681, 186676240689⟩, ⟨182087174733, 191319565157⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 571473920 593756160 t = true :=
  ⟨_, (join_sr (m := 582615040) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 577044480) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 577044480) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229376000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228065280) (by decide) (join_sr (m := 588185600) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226754560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 588185600) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229376000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
