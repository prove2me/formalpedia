-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:57:58.667444+00:00
-- url     : https://prove2.me/submissions/b4cddad3-7212-449c-b9a9-27e1e42694e1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [23/40, 77/128]` by 18 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 482344960 487915520 ⟨⟨184867924374, 184867924383⟩, ⟨176690109698, 193218523870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 487915520 493486080 ⟨⟨186790637825, 186790637832⟩, ⟨178584999310, 195168945346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 482344960 487915520 ⟨⟨182141980469, 182141980473⟩, ⟨174034893709, 190420463861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 487915520 493486080 ⟨⟨184041751889, 184041751892⟩, ⟨175906855143, 192347956058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 493486080 499056640 ⟨⟨188710272051, 188710272060⟩, ⟨180476860675, 197116231686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 499056640 504627200 ⟨⟨190626866160, 190626866167⟩, ⟨182365732151, 199060422745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 493486080 499056640 ⟨⟨185938559280, 185938559284⟩, ⟨177775900276, 194272431654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 499056640 504627200 ⟨⟨187832439977, 187832439981⟩, ⟨179642065741, 196193928683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 482344960 487915520 ⟨⟨179438194163, 179438194171⟩, ⟨171400823243, 187645590183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 487915520 493486080 ⟨⟨181314990224, 181314990231⟩, ⟨173249833301, 189550108683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 208404480 482344960 487915520 ⟨⟨177424573932, 177424573941⟩, ⟨172728964912, 182179310281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 208404480 209715200 482344960 487915520 ⟨⟨176088809121, 176088809129⟩, ⟨171416666643, 180819780669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 487915520 493486080 ⟨⟨179284118309, 179284118317⟩, ⟨174573762997, 184053542978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 487915520 493486080 ⟨⟨177936843409, 177936843416⟩, ⟨173249963118, 182682499374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 204472320 207093760 493486080 499056640 ⟨⟨183188934398, 183188934407⟩, ⟨175096036018, 191451726006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 204472320 207093760 499056640 504627200 ⟨⟨185060062322, 185060062331⟩, ⟨176939466367, 193350478437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 207093760 209715200 493486080 499056640 ⟨⟨180460869688, 180460869696⟩, ⟨172436762763, 188653564336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 207093760 209715200 499056640 504627200 ⟨⟨182309208392, 182309208400⟩, ⟨174257431414, 190529524944⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 482344960 504627200 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 493486080) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 487915520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 499056640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 493486080) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 487915520) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 208404480) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 207093760) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 499056640) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
