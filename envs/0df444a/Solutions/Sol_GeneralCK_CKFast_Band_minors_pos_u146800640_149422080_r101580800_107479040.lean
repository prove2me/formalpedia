-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:00:55.766259+00:00
-- url     : https://prove2.me/submissions/01d8beaf-da8d-4c31-9963-9dfe0f682c08

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 101580800 103055360 ⟨⟨61143842403, 61143842409⟩, ⟨59175112723, 63129092292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 147456000 103055360 104529920 ⟨⟨61974774657, 61974774665⟩, ⟨60003153312, 63962907651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 147456000 148111360 101580800 103055360 ⟨⟨60868475755, 60868475763⟩, ⟨58906363194, 62847008075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147456000 148111360 103055360 104529920 ⟨⟨61696051225, 61696051231⟩, ⟨59731055488, 63677458452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 147456000 104529920 106004480 ⟨⟨62804432162, 62804432168⟩, ⟨60829928266, 64795439087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 147456000 106004480 107479040 ⟨⟨63632820661, 63632820669⟩, ⟨61655443274, 65626692404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 147456000 148111360 104529920 106004480 ⟨⟨62522366679, 62522366685⟩, ⟨60554496743, 64506639778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 147456000 148111360 106004480 107479040 ⟨⟨63347427769, 63347427775⟩, ⟨61376692555, 65334557763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 148111360 148766720 101580800 103055360 ⟨⟨60594685029, 60594685037⟩, ⟨58639138361, 62566552063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 148766720 103055360 104529920 ⟨⟨61418918539, 61418918546⟩, ⟨59460497182, 63393652278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 148766720 149422080 101580800 103055360 ⟨⟨60322453460, 60322453465⟩, ⟨58373422057, 62287706866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148766720 149422080 103055360 104529920 ⟨⟨61143359711, 61143359716⟩, ⟨59191462101, 63111471621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 148111360 148766720 104529920 106004480 ⟨⟨62241906592, 62241906599⟩, ⟨60280619385, 64219498140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 148111360 148766720 106004480 107479040 ⟨⟨63063654749, 63063654755⟩, ⟨61099510479, 65044095261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148766720 149422080 104529920 106004480 ⟨⟨61963034896, 61963034897⟩, ⟨60008279782, 63933996545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148766720 149422080 106004480 107479040 ⟨⟨62781484476, 62781484480⟩, ⟨60823880517, 64755287158⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 148111360) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 147456000) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 147456000) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 148766720) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 148766720) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
