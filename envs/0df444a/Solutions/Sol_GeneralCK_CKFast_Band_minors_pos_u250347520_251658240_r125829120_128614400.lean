-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r125829120_128614400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:47:45.629124+00:00
-- url     : https://prove2.me/submissions/3afa0105-0c8d-41c0-b244-b2d67bae092e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [3/20, 157/1024]` by 16 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 125829120 126525440 ⟨⟨37107984957, 37107984964⟩, ⟨36440044749, 37777919511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250347520 250675200 126525440 127221760 ⟨⟨37308860032, 37308860037⟩, ⟨36640501982, 37979213211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250675200 251002880 125829120 126525440 ⟨⟨37019185179, 37019185184⟩, ⟨36351892952, 37688468493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 126525440 127221760 ⟨⟨37219597167, 37219597172⟩, ⟨36551887700, 37889298503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 250675200 127221760 127918080 ⟨⟨37509695033, 37509695039⟩, ⟨36840919162, 38180466814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 250675200 127918080 128614400 ⟨⟨37710490005, 37710490010⟩, ⟨37041296336, 38381680364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250675200 251002880 127221760 127918080 ⟨⟨37419969352, 37419969358⟩, ⟨36751842669, 38090088689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250675200 251002880 127918080 128614400 ⟨⟨37620301780, 37620301785⟩, ⟨36951757901, 38290839094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 251002880 251330560 125829120 126525440 ⟨⟨36930502002, 36930502007⟩, ⟨36263856222, 37599135619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 251002880 251330560 126525440 127221760 ⟨⟨37130451393, 37130451398⟩, ⟨36463388977, 37799502429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251330560 251658240 125829120 126525440 ⟨⟨36841934985, 36841934989⟩, ⟨36175934131, 37509920437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251330560 251658240 126525440 127221760 ⟨⟨37041422269, 37041422270⟩, ⟨36375005380, 37709824540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251330560 127221760 127918080 ⟨⟨37330361251, 37330361257⟩, ⟨36662882221, 37999829688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251330560 127918080 128614400 ⟨⟨37530231622, 37530231627⟩, ⟨36862335998, 38200117437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251330560 251658240 127221760 127918080 ⟨⟨37240870287, 37240870291⟩, ⟨36574037386, 37909689358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251330560 251658240 127918080 128614400 ⟨⟨37440279087, 37440279091⟩, ⟨36773030192, 38109514936⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 125829120 128614400 t = true :=
  ⟨_, (join_su (m := 251002880) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 250675200) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126525440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 250675200) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 127918080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 127221760) (by decide) (join_su (m := 251330560) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126525440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251330560) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 127918080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (157/1024 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
