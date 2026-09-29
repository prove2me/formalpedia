-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u224133120_225443840_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:44:35.927497+00:00
-- url     : https://prove2.me/submissions/e383d9c5-f93c-4200-9593-53632b616c97

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [171/640, 43/160]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 224133120 224460800 125829120 127221760 ⟨⟨44752178843, 44752178850⟩, ⟨43891503876, 45616193873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 224460800 224788480 125829120 127221760 ⟨⟨44652193007, 44652193013⟩, ⟨43792640124, 45515078677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 224133120 224460800 127221760 128614400 ⟨⟨45231376102, 45231376107⟩, ⟨44369675560, 46096417790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 224460800 224788480 127221760 128614400 ⟨⟨45130374853, 45130374858⟩, ⟨44269798025, 45994285559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224788480 225116160 125829120 127221760 ⟨⟨44552366072, 44552366078⟩, ⟨43693932544, 45414125138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225116160 225443840 125829120 127221760 ⟨⟨44452697419, 44452697422⟩, ⟨43595380531, 45313332618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224788480 225116160 127221760 128614400 ⟨⟨45029533782, 45029533787⟩, ⟨44170077938, 45892316264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 225116160 225443840 127221760 128614400 ⟨⟨44928852265, 44928852267⟩, ⟨44070514687, 45790509261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224460800 128614400 130007040 ⟨⟨45710304451, 45710304457⟩, ⟨44847578980, 46576372149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224460800 224788480 128614400 130007040 ⟨⟨45608289458, 45608289463⟩, ⟨44746689325, 46473224558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 224460800 130007040 131399680 ⟨⟨46188964574, 46188964579⟩, ⟨45325214817, 47056057632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224460800 224788480 130007040 131399680 ⟨⟨46085937500, 46085937506⟩, ⟨45223314697, 46951896353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224788480 225116160 128614400 130007040 ⟨⟨45506435911, 45506435917⟩, ⟨44645958383, 46370241173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225116160 225443840 128614400 130007040 ⟨⟨45404743181, 45404743184⟩, ⟨44545385539, 46267421347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225116160 130007040 131399680 ⟨⟨45983073131, 45983073137⟩, ⟨45121574548, 46847900540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 225116160 225443840 130007040 131399680 ⟨⟨45880370834, 45880370836⟩, ⟨45019993748, 46744069543⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 224133120 225443840 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 224460800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 225116160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224788480) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 224460800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 225116160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (171/640 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
