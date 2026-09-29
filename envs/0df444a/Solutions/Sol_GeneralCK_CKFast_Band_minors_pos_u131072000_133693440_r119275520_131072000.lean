-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:07:46.78128+00:00
-- url     : https://prove2.me/submissions/237685fa-fa05-408c-9ea9-45d786578781

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 119275520 122224640 ⟨⟨79607959641, 79607959650⟩, ⟨76852537976, 82394003424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131727360 132382720 119275520 122224640 ⟨⟨79243521777, 79243521785⟩, ⟨76499311399, 82018137256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 131727360 122224640 125173760 ⟨⟨81397955474, 81397955482⟩, ⟨78635878792, 84190574794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131727360 132382720 122224640 125173760 ⟨⟨81026504334, 81026504341⟩, ⟨78275652066, 83807683922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 132382720 133038080 119275520 122224640 ⟨⟨78881355575, 78881355580⟩, ⟨76148264585, 81644637077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133038080 133693440 119275520 122224640 ⟨⟨78521435367, 78521435375⟩, ⟨75799373039, 81273476021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 132382720 133038080 122224640 125173760 ⟨⟨80657355143, 80657355144⟩, ⟨77917635577, 83427189104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133038080 133693440 122224640 125173760 ⟨⟨80290482004, 80290482011⟩, ⟨77561804601, 83049063256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 131727360 125173760 128122880 ⟨⟨83181647454, 83181647461⟩, ⟨80412978633, 85980779278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131727360 132382720 125173760 128122880 ⟨⟨82803254568, 82803254577⟩, ⟨80045822408, 85590936110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 131727360 128122880 131072000 ⟨⟨84959098571, 84959098580⟩, ⟨82183899560, 87764680810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 131727360 132382720 128122880 131072000 ⟨⟨84573834433, 84573834441⟩, ⟨81809883467, 87367956696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133038080 125173760 128122880 ⟨⟨82427193067, 82427193072⟩, ⟨79680906060, 85203518201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133038080 133693440 125173760 128122880 ⟨⟨82053436848, 82053436855⟩, ⟨79318204641, 84818498262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 132382720 133038080 128122880 131072000 ⟨⟨84190930286, 84190930292⟩, ⟨81438136069, 86973686204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133038080 133693440 128122880 131072000 ⟨⟨83810359829, 83810359836⟩, ⟨81068632214, 86581841853⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 132382720) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 131727360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133038080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 132382720) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 131727360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133038080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
