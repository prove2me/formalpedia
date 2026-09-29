-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_175636480_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.276476+00:00
-- url     : https://prove2.me/submissions/ed345bbf-ddb9-4c61-8f0e-79a2df4837f7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 67/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 173670400 125829120 127221760 ⟨⟨62720753554, 62720753561⟩, ⟨60963598728, 64490730439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 173670400 127221760 128614400 ⟨⟨63376533005, 63376533012⟩, ⟨61617048654, 65148838847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173670400 174325760 125829120 127221760 ⟨⟨62451727754, 62451727760⟩, ⟨60699540007, 64216674355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 173670400 174325760 127221760 128614400 ⟨⟨63104955197, 63104955204⟩, ⟨61350444174, 64872224640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 173670400 128614400 130007040 ⟨⟨64031639664, 64031639670⟩, ⟨62269829738, 65806270483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 173670400 130007040 131399680 ⟨⟨64686075865, 64686075871⟩, ⟨62921944291, 66463027693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173670400 174325760 128614400 130007040 ⟨⟨63757517451, 63757517457⟩, ⟨62000687036, 65527105819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 173670400 174325760 130007040 131399680 ⟨⟨64409416811, 64409416818⟩, ⟨62650270873, 66181320201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 174325760 174981120 125829120 127221760 ⟨⟨62183920404, 62183920411⟩, ⟨60436667140, 63943869875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 174325760 174981120 127221760 128614400 ⟨⟨62834604485, 62834604493⟩, ⟨61085034188, 64596870688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 174981120 175636480 125829120 127221760 ⟨⟨61917320391, 61917320394⟩, ⟨60174969332, 63672305553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 174981120 175636480 127221760 128614400 ⟨⟨62565469700, 62565469703⟩, ⟨60820807844, 64322765483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 174325760 174981120 128614400 130007040 ⟨⟨63484630899, 63484630906⟩, ⟨61732747390, 65249209976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 174325760 174981120 130007040 131399680 ⟨⟨64134001904, 64134001912⟩, ⟨62379808993, 65900890013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 174981120 175636480 128614400 130007040 ⟨⟨63212968778, 63212968781⟩, ⟨61465999890, 64972571389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 174981120 175636480 130007040 131399680 ⟨⟨63859819854, 63859819858⟩, ⟨62110547679, 65621725510⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 175636480 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 174325760) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 173670400) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 173670400) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 174981120) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 127221760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 174981120) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (67/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
