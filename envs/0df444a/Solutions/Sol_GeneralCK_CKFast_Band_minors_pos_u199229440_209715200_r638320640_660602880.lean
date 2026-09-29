-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r638320640_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:34.220251+00:00
-- url     : https://prove2.me/submissions/fd140df6-a9cd-465d-a2fc-a9a79e058bae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [487/640, 63/80]` by 15 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 638320640 643891200 ⟨⟨237661852473, 237661852482⟩, ⟨228721902932, 246769461165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 643891200 649461760 ⟨⟨239512156730, 239512156739⟩, ⟨230545546023, 248646170137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 638320640 643891200 ⟨⟨234331690072, 234331690077⟩, ⟨225461772920, 243368653938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 643891200 649461760 ⟨⟨236161673354, 236161673359⟩, ⟨227265034078, 245225131694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 649461760 660602880 ⟨⟨242283699460, 242283699469⟩, ⟨231812146565, 252985478671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201850880 204472320 649461760 655032320 ⟨⟨237989636884, 237989636889⟩, ⟨229066305421, 247079554653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 655032320 660602880 ⟨⟨239815611031, 239815611034⟩, ⟨230865616739, 248931953742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 204472320 207093760 638320640 643891200 ⟨⟨231021795968, 231021795978⟩, ⟨222221200739, 239988817584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 643891200 649461760 ⟨⟨232831361279, 232831361288⟩, ⟨224003994198, 241824955117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207093760 209715200 638320640 643891200 ⟨⟨227731726569, 227731726578⟩, ⟨218999755955, 236629495860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 643891200 649461760 ⟨⟨229520780327, 229520780338⟩, ⟨220761999039, 238445187912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 204472320 207093760 649461760 655032320 ⟨⟨234638978072, 234638978081⟩, ⟨225784866962, 243659111276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 655032320 660602880 ⟨⟨236444675474, 236444675484⟩, ⟨227563847614, 245491315717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 209715200 649461760 655032320 ⟨⟨231307955230, 231307955239⟩, ⟨222522388998, 240258970426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 655032320 660602880 ⟨⟨233093279200, 233093279210⟩, ⟨224280953243, 242070871828⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 638320640 660602880 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 649461760) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 643891200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (leaf_ok cell4) (join_sr (m := 655032320) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 649461760) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 643891200) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 207093760) (by decide) (join_sr (m := 655032320) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 655032320) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (487/640 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
