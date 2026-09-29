-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:37:55.777217+00:00
-- url     : https://prove2.me/submissions/e70eabcb-b8bf-45e9-8f03-0643243a02e1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [103/256, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 337510400 340295680 ⟨⟨110019566710, 110019566715⟩, ⟨106656786498, 113420472966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 340295680 343080960 ⟨⟨110874936088, 110874936095⟩, ⟨107505222833, 114282804721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 337510400 340295680 ⟨⟨109090236229, 109090236233⟩, ⟨105741696023, 112476700781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 340295680 343080960 ⟨⟨109939149682, 109939149686⟩, ⟨106583698947, 113332554952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 343080960 345866240 ⟨⟨111729665654, 111729665661⟩, ⟨108353022701, 115144493108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 345866240 348651520 ⟨⟨112583758734, 112583758740⟩, ⟨109200189407, 116005541473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 343080960 345866240 ⟨⟨110787437981, 110787437984⟩, ⟨107425079859, 114187780621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 345866240 348651520 ⟨⟨111635104360, 111635104363⟩, ⟨108265841976, 115042381042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 337510400 340295680 ⟨⟨108164915189, 108164915195⟩, ⟨104830498884, 111537056159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 340295680 343080960 ⟨⟨109007382445, 109007382451⟩, ⟨105666078368, 112386442211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235929600 337510400 340295680 ⟨⟨107243550998, 107243551006⟩, ⟨103923143957, 110601485007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 340295680 343080960 ⟨⟨108079581755, 108079581763⟩, ⟨104752309938, 111444412382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 343080960 345866240 ⟨⟨109849238948, 109849238955⟩, ⟨106501050048, 113235214365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 345866240 348651520 ⟨⟨110690487846, 110690487853⟩, ⟨107335417043, 114083375789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 343080960 345866240 ⟨⟨108915015913, 108915015919⟩, ⟨105580882070, 112286740212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 345866240 348651520 ⟨⟨109749856527, 109749856535⟩, ⟨106408863389, 113128471571⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 340295680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 345866240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 343080960) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 340295680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 234618880) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 345866240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
