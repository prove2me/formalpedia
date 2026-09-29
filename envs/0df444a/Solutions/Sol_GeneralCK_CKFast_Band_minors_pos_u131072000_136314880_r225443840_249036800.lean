-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_136314880_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:42:47.122735+00:00
-- url     : https://prove2.me/submissions/74f0ecbf-af58-43e1-9a70-a39ee2f0577f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 13/80]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 132382720 225443840 231342080 ⟨⟨140991747585, 140991747593⟩, ⟨135103210094, 146990622275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 132382720 133693440 225443840 231342080 ⟨⟨139835976106, 139835976114⟩, ⟨133991774303, 145789257954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 132382720 231342080 237240320 ⟨⟨144173246566, 144173246575⟩, ⟨138265168411, 150191014804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 132382720 133693440 231342080 237240320 ⟨⟨142997752403, 142997752411⟩, ⟨137133944983, 148970016061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 133693440 135004160 225443840 231342080 ⟨⟨138691803040, 138691803044⟩, ⟨132891313260, 144600137985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135004160 136314880 225443840 231342080 ⟨⟨137559006717, 137559006725⟩, ⟨131801618720, 143423026753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 133693440 135004160 231342080 237240320 ⟨⟨141833924621, 141833924623⟩, ⟨136013770558, 147761322626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135004160 136314880 231342080 237240320 ⟨⟨140681541988, 140681541996⟩, ⟨134904437081, 146564699603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 132382720 237240320 243138560 ⟨⟨147337226027, 147337226035⟩, ⟨141409900583, 153373594605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133693440 237240320 243138560 ⟨⟨146142345896, 146142345904⟩, ⟨140259220158, 152133304027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 132382720 243138560 249036800 ⟨⟨150484003496, 150484003504⟩, ⟨144537716315, 156538687109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 132382720 133693440 243138560 249036800 ⟨⟨149270065375, 149270065385⟩, ⟨143367901058, 155279438276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 133693440 135004160 237240320 243138560 ⟨⟨144959194109, 144959194112⟩, ⟨139119657059, 150905373652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 135004160 136314880 237240320 243138560 ⟨⟨143787549984, 143787549992⟩, ⟨137991003531, 149689569404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 135004160 243138560 249036800 ⟨⟨148067911803, 148067911809⟩, ⟨142209265759, 154032598734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 135004160 136314880 243138560 249036800 ⟨⟨146877322747, 146877322755⟩, ⟨141061603059, 152797935323⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 136314880 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 132382720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 135004160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 133693440) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 132382720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 135004160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
