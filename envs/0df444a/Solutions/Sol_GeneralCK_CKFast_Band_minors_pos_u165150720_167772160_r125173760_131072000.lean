-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:58.977711+00:00
-- url     : https://prove2.me/submissions/afd4beb6-f941-4bbf-a2e7-ecd61ad5d73c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [191/1280, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 125173760 126648320 ⟨⟨65744956777, 65744956782⟩, ⟨63902113214, 67601821563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 126648320 128122880 ⟨⟨66472812026, 66472812028⟩, ⟨64627402075, 68332240340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 125173760 126648320 ⟨⟨65461568865, 65461568873⟩, ⟨63624228002, 67312857886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 126648320 128122880 ⟨⟨66186603160, 66186603166⟩, ⟨64346702660, 68040449140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 128122880 129597440 ⟨⟨67199801947, 67199801952⟩, ⟨65351831064, 69061788299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 165806080 129597440 131072000 ⟨⟨67925929899, 67925929903⟩, ⟨66075403506, 69790468820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166461440 128122880 129597440 ⟨⟨66910781859, 66910781867⟩, ⟨65068327092, 68767179390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165806080 166461440 129597440 131072000 ⟨⟨67634108268, 67634108274⟩, ⟨65789104572, 69493051966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 167116800 125173760 126648320 ⟨⟨65179539547, 65179539555⟩, ⟨63347663830, 67025291020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166461440 167116800 126648320 128122880 ⟨⟨65901762892, 65901762898⟩, ⟨64067334287, 67750064752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167116800 167772160 125173760 126648320 ⟨⟨64898856002, 64898856010⟩, ⟨63072408265, 66739107750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167772160 126648320 128122880 ⟨⟨65618278329, 65618278335⟩, ⟨63789284456, 67461073890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 128122880 129597440 ⟨⟨66623140267, 66623140274⟩, ⟨64786164063, 68473987188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167116800 129597440 131072000 ⟨⟨67343674924, 67343674930⟩, ⟨65504156379, 69197061603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167772160 128122880 129597440 ⟨⟨66336864208, 66336864215⟩, ⟨64505329404, 68182198334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 129597440 131072000 ⟨⟨67054616837, 67054616845⟩, ⟨65220546281, 68902484308⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 166461440) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126648320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (join_sr (m := 129597440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 129597440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128122880) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126648320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 167116800) (by decide) (join_sr (m := 129597440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 129597440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
