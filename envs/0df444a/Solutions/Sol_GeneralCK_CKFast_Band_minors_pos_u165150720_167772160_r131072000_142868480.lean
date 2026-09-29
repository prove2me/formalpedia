-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:32.427191+00:00
-- url     : https://prove2.me/submissions/e0c2fb7e-11e7-4050-abe6-a5f7233c0b3e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [5/32, 109/640]` by 20 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 131072000 132546560 ⟨⟨68651199218, 68651199223⟩, ⟨66798122713, 70518285268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 132546560 134021120 ⟨⟨69375613228, 69375613232⟩, ⟨67519991984, 71245240990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 131072000 132546560 ⟨⟨68356585669, 68356585677⟩, ⟨66509038364, 70218070175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 132546560 134021120 ⟨⟨69078217336, 69078217342⟩, ⟨67228131711, 70942237316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 134021120 136970240 ⟨⟨70460637767, 70460637772⟩, ⟨68158854680, 72784209610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165806080 166461440 134021120 136970240 ⟨⟨70159086199, 70159086205⟩, ⟨67865019823, 72474817199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 166461440 167116800 131072000 132546560 ⟨⟨68063370096, 68063370102⟩, ⟨66221314446, 69919291256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167116800 132546560 134021120 ⟨⟨68782229003, 68782229010⟩, ⟨66937641458, 70640679391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167116800 167772160 131072000 132546560 ⟨⟨67771539402, 67771539410⟩, ⟨65934938249, 69621935020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 167116800 167772160 132546560 134021120 ⟨⟨68487635070, 68487635076⟩, ⟨66648508449, 70340553662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167116800 134021120 136970240 ⟨⟨69858956374, 69858956380⟩, ⟨67572556445, 72166897916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167772160 134021120 136970240 ⟨⟨69560235035, 69560235043⟩, ⟨67281451806, 71860437975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 165806080 136970240 139919360 ⟨⟨71904374310, 71904374312⟩, ⟨69596904108, 74233610229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165806080 166461440 136970240 139919360 ⟨⟨71597314866, 71597314872⟩, ⟨69297576255, 73918695738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 165806080 139919360 142868480 ⟨⟨73344748645, 73344748650⟩, ⟨71031619376, 75679620407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165806080 166461440 139919360 142868480 ⟨⟨73032218703, 73032218711⟩, ⟨70726835488, 75359221623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 166461440 167116800 136970240 139919360 ⟨⟨71291695726, 71291695732⟩, ⟨68999638468, 73605272892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 167116800 167772160 136970240 139919360 ⟨⟨70987503507, 70987503514⟩, ⟨68703077883, 73293327783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 166461440 167116800 139919360 142868480 ⟨⟨72721147224, 72721147231⟩, ⟨70423459865, 75040332596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 167116800 167772160 139919360 142868480 ⟨⟨72411520705, 72411520713⟩, ⟨70121479514, 74722939304⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 132546560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132546560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 134021120) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 132546560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 132546560) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 167116800) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 166461440) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 165806080) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 139919360) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 167116800) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
