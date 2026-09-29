-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:43.014282+00:00
-- url     : https://prove2.me/submissions/366cb269-a708-426d-8fd6-23f5e4549ce1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 170393600 173178880 ⟨⟨72001156190, 72001156196⟩, ⟨70000204695, 74018311883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 197263360 197918720 170393600 173178880 ⟨⟨71698407161, 71698407166⟩, ⟨69703217677, 73709725910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 196608000 197263360 173178880 175964160 ⟨⟨73111070053, 73111070060⟩, ⟨71105624625, 75132718345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 173178880 175964160 ⟨⟨72804090491, 72804090497⟩, ⟨70804418422, 74819890777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 197918720 198574080 170393600 173178880 ⟨⟨71396739234, 71396739238⟩, ⟨69407280836, 73402252518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 198574080 199229440 170393600 173178880 ⟨⟨71096143749, 71096143756⟩, ⟨69112385782, 73095882778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 173178880 175964160 ⟨⟨72498202236, 72498202240⟩, ⟨70504272610, 74508185978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 198574080 199229440 173178880 175964160 ⟨⟨72193396570, 72193396576⟩, ⟨70205178741, 74197594966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197263360 175964160 178749440 ⟨⟨74219374207, 74219374213⟩, ⟨72209445207, 76245504621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197263360 197918720 175964160 178749440 ⟨⟨73908182234, 73908182240⟩, ⟨71904037767, 75928453752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197263360 178749440 181534720 ⟨⟨75326078148, 75326078155⟩, ⟨73311675865, 77356680286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197263360 197918720 178749440 181534720 ⟨⟨75010691745, 75010691753⟩, ⟨73002085000, 77035424269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 197918720 198574080 175964160 178749440 ⟨⟨73598091595, 73598091597⟩, ⟨71599700758, 75612535664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 198574080 199229440 175964160 178749440 ⟨⟨73289093513, 73289093518⟩, ⟨71296425672, 75297741314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 198574080 178749440 181534720 ⟨⟨74696416524, 74696416529⟩, ⟨72693574428, 76715310861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 198574080 199229440 178749440 181534720 ⟨⟨74383243655, 74383243662⟩, ⟨72386135583, 76396330972⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 197263360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 198574080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 197918720) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 197263360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 198574080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
