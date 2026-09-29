-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u54525952_56623104_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:58:51.56147+00:00
-- url     : https://prove2.me/submissions/09cc46cd-51d7-426a-945c-99be60b89217

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/200, 27/400]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 54525952 55050240 62914560 65945600 ⟨⟨89865501086, 89865501100⟩, ⟨85071218599, 94758333079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 55050240 55574528 62914560 65945600 ⟨⟨89277137400, 89277137411⟩, ⟨84518187329, 94133304208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 55050240 65945600 68976640 ⟨⟨93481676426, 93481676440⟩, ⟨88679702800, 98380971529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 55050240 55574528 65945600 68976640 ⟨⟨92875448248, 92875448259⟩, ⟨88108688616, 97738227058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 55574528 56098816 62914560 65945600 ⟨⟨88696281052, 88696281066⟩, ⟨83972117514, 93516356515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 56098816 56623104 62914560 65945600 ⟨⟨88122778154, 88122778165⟩, ⟨83432868003, 92907322580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 55574528 56098816 65945600 68976640 ⟨⟨92276869772, 92276869786⟩, ⟨87544784182, 97103699271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 56098816 56623104 65945600 68976640 ⟨⟨91685785772, 91685785784⟩, ⟨86987846758, 96477219687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 55050240 68976640 72007680 ⟨⟨97054269674, 97054269689⟩, ⟨92245253981, 101959395520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 55050240 55574528 68976640 72007680 ⟨⟨96430785148, 96430785159⟩, ⟨91656855092, 101299552850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 54525952 55050240 72007680 75038720 ⟨⟨100584416740, 100584416752⟩, ⟨95768975807, 105494773131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 55050240 55574528 72007680 75038720 ⟨⟨99944259257, 99944259269⟩, ⟨95163766493, 104818424093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 55574528 56098816 68976640 72007680 ⟨⟨95815081836, 95815081850⟩, ⟨91075703533, 100648051402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 56098816 56623104 68976640 72007680 ⟨⟨95207003414, 95207003425⟩, ⟨90501655233, 100004721871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 55574528 56098816 72007680 75038720 ⟨⟨99312004297, 99312004309⟩, ⟨94565932014, 104150530514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 56098816 56623104 72007680 75038720 ⟨⟨98687494657, 98687494669⟩, ⟨93975327177, 103490922492⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 54525952 56623104 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 55574528) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 55050240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 55050240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 56098816) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 56098816) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 55574528) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 55050240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 55050240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 56098816) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 56098816) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/200 : ℝ) (27/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e1 : (((56623104 : ℤ) : ℝ) / (D : ℝ)) = (27/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
