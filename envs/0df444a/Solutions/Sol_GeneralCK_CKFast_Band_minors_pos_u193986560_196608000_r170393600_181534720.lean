-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:20.213173+00:00
-- url     : https://prove2.me/submissions/909b15ea-0504-4b24-a54e-95306c20a982

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 170393600 173178880 ⟨⟨73223139508, 73223139514⟩, ⟨71198825330, 75263963276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 194641920 195297280 170393600 173178880 ⟨⟨72915977761, 72915977764⟩, ⟨70897551995, 74950835904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 194641920 173178880 175964160 ⟨⟨74350078713, 74350078721⟩, ⟨72321225327, 76395439172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 173178880 175964160 ⟨⟨74038645032, 74038645035⟩, ⟨72015691358, 76078028869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 195297280 195952640 170393600 173178880 ⟨⟨72609932614, 72609932621⟩, ⟨70597363252, 74638857728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195952640 196608000 170393600 173178880 ⟨⟨72304995064, 72304995071⟩, ⟨70298250367, 74328019454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 195952640 173178880 175964160 ⟨⟨73728338389, 73728338396⟩, ⟨71711252432, 75761778181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195952640 196608000 173178880 175964160 ⟨⟨73419149723, 73419149729⟩, ⟨71407899756, 75446677758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 194641920 175964160 178749440 ⟨⟨75475333890, 75475333896⟩, ⟨73441952367, 77525219850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 194641920 195297280 175964160 178749440 ⟨⟨75159647132, 75159647134⟩, ⟨73132176442, 77203545655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 194641920 178749440 181534720 ⟨⟨76598915125, 76598915131⟩, ⟨74561016457, 78653315480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 194641920 195297280 178749440 181534720 ⟨⟨76278993997, 76278994000⟩, ⟨74247017102, 78327396279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 175964160 178749440 ⟨⟨74845097664, 74845097670⟩, ⟨72823505825, 76883041306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195952640 196608000 175964160 178749440 ⟨⟨74531676368, 74531676374⟩, ⟨72515931667, 76563697400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195297280 195952640 178749440 181534720 ⟨⟨75960220228, 75960220234⟩, ⟨73934133140, 78002656971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 178749440 181534720 ⟨⟨75642584642, 75642584648⟩, ⟨73622355668, 77679088095⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 194641920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 195952640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 195297280) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 194641920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 195952640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
