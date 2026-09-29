-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:15:47.365993+00:00
-- url     : https://prove2.me/submissions/34fd74fc-b39c-46bc-9aef-da2beab211ff

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 170393600 173178880 ⟨⟨69608955916, 69608955922⟩, ⟨67653249261, 71580282540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 202506240 203161600 170393600 173178880 ⟨⟨69314618001, 69314618007⟩, ⟨67364433214, 71280352112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 202506240 173178880 175964160 ⟨⟨70685308034, 70685308041⟩, ⟨68725198458, 72661038401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 173178880 175964160 ⟨⟨70386819625, 70386819631⟩, ⟨68432243320, 72356946323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 203161600 203816960 170393600 173178880 ⟨⟨69021294259, 69021294266⟩, ⟨67076602450, 70981465256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203816960 204472320 170393600 173178880 ⟨⟨68728976682, 68728976689⟩, ⟨66789749208, 70683613719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 203161600 203816960 173178880 175964160 ⟨⟨70089355136, 70089355144⟩, ⟨68140283221, 72053907559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203816960 204472320 173178880 175964160 ⟨⟨69792906511, 69792906518⟩, ⟨67849310341, 71751913803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 202506240 175964160 178749440 ⟨⟨71760190501, 71760190507⟩, ⟨69795687040, 73740315464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 202506240 203161600 175964160 178749440 ⟨⟨71457568332, 71457568338⟩, ⟨69498609393, 73432078630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 201850880 202506240 178749440 181534720 ⟨⟨72833611734, 72833611740⟩, ⟨70864723368, 74818122211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 202506240 203161600 178749440 181534720 ⟨⟨72526872415, 72526872421⟩, ⟨70563539663, 74505757387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 175964160 178749440 ⟨⟨71155979670, 71155979676⟩, ⟨69202536373, 73124904685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203816960 204472320 175964160 178749440 ⟨⟨70855416401, 70855416407⟩, ⟨68907460109, 72818785270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 203816960 178749440 181534720 ⟨⟨72221176024, 72221176030⟩, ⟨70263370016, 74194464861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 178749440 181534720 ⟨⟨71916514395, 71916514400⟩, ⟨69964206501, 73884236223⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 202506240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203816960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 203161600) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 202506240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203816960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
