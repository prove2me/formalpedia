-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:45.813401+00:00
-- url     : https://prove2.me/submissions/86452494-cf78-451f-ad52-26bfc7e1879d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 153681920 155074560 ⟨⟨45211822254, 45211822259⟩, ⟨44415105117, 46011400240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250675200 251002880 153681920 155074560 ⟨⟨45104481012, 45104481017⟩, ⟨44308726367, 45903091033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250347520 250675200 155074560 156467200 ⟨⟨45610358138, 45610358143⟩, ⟨44812742981, 46410835652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 155074560 156467200 ⟨⟨45502112402, 45502112409⟩, ⟨44705461117, 46301620576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 251002880 251330560 153681920 155074560 ⟨⟨44997275064, 44997275069⟩, ⟨44202480862, 45794919187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251330560 251658240 153681920 155074560 ⟨⟨44890203909, 44890203913⟩, ⟨44096368111, 45686884188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 251002880 251330560 155074560 156467200 ⟨⟨45394002824, 45394002829⟩, ⟨44598313361, 46192543725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251330560 251658240 155074560 156467200 ⟨⟨45286028899, 45286028903⟩, ⟨44491299216, 46083604584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 250675200 156467200 157859840 ⟨⟨46008740944, 46008740949⟩, ⟨45210227957, 46810117795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250675200 251002880 156467200 157859840 ⟨⟨45899591742, 45899591747⟩, ⟨45102044001, 46699997881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 250675200 157859840 159252480 ⟨⟨46406971011, 46406971016⟩, ⟨45607560381, 47209247009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250675200 251002880 157859840 159252480 ⟨⟨46296919366, 46296919372⟩, ⟨45498475354, 47098223284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251330560 156467200 157859840 ⟨⟨45790579554, 45790579559⟩, ⟨44993995009, 46590017050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251330560 251658240 156467200 157859840 ⟨⟨45681703873, 45681703877⟩, ⟨44886080482, 46480174785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251330560 157859840 159252480 ⟨⟨46187005586, 46187005592⟩, ⟨45389526140, 46987339496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251330560 251658240 157859840 159252480 ⟨⟨46077229165, 46077229169⟩, ⟨45280712242, 46876595123⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 250675200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251330560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 251002880) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 250675200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251330560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
