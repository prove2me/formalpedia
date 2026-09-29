-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_71303168_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:48:47.212091+00:00
-- url     : https://prove2.me/submissions/dfa88b84-720b-4ed1-b979-f655207c3bc5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 17/200]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 68157440 159907840 165969920 ⟨⟨168711162464, 168711162478⟩, ⟨160354411346, 177280926991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 68157440 69206016 159907840 165969920 ⟨⟨167179064179, 167179064193⟩, ⟨158909600761, 175657974455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 68157440 165969920 172032000 ⟨⟨173621131785, 173621131799⟩, ⟨165260120044, 182191215305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 68157440 69206016 165969920 172032000 ⟨⟨172063206285, 172063206299⟩, ⟨163788603589, 180543447718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 69206016 70254592 159907840 165969920 ⟨⟨165671315145, 165671315159⟩, ⟨157487357464, 174061244398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 70254592 71303168 159907840 165969920 ⟨⟨164187265266, 164187265279⟩, ⟨156087085959, 172490029009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69206016 70254592 165969920 172032000 ⟨⟨170529653762, 170529653773⟩, ⟨162339720265, 178921879000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 70254592 71303168 165969920 172032000 ⟨⟨169019831793, 169019831804⟩, ⟨160912880252, 177325811265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 68157440 172032000 178094080 ⟨⟨178465550268, 178465550282⟩, ⟨170101306085, 187035007264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 68157440 69206016 172032000 178094080 ⟨⟨176882945032, 176882945046⟩, ⟨168604223727, 185363574922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 68157440 178094080 184156160 ⟨⟨183246620841, 183246620855⟩, ⟨174880101183, 191814575127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 68157440 69206016 178094080 184156160 ⟨⟨181640422369, 181640422380⟩, ⟨173358533858, 190120565565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 69206016 70254592 172032000 178094080 ⟨⟨175324715960, 175324715970⟩, ⟨167129819132, 183718298247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 70254592 71303168 172032000 178094080 ⟨⟨173790228615, 173790228626⟩, ⟨165677508529, 182098489497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 69206016 70254592 178094080 184156160 ⟨⟨180058584547, 180058584561⟩, ⟨171859669519, 188452650742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70254592 71303168 178094080 184156160 ⟨⟨178500481178, 178500481192⟩, ⟨170382930764, 186810153217⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 71303168 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 68157440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 68157440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 70254592) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 70254592) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 69206016) (by decide) (join_sr (m := 178094080) (by decide) (join_su (m := 68157440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 68157440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178094080) (by decide) (join_su (m := 70254592) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 70254592) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
