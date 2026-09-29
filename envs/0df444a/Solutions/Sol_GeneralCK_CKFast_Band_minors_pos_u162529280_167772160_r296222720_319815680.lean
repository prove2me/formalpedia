-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:02:01.120023+00:00
-- url     : https://prove2.me/submissions/b478237f-e58c-41c3-961a-e7f03b36e9d1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 296222720 302120960 ⟨⟨148101719800, 148101719808⟩, ⟨142901814370, 153383933716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163840000 165150720 296222720 302120960 ⟨⟨146969651562, 146969651571⟩, ⟨141802316190, 152218586658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163840000 302120960 308019200 ⟨⟨150708452284, 150708452293⟩, ⟨145490589572, 156008354935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 302120960 308019200 ⟨⟨149560678257, 149560678266⟩, ⟨144375375657, 154827322978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 166461440 296222720 302120960 ⟨⟨145845689832, 145845689841⟩, ⟨140710572485, 151061707422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166461440 167772160 296222720 302120960 ⟨⟨144729709210, 144729709214⟩, ⟨139626463767, 149913164535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 166461440 302120960 308019200 ⟨⟨148421039155, 148421039164⟩, ⟨143267947657, 153654783956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167772160 302120960 308019200 ⟨⟨147289409918, 147289409922⟩, ⟨142168186322, 152490606838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 308019200 313917440 ⟨⟨153306074708, 153306074717⟩, ⟨148070388170, 158623530922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 165150720 308019200 313917440 ⟨⟨152142766002, 152142766010⟩, ⟨146939626649, 157426988121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163840000 313917440 319815680 ⟨⟨155894721264, 155894721273⟩, ⟨150641341796, 161229598453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163840000 165150720 313917440 319815680 ⟨⟨154716045584, 154716045594⟩, ⟨149495197482, 160017715374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 308019200 313917440 ⟨⟨150987617955, 150987617964⟩, ⟨145816679837, 156238960652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167772160 308019200 313917440 ⟨⟨149840505881, 149840505885⟩, ⟨144701428756, 155059317965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 166461440 313917440 319815680 ⟨⟨153545553701, 153545553708⟩, ⟨148356894102, 158814367397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 313917440 319815680 ⟨⟨152383121328, 152383121332⟩, ⟨147226312989, 157619424479⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 296222720 319815680 t = true :=
  ⟨_, (join_sr (m := 308019200) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 302120960) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163840000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 302120960) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166461440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165150720) (by decide) (join_sr (m := 313917440) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163840000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 313917440) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166461440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
