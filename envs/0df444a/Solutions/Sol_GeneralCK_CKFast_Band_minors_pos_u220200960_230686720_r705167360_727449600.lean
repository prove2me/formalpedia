-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r705167360_727449600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:06:43.690831+00:00
-- url     : https://prove2.me/submissions/cc76c74a-fa1a-4f6b-896a-6ab028a6c626

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [269/320, 111/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 705167360 710737920 ⟨⟨231688688614, 231688688623⟩, ⟨222968550728, 240570528267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 710737920 716308480 ⟨⟨233356701701, 233356701710⟩, ⟨224609875341, 242265127996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 705167360 710737920 ⟨⟨228260478406, 228260478415⟩, ⟨219605164070, 237077114531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 710737920 716308480 ⟨⟨229908144614, 229908144623⟩, ⟨221226140768, 238751392672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 716308480 721879040 ⟨⟨235023422794, 235023422803⟩, ⟨226249919140, 243958419869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 721879040 727449600 ⟨⟨236688873015, 236688873026⟩, ⟨227888702879, 245650425357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 716308480 721879040 ⟨⟨231554567865, 231554567876⟩, ⟨222845884044, 240424413747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 721879040 727449600 ⟨⟨233199768388, 233199768398⟩, ⟨224464413778, 242096198312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 705167360 710737920 ⟨⟨224848288174, 224848288184⟩, ⟨216257293068, 233600212860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 710737920 716308480 ⟨⟨226475518536, 226475518545⟩, ⟨217857842188, 235254070507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 705167360 710737920 ⟨⟨221451778167, 221451778172⟩, ⟨212924605970, 230139475985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 710737920 716308480 ⟨⟨223058486373, 223058486376⟩, ⟨214504650283, 231772817131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 716308480 721879040 ⟨⟨228101553823, 228101553832⟩, ⟨219457204154, 236906720701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 721879040 727449600 ⟨⟨229726413397, 229726413406⟩, ⟨221055397993, 238558183112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 716308480 721879040 ⟨⟨224664046236, 224664046241⟩, ⟨216083552584, 233404999258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 721879040 727449600 ⟨⟨226268476280, 226268476284⟩, ⟨217661331083, 235036041181⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 705167360 727449600 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 710737920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 710737920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 721879040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 721879040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 716308480) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 710737920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 710737920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 721879040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 721879040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (111/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
