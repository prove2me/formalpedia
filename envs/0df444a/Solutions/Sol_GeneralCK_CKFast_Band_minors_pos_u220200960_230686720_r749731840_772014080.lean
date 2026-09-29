-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r749731840_772014080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:12:26.062217+00:00
-- url     : https://prove2.me/submissions/86948bc8-f77a-42f6-af74-0c46eed272b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [143/160, 589/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 749731840 755302400 ⟨⟨244997793353, 244997793362⟩, ⟨236064440059, 254091901468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 755302400 760872960 ⟨⟨246656056366, 246656056375⟩, ⟨237696093726, 255776633936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 749731840 755302400 ⟨⟨241408131507, 241408131517⟩, ⟨232539548594, 250437286353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 755302400 760872960 ⟨⟨243046415256, 243046415266⟩, ⟨234151209384, 252102078301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 760872960 766443520 ⟨⟨248313193620, 248313193631⟩, ⟨239326629874, 257460227546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 766443520 772014080 ⟨⟨249969225476, 249969225484⟩, ⟨240956068501, 259142702996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 760872960 766443520 ⟨⟨244683615311, 244683615321⟩, ⟨235761793239, 253765775045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 766443520 772014080 ⟨⟨246319751188, 246319751196⟩, ⟨237371319330, 255428396423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 749731840 755302400 ⟨⟨237833747108, 237833747119⟩, ⟨229029505412, 246798360660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 755302400 760872960 ⟨⟨239451954151, 239451954160⟩, ⟨230621085379, 248443104536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 749731840 755302400 ⟨⟨234274321761, 234274321765⟩, ⟨225533998344, 243174800309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 755302400 760872960 ⟨⟨235872357326, 235872357330⟩, ⟨227105412006, 244799391463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 760872960 766443520 ⟨⟨241069118620, 241069118628⟩, ⟨232211628073, 250086795906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 766443520 772014080 ⟨⟨242685259213, 242685259220⟩, ⟨233801151863, 251729453769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 760872960 766443520 ⟨⟨237469390498, 237469390503⟩, ⟨228675827136, 246422971842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 766443520 772014080 ⟨⟨239065439179, 239065439182⟩, ⟨230245261328, 248045559635⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 749731840 772014080 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 755302400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 755302400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 766443520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 766443520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 760872960) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 755302400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 755302400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 766443520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 766443520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (589/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
