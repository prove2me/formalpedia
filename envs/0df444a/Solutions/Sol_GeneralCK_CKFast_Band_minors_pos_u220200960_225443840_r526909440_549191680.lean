-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:49:03.866261+00:00
-- url     : https://prove2.me/submissions/c8d54758-25e6-43c5-afcf-814dc2a9e214

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [201/320, 419/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 526909440 532480000 ⟨⟨178186997050, 178186997058⟩, ⟨173602794709, 182827258584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221511680 222822400 526909440 532480000 ⟨⟨176809678211, 176809678218⟩, ⟨172247567539, 181427597277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 532480000 538050560 ⟨⟨179913805946, 179913805955⟩, ⟨175315157609, 184568487509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 532480000 538050560 ⟨⟨178525277952, 178525277960⟩, ⟨173948737028, 183157605173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 526909440 532480000 ⟨⟨175436956484, 175436956491⟩, ⟨170896803524, 180032668098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224133120 225443840 526909440 532480000 ⟨⟨174068778306, 174068778314⟩, ⟨169550450445, 178642416140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 224133120 532480000 538050560 ⟨⟨177141337992, 177141338001⟩, ⟨172586771794, 181751444544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 225443840 532480000 538050560 ⟨⟨175761932784, 175761932792⟩, ⟨171229209949, 180349951013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 221511680 538050560 543621120 ⟨⟨181638562084, 181638562093⟩, ⟨177025485516, 186307644659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222822400 538050560 543621120 ⟨⟨180238866563, 180238866571⟩, ⟨175647912418, 184885583671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 221511680 543621120 549191680 ⟨⟨183361291088, 183361291097⟩, ⟨178733803773, 188044755940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221511680 222822400 543621120 549191680 ⟨⟨181950469062, 181950469071⟩, ⟨177345118461, 186611558056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 538050560 543621120 ⟨⟨178843749418, 178843749427⟩, ⟨174274786295, 183468233374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 225443840 538050560 543621120 ⟨⟨177453157650, 177453157657⟩, ⟨172906055442, 182055539471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222822400 224133120 543621120 549191680 ⟨⟨180544215185, 180544215193⟩, ⟨175960871186, 185183059273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 543621120 549191680 ⟨⟨179142476744, 179142476752⟩, ⟨174581010509, 183759205606⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 526909440 549191680 t = true :=
  ⟨_, (join_sr (m := 538050560) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 532480000) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221511680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 532480000) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224133120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222822400) (by decide) (join_sr (m := 543621120) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221511680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543621120) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224133120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
