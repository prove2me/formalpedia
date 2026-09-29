-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:36:40.472173+00:00
-- url     : https://prove2.me/submissions/cb5e3bb4-f8b3-4a17-8d78-38763976f5ae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [19/64, 13/40]` by 12 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 249036800 254935040 ⟨⟨175149193032, 175149193043⟩, ⟨168386573348, 182041263002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 111411200 112721920 249036800 254935040 ⟨⟨173692149383, 173692149392⟩, ⟨166985159496, 180527041944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 111411200 254935040 260833280 ⟨⟨178562536136, 178562536147⟩, ⟨171784038758, 185469365630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 111411200 112721920 254935040 260833280 ⟨⟨177086514981, 177086514992⟩, ⟨170363412257, 183936439195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 114032640 249036800 254935040 ⟨⟨172251353074, 172251353082⟩, ⟨165599138286, 179029951394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 114032640 115343360 249036800 254935040 ⟨⟨170826468477, 170826468482⟩, ⟨164228194011, 177549635103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 112721920 114032640 254935040 260833280 ⟨⟨175626761978, 175626761987⟩, ⟨168958211369, 182420650749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114032640 115343360 254935040 260833280 ⟨⟨174182943854, 174182943859⟩, ⟨167568122272, 180921646916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 112721920 260833280 266731520 ⟨⟨181204619312, 181204619315⟩, ⟨170521215905, 192208142402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110100480 112721920 266731520 272629760 ⟨⟨184565506698, 184565506705⟩, ⟨173851734280, 195597023275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 115343360 260833280 266731520 ⟨⟨178247896477, 178247896486⟩, ⟨167723117556, 189086020292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112721920 115343360 266731520 272629760 ⟨⟨181572406359, 181572406370⟩, ⟨171016634978, 192439308529⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 111411200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 114032640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 112721920) (by decide) (join_sr (m := 266731520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 266731520) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
