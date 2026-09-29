-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:38:22.077015+00:00
-- url     : https://prove2.me/submissions/56446a41-1481-41e9-a2dc-e02a8a1bb8fa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [19/64, 13/40]` by 15 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 249036800 254935040 ⟨⟨169417169315, 169417169325⟩, ⟨162872019720, 176085746806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 116654080 117964800 249036800 254935040 ⟨⟨168023138341, 168023138352⟩, ⟨161530316874, 174637949881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 116654080 254935040 260833280 ⟨⟨172754736555, 172754736565⟩, ⟨166192839784, 179439084145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 254935040 260833280 ⟨⟨171341824925, 171341824934⟩, ⟨164832067019, 177972628375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 117964800 119275520 249036800 254935040 ⟨⟨166644066998, 166644067006⟩, ⟨160202795068, 173205916978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119275520 120586240 249036800 254935040 ⟨⟨165279655114, 165279655123⟩, ⟨158889171745, 171789329707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 119275520 254935040 260833280 ⟨⟨169943902369, 169943902378⟩, ⟨163485515128, 176521954682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119275520 120586240 254935040 260833280 ⟨⟨168560670570, 168560670581⟩, ⟨162152902998, 175086746956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 116654080 260833280 266731520 ⟨⟨176071947496, 176071947505⟩, ⟨169493630239, 182771742787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 116654080 117964800 260833280 266731520 ⟨⟨174640526022, 174640526031⟩, ⟨168114153037, 181287003885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 117964800 266731520 272629760 ⟨⟨178642521497, 178642521508⟩, ⟨168240020272, 189349767264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 119275520 260833280 266731520 ⟨⟨173224116973, 173224116982⟩, ⟨166748930438, 179818059042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 119275520 120586240 260833280 266731520 ⟨⟨171822423968, 171822423977⟩, ⟨165397682874, 178364594515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 117964800 119275520 266731520 272629760 ⟨⟨176485092079, 176485092089⟩, ⟨169993412732, 183094620902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 120586240 266731520 272629760 ⟨⟨175065286420, 175065286429⟩, ⟨168623873242, 181623252785⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 116654080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119275520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 117964800) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 266731520) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 119275520) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
