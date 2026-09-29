-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:15:29.906103+00:00
-- url     : https://prove2.me/submissions/149ea2f0-6643-48bd-918b-2eb0c9d37269

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [159/640, 71/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 208404480 214466560 ⟨⟨236366143072, 236366143088⟩, ⟨221902774267, 251350114172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 52428800 214466560 220528640 ⟨⟨241068625750, 241068625763⟩, ⟨226625895606, 256020580655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 52428800 54525952 208404480 214466560 ⟨⟨232051535826, 232051535842⟩, ⟨217896223056, 246711501667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 214466560 220528640 ⟨⟨236723586195, 236723586208⟩, ⟨222584376733, 251356809879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 52428800 220528640 226590720 ⟨⟨245707890316, 245707890332⟩, ⟨231286483468, 260627442939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 52428800 226590720 232652800 ⟨⟨250286194517, 250286194533⟩, ⟨235886720659, 265173023246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 52428800 54525952 220528640 226590720 ⟨⟨241334180656, 241334180669⟩, ⟨227211821456, 255940182355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 52428800 54525952 226590720 232652800 ⟨⟨245885470488, 245885470503⟩, ⟨231780634961, 260463835005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 56623104 208404480 214466560 ⟨⟨227878582287, 227878582302⟩, ⟨214018094090, 242228521477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 56623104 214466560 220528640 ⟨⟨232518997438, 232518997451⟩, ⟨218670455087, 246847035639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 56623104 58720256 208404480 214466560 ⟨⟨223839414833, 223839414848⟩, ⟨210261371719, 237892409916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 56623104 58720256 214466560 220528640 ⟨⟨228447148299, 228447148312⟩, ⟨214877237560, 242482689410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 54525952 56623104 220528640 226590720 ⟨⟨237099690773, 237099690788⟩, ⟨223263891526, 251405269789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 54525952 56623104 226590720 232652800 ⟨⟨241622711865, 241622711880⟩, ⟨227800381141, 255905337753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 56623104 58720256 220528640 226590720 ⟨⟨232996862992, 232996863005⟩, ⟨219435921788, 247014326940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 56623104 58720256 226590720 232652800 ⟨⟨237490511408, 237490511420⟩, ⟨223939307020, 251489338435⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 54525952) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 52428800) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 52428800) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 226590720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 56623104) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 214466560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 56623104) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 226590720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
