-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:33:04.120983+00:00
-- url     : https://prove2.me/submissions/9e1f1ce8-2652-4577-86c2-a5b94c40e453

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 460062720 465633280 ⟨⟨162300660542, 162300660550⟩, ⟨157802414066, 166856385203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 460062720 465633280 ⟨⟨161042122915, 161042122924⟩, ⟨156566329372, 165575090631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 216268800 465633280 471203840 ⟨⟨164101182248, 164101182257⟩, ⟨159588164705, 168671651311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 465633280 471203840 ⟨⟨162830893141, 162830893149⟩, ⟨158340348985, 167378588804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218890240 460062720 465633280 ⟨⟨159788474967, 159788474975⟩, ⟨155334979035, 164298843081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218890240 220200960 460062720 465633280 ⟨⟨158539657208, 158539657211⟩, ⟨154108305312, 163027581292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 218890240 465633280 471203840 ⟨⟨161565491657, 161565491665⟩, ⟨157097266824, 166090569925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218890240 220200960 465633280 471203840 ⟨⟨160304918549, 160304918553⟩, ⟨155858860693, 164807533688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 216268800 471203840 476774400 ⟨⟨165899124746, 165899124754⟩, ⟨161371360975, 170484312081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 217579520 471203840 476774400 ⟨⟨164617136574, 164617136582⟩, ⟨160111865742, 169179534976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 216268800 476774400 482344960 ⟨⟨167694518738, 167694518747⟩, ⟨163152033230, 172294398570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216268800 217579520 476774400 482344960 ⟨⟨166400883174, 166400883182⟩, ⟨161880909261, 170977959448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 471203840 476774400 ⟨⟨163340033208, 163340033216⟩, ⟨158857102517, 167879797333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 220200960 471203840 476774400 ⟨⟨162067755650, 162067755654⟩, ⟨157607013995, 166585038440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 218890240 476774400 482344960 ⟨⟨165112128849, 165112128858⟩, ⟨160614515016, 169666554858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 476774400 482344960 ⟨⟨163828197023, 163828197026⟩, ⟨159352793413, 168360124377⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216268800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218890240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 217579520) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 216268800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 476774400) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 218890240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
