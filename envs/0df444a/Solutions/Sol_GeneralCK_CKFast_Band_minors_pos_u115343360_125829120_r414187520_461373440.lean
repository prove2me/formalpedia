-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r414187520_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:44:23.595566+00:00
-- url     : https://prove2.me/submissions/a72ebe3c-4c36-4ab1-b81a-da35a9d925c7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [79/160, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 414187520 425984000 ⟨⟨256859463673, 256859463684⟩, ⟨243156467732, 270950103191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 117964800 120586240 414187520 425984000 ⟨⟨253253096315, 253253096326⟩, ⟨239729345587, 267159216893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 117964800 425984000 437780480 ⟨⟨262611132535, 262611132546⟩, ⟨248864466294, 276738689981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 425984000 437780480 ⟨⟨258958716437, 258958716448⟩, ⟨245389375907, 272904016539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 123207680 414187520 425984000 ⟨⟨249702034744, 249702034755⟩, ⟨236353637095, 263427612293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 125829120 414187520 425984000 ⟨⟨246204503393, 246204503400⟩, ⟨233027698752, 259753381361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 120586240 123207680 425984000 437780480 ⟨⟨255361100362, 255361100373⟩, ⟨241965320531, 269127977504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123207680 125829120 425984000 437780480 ⟨⟨251816545631, 251816545638⟩, ⟨238590686950, 265408708971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 117964800 437780480 449576960 ⟨⟨268316745689, 268316745699⟩, ⟨254527487469, 282480199627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 120586240 437780480 449576960 ⟨⟨264619576841, 264619576853⟩, ⟨251005715105, 278603035881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 117964800 449576960 461373440 ⟨⟨273977971919, 273977971929⟩, ⟨260147138756, 288176360659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 120586240 449576960 461373440 ⟨⟨270237279705, 270237279715⟩, ⟨256579906385, 284257934805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 437780480 449576960 ⟨⟨260976680145, 260976680156⟩, ⟨247534574528, 274783840375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 437780480 449576960 ⟨⟨257386353392, 257386353399⟩, ⟨244112482679, 271020792571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 123207680 449576960 461373440 ⟨⟨266550311960, 266550311972⟩, ⟨253062880290, 280396794424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 449576960 461373440 ⟨⟨262915402482, 262915402486⟩, ⟨249594507366, 276591161547⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 414187520 461373440 t = true :=
  ⟨_, (join_sr (m := 437780480) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 117964800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 425984000) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 123207680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 120586240) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 117964800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 449576960) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 123207680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
