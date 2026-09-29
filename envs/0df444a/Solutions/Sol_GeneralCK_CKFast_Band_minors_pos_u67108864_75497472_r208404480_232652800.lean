-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:51:42.157148+00:00
-- url     : https://prove2.me/submissions/0cfec715-4848-4636-8153-e815ccbc14e9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [159/640, 71/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 208404480 214466560 ⟨⟨205414306061, 205414306072⟩, ⟨193087869073, 218152393109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 69206016 214466560 220528640 ⟨⟨209847309929, 209847309940⟩, ⟨197514135061, 222585366155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 71303168 208404480 214466560 ⟨⟨202042774123, 202042774136⟩, ⟨189938772726, 214547367586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 214466560 220528640 ⟨⟨206439266623, 206439266635⟩, ⟨194326236064, 218946530598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 69206016 220528640 226590720 ⟨⟨214230282182, 214230282193⟩, ⟨201891293334, 226967506299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 69206016 226590720 232652800 ⟨⟨218564754244, 218564754258⟩, ⟨206220817018, 231300400529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69206016 71303168 220528640 226590720 ⟨⟨210787212812, 210787212825⟩, ⟨198666078340, 223296331592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 69206016 71303168 226590720 232652800 ⟨⟨215088071624, 215088071635⟩, ⟨202959702598, 227598283118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 73400320 208404480 214466560 ⟨⟨198764020148, 198764020159⟩, ⟨186874358762, 211043681113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71303168 73400320 214466560 220528640 ⟨⟨203123665106, 203123665120⟩, ⟨191222868294, 215408485505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 73400320 75497472 208404480 214466560 ⟨⟨195573684372, 195573684384⟩, ⟨183890705898, 207636509879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 73400320 75497472 214466560 220528640 ⟨⟨199896208852, 199896208862⟩, ⟨188200158794, 211966487349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 73400320 220528640 226590720 ⟨⟨207436210944, 207436210957⟩, ⟨195525201618, 219725365651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 71303168 73400320 226590720 232652800 ⟨⟨211703047620, 211703047630⟩, ⟨199782695200, 223995763126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 73400320 75497472 220528640 226590720 ⟨⟨204173043396, 204173043409⟩, ⟨192464839191, 216249944666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 73400320 75497472 226590720 232652800 ⟨⟨208405512356, 208405512369⟩, ⟨196686020293, 220488255783⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 71303168) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 69206016) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 226590720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 214466560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 73400320) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 226590720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
