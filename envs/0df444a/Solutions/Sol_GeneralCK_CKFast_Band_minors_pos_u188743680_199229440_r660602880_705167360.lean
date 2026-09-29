-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r660602880_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:23.602129+00:00
-- url     : https://prove2.me/submissions/c38608b3-3d7a-4097-8ac1-16dd522b5a56

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [63/80, 269/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 660602880 671744000 ⟨⟨259863240161, 259863240167⟩, ⟨248945228731, 271014696765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 660602880 671744000 ⟨⟨256358429348, 256358429358⟩, ⟨245539486353, 267409783518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 671744000 682885120 ⟨⟨263701082387, 263701082393⟩, ⟨252728272345, 274905911571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 671744000 682885120 ⟨⟨260157241308, 260157241317⟩, ⟨249283207763, 271262354866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 660602880 671744000 ⟨⟨252875256208, 252875256219⟩, ⟨242154412133, 263827456548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 199229440 660602880 671744000 ⟨⟨249413249633, 249413249643⟩, ⟨238789551124, 260267229749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 193986560 196608000 671744000 682885120 ⟨⟨256634799080, 256634799090⟩, ⟨245858603849, 267641111676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 199229440 671744000 682885120 ⟨⟨253133292448, 253133292458⟩, ⟨242454012585, 264041704725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 191365120 682885120 694026240 ⟨⟨267530130854, 267530130861⟩, ⟨256502706433, 278788123770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 193986560 682885120 694026240 ⟨⟨263947544958, 263947544968⟩, ⟨253018596463, 275106217726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 191365120 694026240 705167360 ⟨⟨271350670532, 271350670535⟩, ⟨260268808654, 282661625447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 191365120 193986560 694026240 705167360 ⟨⟨267729614452, 267729614460⟩, ⟨256745919634, 278941653037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 682885120 694026240 ⟨⟨260386113702, 260386113713⟩, ⟨249554734233, 271446347151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 199229440 682885120 694026240 ⟨⟨256845381655, 256845381665⟩, ⟨246110678643, 267808043541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193986560 196608000 694026240 705167360 ⟨⟨264129463717, 264129463726⟩, ⟨253243060278, 275243433077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 694026240 705167360 ⟨⟨260549770683, 260549770692⟩, ⟨249759796394, 271566505775⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 660602880 705167360 t = true :=
  ⟨_, (join_sr (m := 682885120) (by decide) (join_su (m := 193986560) (by decide) (join_sr (m := 671744000) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 671744000) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 196608000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 193986560) (by decide) (join_sr (m := 694026240) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 191365120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 694026240) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 196608000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
