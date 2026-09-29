-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:37:21.269507+00:00
-- url     : https://prove2.me/submissions/e82b31d1-ef2e-47c7-a4ac-75a9b22f520c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 192675840 195461120 ⟨⟨71834919421, 71834919427⟩, ⟨69951199693, 73732976885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215613440 216268800 192675840 195461120 ⟨⟨71528079796, 71528079803⟩, ⟨69649434914, 73421002610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 195461120 198246400 ⟨⟨72820906942, 72820906949⟩, ⟨70933061370, 74723094726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 195461120 198246400 ⟨⟨72510208642, 72510208647⟩, ⟨70627448337, 74407251542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216268800 216924160 192675840 195461120 ⟨⟨71222173568, 71222173574⟩, ⟨69348579004, 73109986654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216924160 217579520 192675840 195461120 ⟨⟨70917193730, 70917193737⟩, ⟨69048625146, 72799921824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 216924160 195461120 198246400 ⟨⟨72200451372, 72200451378⟩, ⟨70322751813, 74092374306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216924160 217579520 195461120 198246400 ⟨⟨71891628086, 71891628093⟩, ⟨70018964942, 73778455781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 215613440 198246400 201031680 ⟨⟨73805778571, 73805778578⟩, ⟨71913813098, 75712090649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215613440 216268800 198246400 201031680 ⟨⟨73491234565, 73491234572⟩, ⟨71604364667, 75392391643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 215613440 201031680 203816960 ⟨⟨74789540269, 74789540275⟩, ⟨72893460799, 76699970646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 215613440 216268800 201031680 203816960 ⟨⟨74471163437, 74471163443⟩, ⟨72580189735, 76376428815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 198246400 201031680 ⟨⟨73177639097, 73177639104⟩, ⟨71295840258, 75073666085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216924160 217579520 198246400 201031680 ⟨⟨72864985083, 72864985090⟩, ⟨70988232977, 74755906697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216268800 216924160 201031680 203816960 ⟨⟨74153742527, 74153742534⟩, ⟨72267850083, 76053867805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 201031680 203816960 ⟨⟨73837270417, 73837270422⟩, ⟨71956434913, 75732280298⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215613440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 216924160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216268800) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 215613440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 216924160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
