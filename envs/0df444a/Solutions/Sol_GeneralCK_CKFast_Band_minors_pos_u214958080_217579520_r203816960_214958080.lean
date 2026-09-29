-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:39:17.789247+00:00
-- url     : https://prove2.me/submissions/c499c587-83d4-40e7-881a-923eb3445db1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 203816960 206602240 ⟨⟨75772197961, 75772197967⟩, ⟨73872010366, 77686740683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215613440 216268800 203816960 206602240 ⟨⟨75450001097, 75450001102⟩, ⟨73554929346, 77359368935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 206602240 209387520 ⟨⟨76753757546, 76753757553⟩, ⟨74849467660, 78672406695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 206602240 209387520 ⟨⟨76427753353, 76427753359⟩, ⟨74528589277, 78341217847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216268800 216924160 203816960 206602240 ⟨⟨75128767412, 75128767418⟩, ⟨73238787009, 77032985254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216924160 217579520 203816960 206602240 ⟨⟨74808489751, 74808489756⟩, ⟨72923576384, 76707582287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 216924160 206602240 209387520 ⟨⟨76102719478, 76102719484⟩, ⟨74208656724, 78011024190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216924160 217579520 206602240 209387520 ⟨⟨75778648725, 75778648731⟩, ⟨73889662992, 77681818336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 215613440 209387520 212172800 ⟨⟨77734224893, 77734224900⟩, ⟨75825838515, 79656974583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215613440 216268800 209387520 212172800 ⟨⟨77404425990, 77404425996⟩, ⟨75501175273, 79321981368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 215613440 212172800 214958080 ⟨⟨78713605841, 78713605846⟩, ⟨76801128734, 80640450224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 215613440 216268800 212172800 214958080 ⟨⟨78380024756, 78380024763⟩, ⟨76472693054, 80301665283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 209387520 212172800 ⟨⟨77075604419, 77075604425⟩, ⟨75177464890, 78987990342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216924160 217579520 209387520 212172800 ⟨⟨76747752950, 76747752957⟩, ⟨74854700319, 78654994085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216268800 216924160 212172800 214958080 ⟨⟨78047427901, 78047427907⟩, ⟨76145217139, 79963889412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 212172800 214958080 ⟨⟨77715808009, 77715808016⟩, ⟨75818693913, 79627115155⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215613440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 216924160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216268800) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 215613440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 216924160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
