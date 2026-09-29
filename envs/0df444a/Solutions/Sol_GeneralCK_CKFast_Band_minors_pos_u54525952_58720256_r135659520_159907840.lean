-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u54525952_58720256_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:10:18.523993+00:00
-- url     : https://prove2.me/submissions/8d1e49f8-b381-4e0f-9472-24a2b21042cb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/200, 7/100]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 54525952 55574528 135659520 141721600 ⟨⟨167519830550, 167519830565⟩, ⟨157923820091, 177406164024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 55574528 56623104 135659520 141721600 ⟨⟨165751507307, 165751507323⟩, ⟨156275812003, 175511568595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 55574528 141721600 147783680 ⟨⟨173096575653, 173096575669⟩, ⟨163505757114, 182970924973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 55574528 56623104 141721600 147783680 ⟨⟨171296313139, 171296313151⟩, ⟨161824214470, 181046251078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 56623104 57671680 135659520 141721600 ⟨⟨164017916651, 164017916666⟩, ⟨154659542608, 173654886719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 57671680 58720256 135659520 141721600 ⟨⟨162317936298, 162317936310⟩, ⟨153074000903, 171834876992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 56623104 57671680 141721600 147783680 ⟨⟨169530780876, 169530780892⟩, ⟨160174494236, 179159389980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 57671680 58720256 141721600 147783680 ⟨⟨167798873415, 167798873430⟩, ⟨158555597393, 177309122635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 55574528 147783680 153845760 ⟨⟨178578041212, 178578041228⟩, ⟨168993933254, 188439079829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 55574528 56623104 147783680 153845760 ⟨⟨176747683359, 176747683371⟩, ⟨167280695555, 186486163872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 54525952 55574528 153845760 159907840 ⟨⟨183968097417, 183968097430⟩, ⟨174392079657, 193814631625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 55574528 56623104 153845760 159907840 ⟨⟨182109367565, 182109367580⟩, ⟨172648869863, 191835185952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 56623104 57671680 147783680 153845760 ⟨⟨174952016025, 174952016041⟩, ⟨165599324587, 184570925340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 57671680 58720256 147783680 153845760 ⟨⟨173189951166, 173189951180⟩, ⟨163948834096, 182692167862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 56623104 57671680 153845760 159907840 ⟨⟨180285255270, 180285255285⟩, ⟨170937535815, 189893251905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 57671680 58720256 153845760 159907840 ⟨⟨178494690308, 178494690323⟩, ⟨169257104662, 187987655946⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 54525952 58720256 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 56623104) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 55574528) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 55574528) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 57671680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 57671680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 56623104) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 55574528) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 55574528) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 57671680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 57671680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/200 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
