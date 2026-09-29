-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:44:41.271276+00:00
-- url     : https://prove2.me/submissions/ef70ed47-6793-44fc-b5b2-3b5d88665ece

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 1/20]`, `ρ ∈ [207/1280, 61/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 37748736 38797312 135659520 141721600 ⟨⟨201701758445, 201701758463⟩, ⟨189654640447, 214168450135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 38797312 39845888 135659520 141721600 ⟨⟨199169666179, 199169666187⟩, ⟨187312176715, 211436244939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 38797312 141721600 147783680 ⟨⟨207767752063, 207767752083⟩, ⟨195768702571, 220172839989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38797312 39845888 141721600 147783680 ⟨⟨205207801154, 205207801162⟩, ⟨193394365565, 217417404399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 39845888 40894464 135659520 141721600 ⟨⟨196700381330, 196700381348⟩, ⟨185026589736, 208773176219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 40894464 41943040 135659520 141721600 ⟨⟨194291356495, 194291356510⟩, ⟨182795608976, 206176399643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 39845888 40894464 141721600 147783680 ⟨⟨202710054696, 202710054711⟩, ⟨191076538004, 214730232656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 40894464 41943040 141721600 147783680 ⟨⟨200272031682, 200272031700⟩, ⟨188813000214, 212108564643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 37748736 38797312 147783680 153845760 ⟨⟨213703601844, 213703601859⟩, ⟨201753649431, 226046622040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 38797312 39845888 147783680 153845760 ⟨⟨211118264894, 211118264902⟩, ⟨199349994980, 223270306824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 37748736 39845888 153845760 159907840 ⟨⟨218203821179, 218203821194⟩, ⟨201043687923, 236186366905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 39845888 40894464 147783680 153845760 ⟨⟨208594493030, 208594493048⟩, ⟨197002435665, 220561359950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 40894464 41943040 147783680 153845760 ⟨⟨206129870399, 206129870417⟩, ⟨194708802446, 217917102982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 41943040 153845760 159907840 ⟨⟨213108102328, 213108102343⟩, ⟨196437703208, 230564841217⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 41943040 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 39845888) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 38797312) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 38797312) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 40894464) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 40894464) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 39845888) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 38797312) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 153845760) (by decide) (join_su (m := 40894464) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
