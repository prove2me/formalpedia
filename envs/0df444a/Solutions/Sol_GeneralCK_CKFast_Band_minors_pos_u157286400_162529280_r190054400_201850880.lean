-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:51:51.202017+00:00
-- url     : https://prove2.me/submissions/73c7f744-417c-42f4-a5eb-749d1e4f8981

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [29/128, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 190054400 193003520 ⟨⟨102070993157, 102070993165⟩, ⟨98044048986, 106156498062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 158597120 193003520 195952640 ⟨⟨103511834989, 103511834997⟩, ⟨99475346821, 107606827526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 158597120 159907840 190054400 193003520 ⟨⟨101230898523, 101230898531⟩, ⟨97228443501, 105291345680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 193003520 195952640 ⟨⟨102661746922, 102661746931⟩, ⟨98649773023, 106731660215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 158597120 195952640 198901760 ⟨⟨104949394289, 104949394296⟩, ⟨100903403046, 109053832944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 158597120 198901760 201850880 ⟨⟨106383696860, 106383696867⟩, ⟨102328243055, 110497540536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159907840 195952640 198901760 ⟨⟨104089380803, 104089380809⟩, ⟨100067927860, 108168719807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 158597120 159907840 198901760 201850880 ⟨⟨105513825222, 105513825231⟩, ⟨101482932679, 109602549917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 161218560 190054400 193003520 ⟨⟨100398321113, 100398321118⟩, ⟨96420032471, 104434042903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 161218560 193003520 195952640 ⟨⟨101819226120, 101819226123⟩, ⟨97831444489, 105864391665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161218560 162529280 190054400 193003520 ⟨⟨99573127031, 99573127040⟩, ⟨95618688403, 103584449225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161218560 162529280 193003520 195952640 ⟨⟨100984138273, 100984138280⟩, ⟨97020233279, 105004881003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 195952640 198901760 ⟨⟨103236983307, 103236983310⟩, ⟨99239747459, 107291553256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159907840 161218560 198901760 201850880 ⟨⟨104651617012, 104651617016⟩, ⟨100644965339, 108715552394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 162529280 195952640 198901760 ⟨⟨102392067111, 102392067118⟩, ⟨98418733479, 106422192071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 198901760 201850880 ⟨⟨103796937179, 103796937187⟩, ⟨99814212272, 107836406433⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 159907840) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 158597120) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 198901760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195952640) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 193003520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161218560) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 198901760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
