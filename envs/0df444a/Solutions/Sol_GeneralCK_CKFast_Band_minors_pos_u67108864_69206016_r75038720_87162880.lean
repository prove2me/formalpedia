-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_69206016_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:26:08.228995+00:00
-- url     : https://prove2.me/submissions/0fe1f9a9-5f31-4e2d-bc42-5cbec93d04b2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 33/400]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 67633152 75038720 78069760 ⟨⟨90254571155, 90254571166⟩, ⟨86145228245, 94434094805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67633152 68157440 75038720 78069760 ⟨⟨89754307303, 89754307316⟩, ⟨85669909558, 93908111335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 67633152 78069760 81100800 ⟨⟨93356413376, 93356413389⟩, ⟨89239466881, 97542868901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 67633152 68157440 78069760 81100800 ⟨⟨92842869786, 92842869796⟩, ⟨88750817553, 97003670868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 68157440 68681728 75038720 78069760 ⟨⟨89259196436, 89259196446⟩, ⟨85199429391, 93387608568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 68681728 69206016 75038720 78069760 ⟨⟨88769151965, 88769151978⟩, ⟨84733707190, 92872493583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 68157440 68681728 78069760 81100800 ⟨⟨92334566237, 92334566250⟩, ⟨88267096413, 96470037630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 68681728 69206016 78069760 81100800 ⟨⟨91831415428, 91831415441⟩, ⟨87788222093, 95941875642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 67633152 81100800 84131840 ⟨⟨96429328674, 96429328684⟩, ⟨92305161223, 100622339868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 67633152 68157440 81100800 84131840 ⟨⟨95902857745, 95902857758⟩, ⟨91803528424, 100070284673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 67633152 84131840 87162880 ⟨⟨99473925547, 99473925560⟩, ⟨95342905018, 103673130973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 67633152 68157440 84131840 87162880 ⟨⟨98934868213, 98934868226⟩, ⟨94828624776, 103108564204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 68157440 68681728 81100800 84131840 ⟨⟨95381708618, 95381708631⟩, ⟨91306908247, 99523872989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 68681728 69206016 81100800 84131840 ⟨⟨94865793360, 94865793370⟩, ⟨90815218611, 98983010760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 68157440 68681728 84131840 87162880 ⟨⟨98401209382, 98401209392⟩, ⟨94319436604, 102549714565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 68681728 69206016 84131840 87162880 ⟨⟨97872860589, 97872860602⟩, ⟨93815257790, 101996487566⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 69206016 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 68157440) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 67633152) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 67633152) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 68681728) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 68681728) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 68157440) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 67633152) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 67633152) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 68681728) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 68681728) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (33/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
