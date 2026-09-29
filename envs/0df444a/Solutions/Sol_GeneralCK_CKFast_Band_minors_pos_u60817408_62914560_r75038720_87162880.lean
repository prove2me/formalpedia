-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u60817408_62914560_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:04:01.053561+00:00
-- url     : https://prove2.me/submissions/c3de0778-eb94-40e0-9525-fa18e0b4453a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/400, 3/40]`, `ρ ∈ [229/2560, 133/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 60817408 61341696 75038720 78069760 ⟨⟨96694152152, 96694152166⟩, ⟨92258514973, 101210423051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 61341696 61865984 75038720 78069760 ⟨⟨96124494351, 96124494365⟩, ⟨91718108686, 100610552516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 60817408 61341696 78069760 81100800 ⟨⟨99962403191, 99962403202⟩, ⟨95520015700, 104484548303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 61341696 61865984 78069760 81100800 ⟨⟨99378365161, 99378365175⟩, ⟨94965138316, 103870408099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 61865984 62390272 75038720 78069760 ⟨⟨95561206008, 95561206019⟩, ⟨91183671185, 100017469883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62390272 62914560 75038720 78069760 ⟨⟨95004171620, 95004171633⟩, ⟨90655095269, 99431050904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 61865984 62390272 78069760 81100800 ⟨⟨98800792149, 98800792160⟩, ⟨94416329315, 103263146778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 62390272 62914560 78069760 81100800 ⟨⟨98229567972, 98229567983⟩, ⟨93873480675, 102662639569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 60817408 61341696 81100800 84131840 ⟨⟨103197045274, 103197045285⟩, ⟨98748358576, 107724623676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 61341696 61865984 81100800 84131840 ⟨⟨102599051696, 102599051707⟩, ⟨98179428655, 107096644210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 60817408 61865984 84131840 87162880 ⟨⟨106092240510, 106092240524⟩, ⟨99625037215, 112727481242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 61865984 62390272 81100800 84131840 ⟨⟨102007612004, 102007612018⟩, ⟨97616660111, 106475627854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62390272 62914560 81100800 84131840 ⟨⟨101422609470, 101422609481⟩, ⟨97059944216, 105861449459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 61865984 62914560 84131840 87162880 ⟨⟨104882404881, 104882404892⟩, ⟨98495310778, 111433810895⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 60817408 62914560 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 61865984) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 61341696) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 61341696) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 62390272) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 62390272) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 61865984) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 61341696) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 84131840) (by decide) (join_su (m := 62390272) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/400 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((60817408 : ℤ) : ℝ) / (D : ℝ)) = (29/400 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
