-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:51:38.219488+00:00
-- url     : https://prove2.me/submissions/4ce1635f-ff1a-4ea3-b63b-04742b39d7d4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [71/256, 49/160]` by 10 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 232652800 244776960 ⟨⟨276324052468, 276324052484⟩, ⟨255304589446, 298287302047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 44040192 46137344 232652800 244776960 ⟨⟨271256616622, 271256616638⟩, ⟨250708661334, 292720102910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 44040192 244776960 256901120 ⟨⟨285288532199, 285288532216⟩, ⟨264411671115, 307060578520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 244776960 256901120 ⟨⟨280189767909, 280189767922⟩, ⟨259768134914, 301481284940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 48234496 232652800 238714880 ⟨⟨264100255209, 264100255225⟩, ⟨249104038256, 279601420338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 48234496 238714880 244776960 ⟨⟨268606447693, 268606447707⟩, ⟨253642863251, 284063347583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 48234496 50331648 232652800 238714880 ⟨⟨259376425625, 259376425641⟩, ⟨244696546407, 274546898203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 48234496 50331648 238714880 244776960 ⟨⟨263861702812, 263861702828⟩, ⟨249209417097, 278993668655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 48234496 244776960 256901120 ⟨⟨275258411271, 275258411288⟩, ⟨255272927874, 296089472414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 48234496 50331648 244776960 256901120 ⟨⟨270484870117, 270484870133⟩, ⟨250917698195, 290874266463⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 46137344) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 44040192) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 244776960) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 238714880) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 48234496) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
