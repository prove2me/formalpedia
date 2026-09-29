-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:37:26.808454+00:00
-- url     : https://prove2.me/submissions/2f70287a-7490-4984-a704-3d2c238f5fb5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 225443840 231342080 ⟨⟨155854932630, 155854932638⟩, ⟨149380254861, 162456988694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 116654080 117964800 225443840 231342080 ⟨⟨154540360363, 154540360372⟩, ⟨148118707615, 161087818887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 116654080 231342080 237240320 ⟨⟨159278153912, 159278153921⟩, ⟨152785313104, 165897379205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 231342080 237240320 ⟨⟨157943102754, 157943102764⟩, ⟨151503122489, 164507929337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 117964800 119275520 225443840 231342080 ⟨⟨153240562670, 153240562678⟩, ⟨146871114954, 159734273756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119275520 120586240 225443840 231342080 ⟨⟨151955233039, 151955233047⟩, ⟨145637189631, 158396026758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 119275520 231342080 237240320 ⟨⟨156622883192, 156622883202⟩, ⟨150234953793, 163134149741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119275520 120586240 231342080 237240320 ⟨⟨155317190124, 155317190132⟩, ⟨148980520752, 161775715742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 116654080 237240320 243138560 ⟨⟨162679306029, 162679306040⟩, ⟨156168673314, 169315333524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 116654080 117964800 237240320 243138560 ⟨⟨161324193601, 161324193611⟩, ⟨154866250203, 167906027507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 116654080 243138560 249036800 ⟨⟨166058833375, 166058833386⟩, ⟨159530768166, 172711307817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 116654080 117964800 243138560 249036800 ⟨⟨164684064974, 164684064983⟩, ⟨158208511488, 171282556866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 117964800 119275520 237240320 243138560 ⟨⟨159983962387, 159983962397⟩, ⟨153577908974, 166512429946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119275520 120586240 237240320 243138560 ⟨⟨158658308818, 158658308828⟩, ⟨152303364477, 165134218159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 117964800 119275520 243138560 249036800 ⟨⟨163324220353, 163324220363⟩, ⟨156900389625, 169869545506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119275520 120586240 243138560 249036800 ⟨⟨161978997591, 161978997601⟩, ⟨155606118666, 168471953155⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 116654080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119275520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 117964800) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 116654080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 119275520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
