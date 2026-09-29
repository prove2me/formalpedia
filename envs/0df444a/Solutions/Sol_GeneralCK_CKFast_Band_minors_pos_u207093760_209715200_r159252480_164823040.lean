-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:04:53.903004+00:00
-- url     : https://prove2.me/submissions/21025917-e85f-4dff-9db0-285b205b8514

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 159252480 160645120 ⟨⟨62832551581, 62832551587⟩, ⟨61248635372, 64426708784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207093760 207749120 160645120 162037760 ⟨⟨63357322924, 63357322931⟩, ⟨61771426798, 64953463654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207749120 208404480 159252480 160645120 ⟨⟨62563596815, 62563596817⟩, ⟨60983431204, 64153963513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 160645120 162037760 ⟨⟨63086295666, 63086295669⟩, ⟨61504155120, 64678640967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 207749120 162037760 163430400 ⟨⟨63881750188, 63881750195⟩, ⟨62293875603, 65479872963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 207749120 163430400 164823040 ⟨⟨64405834332, 64405834339⟩, ⟨62815982744, 66005937676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207749120 208404480 162037760 163430400 ⟨⟨63608654439, 63608654442⟩, ⟨62024540389, 65202976891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207749120 208404480 163430400 164823040 ⟨⟨64130674075, 64130674078⟩, ⟨62544587950, 65726972233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 208404480 209059840 159252480 160645120 ⟨⟨62295552937, 62295552943⟩, ⟨60719117495, 63882149855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 208404480 209059840 160645120 162037760 ⟨⟨62816184309, 62816184316⟩, ⟨61237778912, 64404754910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209059840 209715200 159252480 160645120 ⟨⟨62028412780, 62028412786⟩, ⟨60455687243, 63611260464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 209059840 209715200 160645120 162037760 ⟨⟨62546981655, 62546981661⟩, ⟨60972291137, 64131798106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 162037760 163430400 ⟨⟨63336479561, 63336479568⟩, ⟨61756105611, 64927022423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209059840 163430400 164823040 ⟨⟨63856439625, 63856439630⟩, ⟨62274098521, 65448953328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 209059840 209715200 162037760 163430400 ⟨⟨63065218330, 63065218336⟩, ⟨61488564207, 64652002153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 163430400 164823040 ⟨⟨63583123721, 63583123727⟩, ⟨62004507364, 65171873527⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 208404480) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 207749120) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 207749120) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 209059840) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 160645120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 209059840) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
