-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r744488960_791674880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:59:02.289349+00:00
-- url     : https://prove2.me/submissions/dd80fbf7-ffb2-4728-ac2f-24915bd99fbf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [71/80, 151/160]` by 13 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 744488960 756285440 ⟨⟨369411686282, 369411686286⟩, ⟨355724776934, 383323843669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 744488960 756285440 ⟨⟨365118594400, 365118594411⟩, ⟨351549141744, 378914189855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 141557760 756285440 768081920 ⟨⟨371956732803, 371956732814⟩, ⟨349322290467, 395208402122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 141557760 144179200 744488960 756285440 ⟨⟨360856260559, 360856260571⟩, ⟨347403239439, 374536230309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 146800640 744488960 756285440 ⟨⟨356623961387, 356623961398⟩, ⟨343286364376, 370189227415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 144179200 756285440 768081920 ⟨⟨365504038900, 365504038911⟩, ⟨352007555981, 379223328888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144179200 146800640 756285440 768081920 ⟨⟨361239311043, 361239311055⟩, ⟨347857106565, 374845196343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 136314880 141557760 768081920 779878400 ⟨⟨376639544351, 376639544364⟩, ⟨353919080814, 399965989115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 141557760 779878400 791674880 ⟨⟨381310260516, 381310260527⟩, ⟨358504137245, 404711036366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 768081920 779878400 ⟨⟨370139566241, 370139566252⟩, ⟨356599844922, 383897934908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 146800640 768081920 779878400 ⟨⟨365842689524, 365842689536⟩, ⟨352416101642, 379488950332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 141557760 144179200 779878400 791674880 ⟨⟨374763394590, 374763394601⟩, ⟨361180644283, 388560613378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 146800640 779878400 791674880 ⟨⟨370434632867, 370434632880⟩, ⟨356963871957, 384121038182⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 744488960 791674880 t = true :=
  ⟨_, (join_sr (m := 768081920) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 756285440) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 756285440) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 144179200) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 141557760) (by decide) (join_sr (m := 779878400) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 779878400) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 144179200) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (71/80 : ℝ) (151/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  have e3 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
