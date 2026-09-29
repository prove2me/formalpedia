-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:29.987845+00:00
-- url     : https://prove2.me/submissions/cb6c2a52-56a7-4618-b7d3-00cf0be8cbec

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [113/320, 61/160]` by 13 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 296222720 302120960 ⟨⟨167430294016, 167430294023⟩, ⟨161655999898, 173299646989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142868480 144179200 296222720 302120960 ⟨⟨166149171626, 166149171634⟩, ⟨160414006347, 171978513141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142868480 302120960 308019200 ⟨⟨170291802890, 170291802900⟩, ⟨164500215860, 176177959352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 302120960 308019200 ⟨⟨168994589022, 168994589030⟩, ⟨163242056106, 174840825488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 145489920 296222720 302120960 ⟨⟨164878558833, 164878558843⟩, ⟨159182054589, 170668369132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 145489920 146800640 296222720 302120960 ⟨⟨163618280092, 163618280100⟩, ⟨157959977682, 169369030579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144179200 145489920 302120960 308019200 ⟨⟨167707903680, 167707903689⟩, ⟨161993962211, 173514694817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 145489920 146800640 302120960 308019200 ⟨⟨166431572198, 166431572206⟩, ⟨160755767935, 172199384013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 144179200 308019200 313917440 ⟨⟨172483195745, 172483195755⟩, ⟨163161647969, 182049256454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 313917440 319815680 ⟨⟨175312587922, 175312587931⟩, ⟨165959008914, 184909676801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 145489920 308019200 313917440 ⟨⟨170525439847, 170525439857⟩, ⟨164794239706, 176349032505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 145489920 146800640 308019200 313917440 ⟨⟨169233268338, 169233268346⟩, ⟨163540137373, 175017965461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 146800640 313917440 319815680 ⟨⟨172676169941, 172676169951⟩, ⟨163434199787, 182157814382⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 296222720 319815680 t = true :=
  ⟨_, (join_sr (m := 308019200) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 302120960) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142868480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 302120960) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 145489920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 144179200) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 313917440) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
