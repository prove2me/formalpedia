-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_67108864_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:14:34.660809+00:00
-- url     : https://prove2.me/submissions/87a223f9-c55e-4750-8d4b-845e020a288a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 2/25]`, `ρ ∈ [61/320, 281/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 62914560 63963136 159907840 165969920 ⟨⟨175096948561, 175096948575⟩, ⟨166372050845, 184050106038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 63963136 65011712 159907840 165969920 ⟨⟨173460434961, 173460434976⟩, ⟨164830547286, 182314616664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 62914560 63963136 165969920 172032000 ⟨⟨180110289008, 180110289019⟩, ⟨171385110700, 189059193935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63963136 65011712 165969920 172032000 ⟨⟨178447942442, 178447942453⟩, ⟨169816704608, 187299098229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 65011712 66060288 159907840 165969920 ⟨⟨171851132958, 171851132963⟩, ⟨163314230380, 180608469039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 66060288 67108864 159907840 165969920 ⟨⟨170268285003, 170268285017⟩, ⟨161822407290, 178930837207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 65011712 66060288 165969920 172032000 ⟨⟨176812794192, 176812794198⟩, ⟨168273523246, 185568273315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 66060288 67108864 165969920 172032000 ⟨⟨175204096997, 175204097011⟩, ⟨166754881551, 183865906326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 63963136 172032000 178094080 ⟨⟨185053277475, 185053277489⟩, ⟨176328868490, 193996984454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 63963136 65011712 172032000 178094080 ⟨⟨183366330475, 183366330489⟩, ⟨174734788394, 192213512996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 65011712 178094080 184156160 ⟨⟨189069753463, 189069753477⟩, ⟨176296055539, 202319568384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 65011712 66060288 172032000 178094080 ⟨⟨181706546834, 181706546840⟩, ⟨173165948407, 190459221048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 66060288 67108864 172032000 178094080 ⟨⟨180073189840, 180073189851⟩, ⟨171621671608, 188733308992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 65011712 67108864 178094080 184156160 ⟨⟨185703021886, 185703021900⟩, ⟨173183021744, 198684438772⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 67108864 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 63963136) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 63963136) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 66060288) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 66060288) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 65011712) (by decide) (join_sr (m := 178094080) (by decide) (join_su (m := 63963136) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 178094080) (by decide) (join_su (m := 66060288) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
