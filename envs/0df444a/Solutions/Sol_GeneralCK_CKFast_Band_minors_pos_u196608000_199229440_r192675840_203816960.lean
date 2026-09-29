-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:07:36.319908+00:00
-- url     : https://prove2.me/submissions/0d78d78f-51ab-4ac7-87eb-1ac78ad85d6d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 192675840 195461120 ⟨⟨80835923028, 80835923035⟩, ⟨78799306136, 82888730289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 197263360 197918720 192675840 195461120 ⟨⟨80499829302, 80499829308⟩, ⟨78469060466, 82546715875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 196608000 197263360 195461120 198246400 ⟨⟨81933221900, 81933221906⟩, ⟨79892191954, 83990439984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 195461120 198246400 ⟨⟨81593038714, 81593038720⟩, ⟨79557866837, 83644326389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 197918720 198574080 192675840 195461120 ⟨⟨80164893410, 80164893414⟩, ⟨78139941838, 82205890603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 198574080 199229440 192675840 195461120 ⟨⟨79831106277, 79831106283⟩, ⟨77811941439, 81866245140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 195461120 198246400 ⟨⟨81254022188, 81254022193⟩, ⟨79224677614, 83299410732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 198574080 199229440 195461120 198246400 ⟨⟨80916163204, 80916163211⟩, ⟨78892615427, 82955683638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197263360 198246400 201031680 ⟨⟨83028985424, 83028985432⟩, ⟨80983552218, 85090604430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197263360 197918720 198246400 201031680 ⟨⟨82684729799, 82684729807⟩, ⟨80645164515, 84740408834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197263360 201031680 203816960 ⟨⟨84123222645, 84123222651⟩, ⟨82073395901, 86189232737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197263360 197918720 201031680 203816960 ⟨⟨83774911468, 83774911476⟩, ⟨81730962342, 85834972187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 197918720 198574080 198246400 201031680 ⟨⟨82341649498, 82341649502⟩, ⟨80307921398, 84391419809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 198574080 199229440 198246400 201031680 ⟨⟨81999735357, 81999735364⟩, ⟨79971813961, 84043627936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 198574080 201031680 203816960 ⟨⟨83427784117, 83427784121⟩, ⟨81389681899, 85481926677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 198574080 199229440 201031680 203816960 ⟨⟨83081831387, 83081831393⟩, ⟨81049545625, 85130086746⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 197263360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 198574080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 197918720) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 197263360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 198574080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
