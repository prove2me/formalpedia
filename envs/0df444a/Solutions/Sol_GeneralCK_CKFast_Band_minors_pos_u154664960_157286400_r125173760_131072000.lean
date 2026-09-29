-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_157286400_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:23.749962+00:00
-- url     : https://prove2.me/submissions/4dcaa763-5992-45da-86cd-9638d7829967

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 3/16]`, `ρ ∈ [191/1280, 5/32]` by 9 cells of the computing
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
theorem cell0 : cellOK 154664960 155320320 125173760 128122880 ⟨⟨70862376939, 70862376947⟩, ⟨68447814540, 73300984044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 155320320 155975680 125173760 128122880 ⟨⟨70553872700, 70553872704⟩, ⟨68147862274, 72983781047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 154664960 155320320 128122880 131072000 ⟨⟨72409126442, 72409126450⟩, ⟨69988536098, 74853726637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 155320320 155975680 128122880 131072000 ⟨⟨72094663275, 72094663278⟩, ⟨69682640560, 74530549934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 155975680 156631040 125173760 128122880 ⟨⟨70246961345, 70246961351⟩, ⟨67849443146, 72668232107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 156631040 157286400 125173760 126648320 ⟨⟨69558766059, 69558766066⟩, ⟨67640782989, 71491785044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 156631040 157286400 126648320 128122880 ⟨⟨70324237159, 70324237165⟩, ⟨68403600305, 72259904421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 156631040 128122880 131072000 ⟨⟨71781815155, 71781815161⟩, ⟨69378300373, 74209049388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 156631040 157286400 128122880 131072000 ⟨⟨71470566179, 71470566187⟩, ⟨69075500280, 73889208423⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 157286400 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 155975680) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 155320320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 128122880) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell4) (join_sr (m := 126648320) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 156631040) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
