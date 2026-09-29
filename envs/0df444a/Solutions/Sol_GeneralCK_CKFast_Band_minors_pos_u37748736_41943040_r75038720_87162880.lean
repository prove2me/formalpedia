-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:36:56.791631+00:00
-- url     : https://prove2.me/submissions/00fecf98-a86c-4344-9044-e490baac6056

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 1/20]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 37748736 38797312 75038720 78069760 ⟨⟨130024824904, 130024824919⟩, ⟨120990861868, 139377668450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 38797312 78069760 81100800 ⟨⟨134016913998, 134016914013⟩, ⟨124985328260, 143361960854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 38797312 39845888 75038720 78069760 ⟨⟨127994177391, 127994177398⟩, ⟨119127846733, 137168989449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38797312 39845888 78069760 81100800 ⟨⟨131948867579, 131948867586⟩, ⟨123083442477, 141117674239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 38797312 81100800 84131840 ⟨⟨137947928010, 137947928029⟩, ⟨128919836146, 147284177681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 37748736 38797312 84131840 87162880 ⟨⟨141819857979, 141819857998⟩, ⟨132796297123, 151146386978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 38797312 39845888 81100800 84131840 ⟨⟨135844259401, 135844259408⟩, ⟨126980837090, 145006068868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 38797312 39845888 84131840 87162880 ⟨⟨139682250604, 139682250612⟩, ⟨130821852796, 148836144546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 39845888 40894464 75038720 78069760 ⟨⟨126027429685, 126027429703⟩, ⟨117322195466, 135031274191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 39845888 40894464 78069760 81100800 ⟨⟨129945060752, 129945060770⟩, ⟨121239384159, 138944543992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 40894464 41943040 75038720 78069760 ⟨⟨124121402809, 124121402827⟩, ⟨115571105100, 132960931950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 40894464 41943040 78069760 81100800 ⟨⟨128002334256, 128002334274⟩, ⟨119450359118, 136839012096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 40894464 81100800 84131840 ⟨⟨133805106622, 133805106641⟩, ⟨125100064355, 142799247768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 40894464 84131840 87162880 ⟨⟨137609376960, 137609376979⟩, ⟨128905973916, 146597265238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 40894464 41943040 81100800 84131840 ⟨⟨131827332622, 131827332640⟩, ⟨123274735302, 140660191167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 40894464 41943040 84131840 87162880 ⟨⟨135598124356, 135598124374⟩, ⟨127045891838, 144426262397⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 41943040 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 39845888) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 38797312) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 38797312) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 40894464) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 78069760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 40894464) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
