-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_77594624_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:40.813197+00:00
-- url     : https://prove2.me/submissions/462c1172-d3cf-4bd4-b015-79341f119a52

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 37/400]`, `ρ ∈ [133/1280, 303/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 75497472 76021760 87162880 90193920 ⟨⟨94279777548, 94279777560⟩, ⟨90504135012, 98112739456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 76021760 76546048 87162880 90193920 ⟨⟨93806327399, 93806327409⟩, ⟨90051145741, 97618271381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 76021760 90193920 93224960 ⟨⟨97086360884, 97086360896⟩, ⟨93303735400, 100925838577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76021760 76546048 90193920 93224960 ⟨⟨96602003791, 96602003801⟩, ⟨92839805255, 100420506569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 76546048 77070336 87162880 90193920 ⟨⟨93337132889, 93337132899⟩, ⟨89602184348, 97128295098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 77070336 77594624 87162880 90193920 ⟨⟨92872130837, 92872130846⟩, ⟨89157191509, 96642743396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76546048 77070336 90193920 93224960 ⟨⟨96121963242, 96121963251⟩, ⟨92379965580, 99919725366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77070336 77594624 90193920 93224960 ⟨⟨95646175629, 95646175641⟩, ⟨91924156574, 99423427388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 76546048 93224960 96256000 ⟨⟨99622750801, 99622750810⟩, ⟨94072889543, 105295793629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 75497472 76546048 96256000 99287040 ⟨⟨102380256368, 102380256378⟩, ⟨96818740074, 108064070236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 76546048 77594624 93224960 96256000 ⟨⟨98641450109, 98641450121⟩, ⟨93148015899, 104255827742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 76546048 77594624 96256000 99287040 ⟨⟨101378226734, 101378226746⟩, ⟨95873051782, 107003495736⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 77594624 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 76546048) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 76021760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 76021760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 90193920) (by decide) (join_su (m := 77070336) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 77070336) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 76546048) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 96256000) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (37/400 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
