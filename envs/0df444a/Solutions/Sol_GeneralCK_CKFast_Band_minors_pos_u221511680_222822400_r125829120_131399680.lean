-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u221511680_222822400_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:42:45.520222+00:00
-- url     : https://prove2.me/submissions/3ea3140c-b621-4554-91ac-ef32af339717

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [169/640, 17/64]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 221511680 221839360 125829120 127221760 ⟨⟨45557861655, 45557861660⟩, ⟨44688110499, 46431012010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221839360 222167040 125829120 127221760 ⟨⟨45456581850, 45456581853⟩, ⟨44587974995, 46328580415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 221839360 127221760 128614400 ⟨⟨46045228680, 46045228685⟩, ⟨45174438826, 46919418750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221839360 222167040 127221760 128614400 ⟨⟨45942923096, 45942923099⟩, ⟨45073279192, 46815959736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222167040 222494720 125829120 127221760 ⟨⟨45355466027, 45355466033⟩, ⟨44488000660, 46226315652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222494720 222822400 125829120 127221760 ⟨⟨45254513546, 45254513551⟩, ⟨44388186860, 46124217058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222167040 222494720 127221760 128614400 ⟨⟨45840782806, 45840782811⟩, ⟨44972282033, 46712668868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222494720 222822400 127221760 128614400 ⟨⟨45738807163, 45738807168⟩, ⟨44871446716, 46609545477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 221839360 128614400 130007040 ⟨⟨46532313125, 46532313130⟩, ⟨45660485278, 47407542198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221839360 222167040 128614400 130007040 ⟨⟨46428983502, 46428983505⟩, ⟨45558303246, 47303057515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 221511680 221839360 130007040 131399680 ⟨⟨47019115715, 47019115722⟩, ⟨46146250580, 47895383083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221839360 222167040 130007040 131399680 ⟨⟨46914763790, 46914763793⟩, ⟨46043047877, 47789874474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222167040 222494720 128614400 130007040 ⟨⟨46325820475, 46325820482⟩, ⟨45456284989, 47198742281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222494720 222822400 128614400 130007040 ⟨⟨46222823395, 46222823400⟩, ⟨45354429870, 47094595823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222167040 222494720 130007040 131399680 ⟨⟨46810579754, 46810579759⟩, ⟨45940010241, 47684536608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222494720 222822400 130007040 131399680 ⟨⟨46706562949, 46706562956⟩, ⟨45837137027, 47579368809⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 221511680 222822400 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 221839360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221839360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222167040) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 221839360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221839360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 222494720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222494720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (169/640 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((221511680 : ℤ) : ℝ) / (D : ℝ)) = (169/640 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
