-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_77594624_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:37:14.638433+00:00
-- url     : https://prove2.me/submissions/0d2e2459-50c4-4787-b1b4-8a75d80e9a79

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 37/400]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 76021760 75038720 78069760 ⟨⟨82823575569, 82823575581⟩, ⟨79078734723, 86627639930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 76021760 76546048 75038720 78069760 ⟨⟨82396378170, 82396378179⟩, ⟨78672096425, 86179288753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 76021760 78069760 81100800 ⟨⟨85722987201, 85722987213⟩, ⟨81969995587, 89534721018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76021760 76546048 78069760 81100800 ⟨⟨85283817254, 85283817264⟩, ⟨81551366236, 89074425401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 76546048 77070336 75038720 78069760 ⟨⟨81973156494, 81973156506⟩, ⟨78269199835, 85735156583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 77070336 77594624 75038720 78069760 ⟨⟨81553849678, 81553849688⟩, ⟨77869988154, 85295178290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76546048 77070336 78069760 81100800 ⟨⟨84848698777, 84848698789⟩, ⟨81136555818, 88618422836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77070336 77594624 78069760 81100800 ⟨⟨84417570226, 84417570237⟩, ⟨80725506804, 88166647564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 76021760 81100800 84131840 ⟨⟨88598525300, 88598525312⟩, ⟨84837689960, 92417625029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 76021760 76546048 81100800 84131840 ⟨⟨88147661058, 88147661068⟩, ⟨84407343628, 91945667276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 75497472 76021760 84131840 87162880 ⟨⟨91450641982, 91450641994⟩, ⟨87682259644, 95276814425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 76021760 76546048 84131840 87162880 ⟨⟨90988353607, 90988353620⟩, ⟨87240462535, 94793468526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 76546048 77070336 81100800 84131840 ⟨⟨87700920077, 87700920087⟩, ⟨83980889558, 91478072604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 77070336 77594624 81100800 84131840 ⟨⟨87258240198, 87258240209⟩, ⟨83558269557, 91014774704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 76546048 77070336 84131840 87162880 ⟨⟨90530256496, 90530256505⟩, ⟨86802627283, 94314551897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 77070336 77594624 84131840 87162880 ⟨⟨90076287944, 90076287956⟩, ⟨86368695103, 93839997748⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 77594624 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 76546048) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 76021760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 76021760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 77070336) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 77070336) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 76546048) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 76021760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 76021760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 77070336) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 77070336) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (37/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
