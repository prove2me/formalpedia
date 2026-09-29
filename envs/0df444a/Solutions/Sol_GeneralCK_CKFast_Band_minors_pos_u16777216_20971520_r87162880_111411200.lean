-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r87162880_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:17:59.40711+00:00
-- url     : https://prove2.me/submissions/6c45c136-c0d9-42c2-b385-4175d57c8850

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/40]`, `ρ ∈ [133/1280, 17/128]` by 20 cells of the computing
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
theorem cell0 : cellOK 16777216 17825792 87162880 90193920 ⟨⟨210351744597, 210351744621⟩, ⟨195935329628, 225421195056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 17825792 90193920 93224960 ⟨⟨214639271024, 214639271054⟩, ⟨200316323357, 229595176221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 17825792 18874368 87162880 90193920 ⟨⟨205657473564, 205657473586⟩, ⟨191670167259, 220266812105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 17825792 18874368 90193920 93224960 ⟨⟨209932217449, 209932217472⟩, ⟨196028988404, 224439025519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 17825792 93224960 99287040 ⟨⟨220898352929, 220898352953⟩, ⟨201417538340, 241518278647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 17825792 18874368 93224960 99287040 ⟨⟨216176332916, 216176332945⟩, ⟨197251570626, 236188498037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 18874368 19922944 87162880 90193920 ⟨⟨201187203223, 201187203245⟩, ⟨187603028324, 215364624447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 18874368 19922944 90193920 93224960 ⟨⟨205446069557, 205446069585⟩, ⟨191937522113, 219530869252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 19922944 20971520 87162880 90193920 ⟨⟨196923905873, 196923905900⟩, ⟨183719219152, 210695066247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 19922944 20971520 90193920 93224960 ⟨⟨201164258560, 201164258582⟩, ⟨188027578629, 214851731986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 18874368 19922944 93224960 99287040 ⟨⟨211670593967, 211670593990⟩, ⟨193270092389, 231110316601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 19922944 20971520 93224960 99287040 ⟨⟨207365225912, 207365225933⟩, ⟨189459906336, 226264797644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 16777216 17825792 99287040 105349120 ⟨⟨228944246558, 228944246581⟩, ⟨209726818183, 249232309791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 17825792 18874368 99287040 105349120 ⟨⟨224209103996, 224209104025⟩, ⟨205523857836, 243918430327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 16777216 17825792 105349120 111411200 ⟨⟨236675307830, 236675307853⟩, ⟨217715770027, 256642668638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 17825792 18874368 105349120 111411200 ⟨⟨231933635972, 231933636000⟩, ⟨213483830417, 251349264503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 18874368 19922944 99287040 105349120 ⟨⟨219684149661, 219684149683⟩, ⟨201501527488, 238847334593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 19922944 20971520 99287040 105349120 ⟨⟨215354297648, 215354297670⟩, ⟨197647205850, 234001214647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 18874368 19922944 105349120 111411200 ⟨⟨227396184751, 227396184778⟩, ⟨209428580715, 246290232653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 19922944 20971520 105349120 111411200 ⟨⟨223048633749, 223048633776⟩, ⟨205537946791, 241448795093⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 20971520 87162880 111411200 t = true :=
  ⟨_, (join_sr (m := 99287040) (by decide) (join_su (m := 18874368) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 17825792) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 17825792) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 93224960) (by decide) (join_su (m := 19922944) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 19922944) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 18874368) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 17825792) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 17825792) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 105349120) (by decide) (join_su (m := 19922944) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 19922944) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
