-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r370933760_382074880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:02:44.595467+00:00
-- url     : https://prove2.me/submissions/1fa9b66e-d15a-4193-a519-35f2589a336b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [283/640, 583/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 370933760 373719040 ⟨⟨112307834111, 112307834117⟩, ⟨108974963945, 115677687685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 373719040 376504320 ⟨⟨113105645653, 113105645660⟩, ⟨109766050111, 116482258122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 370933760 373719040 ⟨⟨111333419926, 111333419932⟩, ⟨108014180994, 114689464685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 373719040 376504320 ⟨⟨112125000046, 112125000053⟩, ⟨108799058005, 115487782187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 376504320 379289600 ⟨⟨113902958923, 113902958931⟩, ⟨110556639675, 117286328437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 379289600 382074880 ⟨⟨114699776471, 114699776478⟩, ⟨111346735177, 118089901189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 376504320 379289600 ⟨⟨112916093719, 112916093727⟩, ⟨109583450079, 116285611557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 379289600 382074880 ⟨⟨113706703422, 113706703430⟩, ⟨110367359680, 117082955285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 370933760 373719040 ⟨⟨110362712392, 110362712399⟩, ⟨107057002270, 113705052364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 373719040 376504320 ⟨⟨111148067907, 111148067913⟩, ⟨107835677178, 114497123495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 370933760 373719040 ⟨⟨109395663967, 109395663969⟩, ⟨106103381449, 112724401937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 373719040 376504320 ⟨⟨110174801682, 110174801685⟩, ⟨106875861289, 113510233259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 376504320 379289600 ⟨⟨111932948590, 111932948597⟩, ⟨108613878606, 115288718273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 379289600 382074880 ⟨⟨112717356850, 112717356857⟩, ⟨109391608951, 116079839117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 376504320 379289600 ⟨⟨110953475978, 110953475982⟩, ⟨107647878907, 114295599796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 379289600 382074880 ⟨⟨111731689194, 111731689197⟩, ⟨108419436629, 115080503903⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 370933760 382074880 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 373719040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 379289600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 376504320) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 373719040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 379289600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (583/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((382074880 : ℤ) : ℝ) / (D : ℝ)) = (583/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
