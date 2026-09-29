-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:18:49.573514+00:00
-- url     : https://prove2.me/submissions/f97f43b2-d755-4589-bc40-2ce42e7f2171

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [173/1280, 91/640]` by 10 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 113377280 116326400 ⟨⟨71946893732, 71946893736⟩, ⟨69333324657, 74588754943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 139591680 140247040 113377280 116326400 ⟨⟨71621621648, 71621621657⟩, ⟨69018201742, 74253140852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 139591680 116326400 119275520 ⟨⟨73665836143, 73665836147⟩, ⟨71045672360, 76314231411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 116326400 119275520 ⟨⟨73333773063, 73333773070⟩, ⟨70723774983, 75971811148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 140247040 140902400 113377280 114851840 ⟨⟨70871070296, 70871070304⟩, ⟨68809693258, 72949937279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140247040 140902400 114851840 116326400 ⟨⟨71725143311, 71725143318⟩, ⟨69660872730, 73806891573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 140902400 141557760 113377280 114851840 ⟨⟨70551330258, 70551330265⟩, ⟨68497181334, 72622860107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140902400 141557760 114851840 116326400 ⟨⟨71402021129, 71402021136⟩, ⟨69344985895, 73476425378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 140247040 140902400 116326400 119275520 ⟨⟨73003669196, 73003669203⟩, ⟨70403757612, 75631431357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 140902400 141557760 116326400 119275520 ⟨⟨72675503278, 72675503284⟩, ⟨70085599942, 75293069788⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 140247040) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 139591680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 116326400) (by decide) (join_su (m := 140902400) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 114851840) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 140902400) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
