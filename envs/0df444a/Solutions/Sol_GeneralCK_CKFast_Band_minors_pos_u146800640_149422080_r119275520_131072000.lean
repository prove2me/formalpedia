-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:09:49.404934+00:00
-- url     : https://prove2.me/submissions/a9c1aa50-5ff2-4a61-89cc-56f54f2c80c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [91/640, 5/32]` by 17 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 119275520 122224640 ⟨⟨71440299283, 71440299290⟩, ⟨68930755371, 73975860152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 147456000 148111360 119275520 122224640 ⟨⟨71124008381, 71124008389⟩, ⟨68623756652, 73650109482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 147456000 122224640 125173760 ⟨⟨73069899725, 73069899732⟩, ⟨70554056050, 75611714050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147456000 148111360 122224640 125173760 ⟨⟨72747263899, 72747263906⟩, ⟨70240728526, 75279603426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 148111360 148766720 119275520 122224640 ⟨⟨70809466545, 70809466553⟩, ⟨68318438432, 73326178157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 148766720 149422080 119275520 120750080 ⟨⟨70093265609, 70093265611⟩, ⟨68110403165, 72092253993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148766720 149422080 120750080 122224640 ⟨⟨70899753188, 70899753193⟩, ⟨68914125690, 72901498275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148111360 148766720 122224640 125173760 ⟨⟨72426402492, 72426402499⟩, ⟨69929106924, 74949337410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 148766720 149422080 122224640 125173760 ⟨⟨72107297193, 72107297195⟩, ⟨69619173716, 74620896878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 146800640 147456000 125173760 128122880 ⟨⟨74694700692, 74694700701⟩, ⟨72172601897, 77242723622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 147456000 148111360 125173760 128122880 ⟨⟨74365773984, 74365773991⟩, ⟨71852998969, 76904307723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 146800640 147456000 128122880 131072000 ⟨⟨76314744653, 76314744660⟩, ⟨73786434820, 78868931896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 147456000 148111360 128122880 131072000 ⟨⟨75979580416, 75979580424⟩, ⟨73460609214, 78524264708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 148111360 148766720 125173760 128122880 ⟨⟨74038646431, 74038646437⟩, ⟨71535126775, 76567761075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148766720 149422080 125173760 128122880 ⟨⟨73713299543, 73713299548⟩, ⟨71218967610, 76233064377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148111360 148766720 128122880 131072000 ⟨⟨75646239471, 75646239477⟩, ⟨73136538563, 78181490803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 148766720 149422080 128122880 131072000 ⟨⟨75314703153, 75314703158⟩, ⟨72814204986, 77840590707⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 147456000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell4) (join_sr (m := 120750080) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 148766720) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 148111360) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 147456000) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 128122880) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 148766720) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
