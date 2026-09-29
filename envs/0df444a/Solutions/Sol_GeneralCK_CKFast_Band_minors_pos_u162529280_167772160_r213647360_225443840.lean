-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r213647360_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:54:26.552926+00:00
-- url     : https://prove2.me/submissions/b279cfd2-b9d2-44e0-b203-b2d88f3f6c63

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [163/640, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 213647360 216596480 ⟨⟨109881279574, 109881279581⟩, ⟨105875876866, 113942669327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163840000 216596480 219545600 ⟨⟨111258931916, 111258931922⟩, ⟨107244374228, 115329429630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 165150720 213647360 216596480 ⟨⟨108993822022, 108993822030⟩, ⟨105011851668, 113031273685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 216596480 219545600 ⟨⟨110362163894, 110362163903⟩, ⟨106371058907, 114408706403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163840000 219545600 222494720 ⟨⟨112633744148, 112633744155⟩, ⟨108610065499, 116713315271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163840000 222494720 225443840 ⟨⟨114005737685, 114005737692⟩, ⟨109972971771, 118094347978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 165150720 219545600 222494720 ⟨⟨111727723507, 111727723515⟩, ⟨107727517005, 115783323201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163840000 165150720 222494720 225443840 ⟨⟨113090521669, 113090521677⟩, ⟨109081246466, 117155145202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 166461440 213647360 216596480 ⟨⟨108113718517, 108113718525⟩, ⟨104154887919, 112127532691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 166461440 216596480 219545600 ⟨⟨109472789141, 109472789148⟩, ⟨105504845035, 113495676166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167772160 213647360 216596480 ⟨⟨107240844274, 107240844277⟩, ⟨103304866326, 111231315896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166461440 167772160 216596480 219545600 ⟨⟨108590682627, 108590682631⟩, ⟨104645613044, 112590208266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 219545600 222494720 ⟨⟨110829134285, 110829134293⟩, ⟨106852108912, 114861061383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 166461440 222494720 225443840 ⟨⟨112182774177, 112182774184⟩, ⟨108196699480, 116223708874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167772160 219545600 222494720 ⟨⟨109937851236, 109937851240⟩, ⟨105983721393, 113946398983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 222494720 225443840 ⟨⟨111282369761, 111282369764⟩, ⟨107319210751, 115299907995⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 213647360 225443840 t = true :=
  ⟨_, (join_su (m := 165150720) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163840000) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 219545600) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 216596480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 166461440) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 222494720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (163/640 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
