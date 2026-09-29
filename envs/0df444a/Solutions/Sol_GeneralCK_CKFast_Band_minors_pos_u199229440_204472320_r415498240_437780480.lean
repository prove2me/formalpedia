-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:54.97298+00:00
-- url     : https://prove2.me/submissions/6597c6fe-9a58-4bf0-a31d-ee9be5389b7a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 415498240 421068800 ⟨⟨162154274091, 162154274095⟩, ⟨157494444743, 166875994674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 200540160 201850880 415498240 421068800 ⟨⟨160928113251, 160928113259⟩, ⟨156292684348, 165625063369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 200540160 421068800 426639360 ⟨⟨164123233856, 164123233860⟩, ⟨159448184371, 168860104375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 421068800 426639360 ⟨⟨162884835506, 162884835514⟩, ⟨158234198383, 167596928689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 203161600 415498240 421068800 ⟨⟨159707633695, 159707633703⟩, ⟨155096413937, 164380007693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203161600 204472320 415498240 421068800 ⟨⟨158492762966, 158492762974⟩, ⟨153905563455, 163140752753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 203161600 421068800 426639360 ⟨⟨161652120296, 161652120304⟩, ⟨157025705780, 166339628826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 204472320 421068800 426639360 ⟨⟨160425016049, 160425016056⟩, ⟨155822636753, 165088130223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 200540160 426639360 432209920 ⟨⟨166088582432, 166088582436⟩, ⟨161398353907, 170840560351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 200540160 201850880 426639360 432209920 ⟨⟨164838016756, 164838016765⟩, ⟨160172211318, 169565211662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 200540160 432209920 437780480 ⟨⟨168050363811, 168050363814⟩, ⟨163344996755, 172817407177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 200540160 201850880 432209920 437780480 ⟨⟨166787699931, 166787699938⟩, ⟨162106765518, 171529955788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 426639360 432209920 ⟨⟨163593135063, 163593135071⟩, ⟨158951564520, 168295737975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 204472320 426639360 432209920 ⟨⟨162353865470, 162353865478⟩, ⟨157736343959, 167032065051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 201850880 203161600 432209920 437780480 ⟨⟨165530719891, 165530719899⟩, ⟨160874031505, 170248377576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 432209920 437780480 ⟨⟨164279352110, 164279352119⟩, ⟨159646725427, 168972598644⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 415498240 437780480 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 200540160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 421068800) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203161600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 201850880) (by decide) (join_sr (m := 432209920) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 200540160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 432209920) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203161600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
