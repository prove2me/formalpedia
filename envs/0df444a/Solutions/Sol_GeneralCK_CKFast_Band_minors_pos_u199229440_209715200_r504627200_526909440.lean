-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:25.282042+00:00
-- url     : https://prove2.me/submissions/8e9b2465-9ee3-4fda-9973-5e0fdd05fba5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 504627200 510197760 ⟨⟨192540458933, 192540458940⟩, ⟨184251651775, 201001558045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 510197760 515768320 ⟨⟨194451088828, 194451088837⟩, ⟨186134657269, 202939676780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 504627200 510197760 ⟨⟨189723431014, 189723431018⟩, ⟨181505387875, 198112484870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 510197760 515768320 ⟨⟨191611569121, 191611569126⟩, ⟨183365902718, 200028137632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 515768320 521338880 ⟨⟨196358793993, 196358794000⟩, ⟨188014786044, 204874817819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 521338880 526909440 ⟨⟨198263612254, 198263612261⟩, ⟨189892075206, 206807019718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 515768320 521338880 ⟨⟨193496890738, 193496890741⟩, ⟨185223646022, 201940924086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 521338880 526909440 ⟨⟨195379432007, 195379432011⟩, ⟨187078653254, 203850881053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 504627200 510197760 ⟨⟨186928409344, 186928409353⟩, ⟨178780159050, 195246401971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 510197760 515768320 ⟨⟨188794010532, 188794010541⟩, ⟨180618148490, 197139532315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 504627200 510197760 ⟨⟨184154872075, 184154872082⟩, ⟨176075465246, 192402765665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 510197760 515768320 ⟨⟨185997894205, 185997894214⟩, ⟨177890897128, 194273320564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 515768320 521338880 ⟨⟨190656900683, 190656900690⟩, ⟨182453468839, 199029904902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 521338880 526909440 ⟨⟨192517114317, 192517114326⟩, ⟨184286153986, 200917554883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 515768320 521338880 ⟨⟨187838308000, 187838308009⟩, ⟨179703759675, 196141223450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 521338880 526909440 ⟨⟨189676146419, 189676146427⟩, ⟨181514085255, 198006507869⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 504627200 526909440 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 515768320) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 510197760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 521338880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 515768320) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 510197760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 521338880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
