-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:27:10.139093+00:00
-- url     : https://prove2.me/submissions/0cbdf320-74b9-42ee-b39e-76c415b69641

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [571/2560, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 187105280 188497920 ⟨⟨62697084181, 62697084182⟩, ⟨61200452683, 64202787569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 188497920 189890560 ⟨⟨63145842938, 63145842942⟩, ⟨61647419521, 64653343282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 187105280 188497920 ⟨⟨62419161661, 62419161666⟩, ⟨60925731042, 63921633850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 188497920 189890560 ⟨⟨62866064343, 62866064350⟩, ⟨61370846213, 64370329117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 189890560 191283200 ⟨⟨63594389510, 63594389515⟩, ⟨62094174760, 65103686212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231342080 191283200 192675840 ⟨⟨64042724421, 64042724425⟩, ⟨62540718921, 65553816883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231997440 189890560 191283200 ⟨⟨63312757443, 63312757450⟩, ⟨61815752370, 64818814220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231342080 231997440 191283200 192675840 ⟨⟨63759241474, 63759241480⟩, ⟨62260450026, 65267089675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 187105280 188497920 ⟨⟨62142004546, 62142004551⟩, ⟨60651759306, 63641261227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 188497920 189890560 ⟨⟨62587054636, 62587054641⟩, ⟨61095026290, 64088099533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 187105280 188497920 ⟨⟨61865607207, 61865607212⟩, ⟨60378531962, 63361663958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 188497920 189890560 ⟨⟨62308808168, 62308808173⟩, ⟨60819954219, 63806648769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 189890560 191283200 ⟨⟨63031897718, 63031897724⟩, ⟨61538086819, 64534730266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231997440 232652800 191283200 192675840 ⟨⟨63476534300, 63476534307⟩, ⟨61980941398, 64981153938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 233308160 189890560 191283200 ⟨⟨62751804671, 62751804676⟩, ⟨61261172553, 64251428573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 191283200 192675840 ⟨⟨63194597216, 63194597221⟩, ⟨61702187465, 64696003875⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 188497920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 191283200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 189890560) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 188497920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 232652800) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 191283200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
