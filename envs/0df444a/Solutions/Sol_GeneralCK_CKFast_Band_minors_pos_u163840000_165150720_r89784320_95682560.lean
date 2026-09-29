-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u163840000_165150720_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:18:11.801993+00:00
-- url     : https://prove2.me/submissions/6f283ad2-ce49-4acf-a29e-8602cd6a70ee

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [25/128, 63/320]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 163840000 164167680 89784320 91258880 ⟨⟨48490247717, 48490247723⟩, ⟨47373316532, 49612784298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 164167680 164495360 89784320 91258880 ⟨⟨48382557507, 48382557513⟩, ⟨47267525259, 49503177960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 164167680 91258880 92733440 ⟨⟨49246877498, 49246877504⟩, ⟨48128394785, 50370962951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 164167680 164495360 91258880 92733440 ⟨⟨49137635387, 49137635394⟩, ⟨48021054372, 50259801990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 164495360 164823040 89784320 91258880 ⟨⟨48275145925, 48275145926⟩, ⟨47162006134, 49393856806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164823040 165150720 89784320 91258880 ⟨⟨48168011572, 48168011578⟩, ⟨47056757796, 49284819417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 164495360 164823040 91258880 92733440 ⟨⟨49028675182, 49028675187⟩, ⟨47913989385, 50148929497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 164823040 165150720 91258880 92733440 ⟨⟨48919995475, 48919995483⟩, ⟨47807198449, 50038344039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164167680 92733440 94208000 ⟨⟨50002530992, 50002531000⟩, ⟨48882501039, 51128161009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 164167680 164495360 92733440 94208000 ⟨⟨49891742699, 49891742705⟩, ⟨48773617174, 51015451179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 163840000 164167680 94208000 95682560 ⟨⟨50757212105, 50757212113⟩, ⟨49635639182, 51884382405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164167680 164495360 94208000 95682560 ⟨⟨50644883315, 50644883321⟩, ⟨49525217516, 51770129425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 164495360 164823040 92733440 94208000 ⟨⟨49781239558, 49781239561⟩, ⟨48665011978, 50903033067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 164823040 165150720 92733440 94208000 ⟨⟨49671020148, 49671020155⟩, ⟨48556684060, 50790905226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 164823040 94208000 95682560 ⟨⟨50532842892, 50532842895⟩, ⟨49415077729, 51656171380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164823040 165150720 94208000 95682560 ⟨⟨50421089400, 50421089407⟩, ⟨49305218419, 51542506809⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 163840000 165150720 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 164167680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 164167680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 164823040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 164823040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 164495360) (by decide) (join_sr (m := 94208000) (by decide) (join_su (m := 164167680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 164167680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 94208000) (by decide) (join_su (m := 164823040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 164823040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (25/128 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((163840000 : ℤ) : ℝ) / (D : ℝ)) = (25/128 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
