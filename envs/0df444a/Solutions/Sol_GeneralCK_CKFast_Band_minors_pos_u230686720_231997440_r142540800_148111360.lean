-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_231997440_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:26:07.52123+00:00
-- url     : https://prove2.me/submissions/aaca1000-d49e-44d1-95a6-4b1348f01933

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 177/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231014400 142540800 143933440 ⟨⟨48275952717, 48275952722⟩, ⟨47425326223, 49129793093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231014400 231342080 142540800 143933440 ⟨⟨48167239722, 48167239728⟩, ⟨47317701402, 49019985225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231014400 143933440 145326080 ⟨⟨48732271492, 48732271498⟩, ⟨47880657649, 49587100404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231014400 231342080 143933440 145326080 ⟨⟨48622585517, 48622585522⟩, ⟨47772061361, 49476318050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231342080 231669760 142540800 143933440 ⟨⟨48058687513, 48058687520⟩, ⟨47210234823, 48910340709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231669760 231997440 142540800 143933440 ⟨⟨47950295479, 47950295482⟩, ⟨47102925887, 48800858922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231669760 143933440 145326080 ⟨⟨48513061428, 48513061434⟩, ⟨47663624414, 49365700151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231669760 231997440 143933440 145326080 ⟨⟨48403698612, 48403698614⟩, ⟨47555346203, 49255246078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231014400 145326080 146718720 ⟨⟨49188359979, 49188359984⟩, ⟨48335759280, 50044176929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231014400 231342080 145326080 146718720 ⟨⟨49077702467, 49077702473⟩, ⟨48226192963, 49932421540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231014400 146718720 148111360 ⟨⟨49644218740, 49644218746⟩, ⟨48790631679, 50501023234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231014400 231342080 146718720 148111360 ⟨⟨49532591134, 49532591139⟩, ⟨48680096768, 50388296256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231342080 231669760 145326080 146718720 ⟨⟨48967207936, 48967207941⟩, ⟨48116787079, 49820831700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231669760 231997440 145326080 146718720 ⟨⟨48856875767, 48856875768⟩, ⟨48007541019, 49709406777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231342080 231669760 146718720 148111360 ⟨⟨49421127592, 49421127599⟩, ⟨48569723373, 50275735915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 231669760 231997440 146718720 148111360 ⟨⟨49309827495, 49309827498⟩, ⟨48459510882, 50163341575⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 231997440 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231014400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 231669760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231342080) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231014400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 231669760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (177/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
