-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:53.970756+00:00
-- url     : https://prove2.me/submissions/6a37608c-093d-4039-bb99-861782324420

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 148111360 149504000 ⟨⟨43616141087, 43616141092⟩, ⟨42823017924, 44412119041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250675200 251002880 148111360 149504000 ⟨⟨43512428144, 43512428149⟩, ⟨42720261914, 44307443673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250347520 250675200 149504000 150896640 ⟨⟨44015292708, 44015292713⟩, ⟨43221270768, 44812170959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 149504000 150896640 ⟨⟨43910671136, 43910671141⟩, ⟨43117607523, 44706585573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 251002880 251330560 148111360 149504000 ⟨⟨43408846987, 43408846993⟩, ⟨42617635647, 44202902155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251330560 251658240 148111360 149504000 ⟨⟨43305397128, 43305397132⟩, ⟨42515138647, 44098493980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 251002880 251330560 149504000 150896640 ⟨⟨43806182236, 43806182242⟩, ⟨43014074907, 44601134919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251330560 251658240 149504000 150896640 ⟨⟨43701825516, 43701825519⟩, ⟨42910672437, 44495818495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 250675200 150896640 152289280 ⟨⟨44414289881, 44414289886⟩, ⟨43619369352, 45212068236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250675200 251002880 150896640 152289280 ⟨⟨44308760718, 44308760724⟩, ⟨43514799909, 45105573872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 250675200 152289280 153681920 ⟨⟨44813132949, 44813132954⟩, ⟨44017314021, 45611811215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250675200 251002880 152289280 153681920 ⟨⟨44706697230, 44706697235⟩, ⟨43911839410, 45504408912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251330560 150896640 152289280 ⟨⟨44203365107, 44203365112⟩, ⟨43410361972, 44999215121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251330560 251658240 150896640 152289280 ⟨⟨44098102552, 44098102556⟩, ⟨43306055055, 44892991478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251330560 152289280 153681920 ⟨⟨44600395938, 44600395943⟩, ⟨43806497178, 45397143098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251330560 251658240 152289280 153681920 ⟨⟨44494228573, 44494228574⟩, ⟨43701286836, 45290013264⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 250675200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251330560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 251002880) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 250675200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251330560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
