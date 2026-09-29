-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:29:55.056335+00:00
-- url     : https://prove2.me/submissions/685ed579-2216-46aa-92e9-cb9387c6139d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 148111360 150896640 ⟨⟨71012198858, 71012198859⟩, ⟨68875205271, 73167831182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178913280 179568640 148111360 150896640 ⟨⟨70712494780, 70712494788⟩, ⟨68582155817, 72861375933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 178913280 150896640 153681920 ⟨⟨72263069340, 72263069343⟩, ⟨70121138119, 74423629053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 150896640 153681920 ⟨⟨71958624880, 71958624888⟩, ⟨69823360966, 74112421170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 179568640 180224000 148111360 150896640 ⟨⟨70414049484, 70414049491⟩, ⟨68290325178, 72556220224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180224000 180879360 148111360 150896640 ⟨⟨70116852010, 70116852017⟩, ⟨67999702779, 72252352713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 150896640 153681920 ⟨⟨71655453155, 71655453162⟩, ⟨69526816601, 73802526758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180224000 180879360 150896640 153681920 ⟨⟨71353543120, 71353543126⟩, ⟨69231494356, 73493934387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 178913280 153681920 156467200 ⟨⟨73511622457, 73511622461⟩, ⟨71364770819, 75677092197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 178913280 179568640 153681920 156467200 ⟨⟨73202463360, 73202463368⟩, ⟨71062291450, 75361157688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 178913280 156467200 159252480 ⟨⟨74757873560, 74757873563⟩, ⟨72606118576, 76928236110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 178913280 179568640 156467200 159252480 ⟨⟨74444025337, 74444025343⟩, ⟨72298962243, 76607600747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 179568640 180224000 153681920 156467200 ⟨⟨72894590687, 72894590693⟩, ⟨70761058578, 75046550311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180224000 180879360 153681920 156467200 ⟨⟨72587993307, 72587993314⟩, ⟨70461061451, 74733258556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 179568640 180224000 156467200 159252480 ⟨⟨74131476965, 74131476971⟩, ⟨71993065859, 76288305913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 180224000 180879360 156467200 159252480 ⟨⟨73820217234, 73820217240⟩, ⟨71688418589, 75970340019⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 178913280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 180224000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 179568640) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 178913280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 180224000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
