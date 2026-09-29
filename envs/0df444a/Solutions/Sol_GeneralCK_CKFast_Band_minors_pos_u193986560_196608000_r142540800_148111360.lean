-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:40:54.508527+00:00
-- url     : https://prove2.me/submissions/d23218f1-22ff-4777-8d11-27df838fbf04

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 142540800 143933440 ⟨⟨61572491300, 61572491306⟩, ⟨59934127194, 63221932144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 194641920 143933440 145326080 ⟨⟨62145114771, 62145114777⟩, ⟨60504644448, 63796664285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 194641920 195297280 142540800 143933440 ⟨⟨61310240694, 61310240697⟩, ⟨59676010843, 62955499950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 143933440 145326080 ⟨⟨61880624474, 61880624477⟩, ⟨60244293891, 63527986995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 194641920 145326080 146718720 ⟨⟨62717289067, 62717289073⟩, ⟨61074714737, 64370945017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 194641920 146718720 148111360 ⟨⟨63289015542, 63289015548⟩, ⟨61644339406, 64944775701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 194641920 195297280 145326080 146718720 ⟨⟨62450564221, 62450564223⟩, ⟨60812135076, 64100027813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 194641920 195297280 146718720 148111360 ⟨⟨63020061267, 63020061270⟩, ⟨61379535724, 64671623743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 195297280 195952640 142540800 143933440 ⟨⟨61048988403, 61048988409⟩, ⟨59418868630, 62690090624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 195952640 143933440 145326080 ⟨⟨61617138760, 61617138767⟩, ⟨59984923734, 63260338846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 195952640 196608000 142540800 143933440 ⟨⟨60788726141, 60788726146⟩, ⟨59162692477, 62425695658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195952640 196608000 143933440 145326080 ⟨⟨61354649303, 61354649310⟩, ⟨59726525860, 62993711289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 145326080 146718720 ⟨⟨62184850173, 62184850179⟩, ⟨60550542026, 63830145969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195297280 195952640 146718720 148111360 ⟨⟨62752123953, 62752123959⟩, ⟨61115724810, 64399513311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195952640 196608000 145326080 146718720 ⟨⟨61920138557, 61920138563⟩, ⟨60289927427, 63561290896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 146718720 148111360 ⟨⟨62485195195, 62485195202⟩, ⟨60852898467, 64128435777⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 195297280) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 194641920) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 143933440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 194641920) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 146718720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 145326080) (by decide) (join_su (m := 195952640) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 143933440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 195952640) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 146718720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
