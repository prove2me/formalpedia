-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:55:52.174217+00:00
-- url     : https://prove2.me/submissions/6e0e2d13-8d1d-48dd-abfd-8fed67dc40fb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 292945920 295731200 ⟨⟨102979467140, 102979467146⟩, ⟨99612779723, 106385589694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 295731200 298516480 ⟨⟨103899683115, 103899683121⟩, ⟨100525805917, 107313021054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 292945920 295731200 ⟨⟨102123012069, 102123012075⟩, ⟨98771191680, 105514032799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 295731200 298516480 ⟨⟨103036408450, 103036408457⟩, ⟨99677422568, 106434621244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 298516480 301301760 ⟨⟨104819063543, 104819063549⟩, ⟨101438002201, 108239610983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 221511680 301301760 304087040 ⟨⟨105737612864, 105737612871⟩, ⟨102349372986, 109165363956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 298516480 301301760 ⟨⟨103948987999, 103948988007⟩, ⟨100582841997, 107354387240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221511680 222822400 301301760 304087040 ⟨⟨104860755036, 104860755042⟩, ⟨101487454259, 108273335139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 292945920 295731200 ⟨⟨101270815818, 101270815824⟩, ⟨97933729319, 104646870496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222822400 224133120 295731200 298516480 ⟨⟨102177407417, 102177407423⟩, ⟨98833179939, 105560630583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 292945920 295731200 ⟨⟨100422820237, 100422820245⟩, ⟨97100336315, 103784042772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 225443840 295731200 298516480 ⟨⟨101322621785, 101322621791⟩, ⟨97993021620, 104690988984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 298516480 301301760 ⟨⟨103083200568, 103083200576⟩, ⟨99731837231, 106473586867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222822400 224133120 301301760 304087040 ⟨⟨103988199473, 103988199479⟩, ⟨100629705365, 107385743577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 298516480 301301760 ⟨⟨102221642946, 102221642952⟩, ⟨98884931408, 105597149708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 301301760 304087040 ⟨⟨103119887801, 103119887807⟩, ⟨99776069730, 106502529057⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 301301760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 298516480) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 295731200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224133120) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 301301760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
