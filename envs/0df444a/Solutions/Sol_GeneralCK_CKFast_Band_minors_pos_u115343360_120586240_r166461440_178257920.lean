-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:28:30.754605+00:00
-- url     : https://prove2.me/submissions/c73cf0b8-cf8b-4793-aaed-36273c647499

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [127/640, 17/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 166461440 169410560 ⟨⟨119380361475, 119380361485⟩, ⟨114429772173, 124416654057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 116654080 169410560 172359680 ⟨⟨121222803697, 121222803705⟩, ⟨116261853868, 126269192837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 116654080 117964800 166461440 169410560 ⟨⟨118303053031, 118303053041⟩, ⟨113392252711, 123298424241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 169410560 172359680 ⟨⟨120132629500, 120132629510⟩, ⟨115211451473, 125138125423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 116654080 172359680 175308800 ⟨⟨123058331978, 123058331988⟩, ⟨118087122969, 128114716154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 116654080 175308800 178257920 ⟨⟨124887020679, 124887020687⟩, ⟨119905652212, 129953300008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117964800 172359680 175308800 ⟨⟨121955437664, 121955437672⟩, ⟨117023980882, 126970959116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 116654080 117964800 175308800 178257920 ⟨⟨123771549571, 123771549581⟩, ⟨118829911432, 128796998952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 119275520 166461440 169410560 ⟨⟨117239409968, 117239409978⟩, ⟨112367707248, 122194576263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 119275520 169410560 172359680 ⟨⟨119056201185, 119056201195⟩, ⟨114174106822, 124021516698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 119275520 120586240 166461440 169410560 ⟨⟨116189121693, 116189121703⟩, ⟨111355843143, 121104780829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 119275520 120586240 169410560 172359680 ⟨⟨117993207778, 117993207788⟩, ⟨113149526730, 122919037169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 117964800 119275520 172359680 175308800 ⟨⟨120866366602, 120866366610⟩, ⟨115973977201, 125841734450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 117964800 119275520 175308800 178257920 ⟨⟨122669976037, 122669976047⟩, ⟨117767386703, 127655300863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 120586240 172359680 175308800 ⟨⟨119790807514, 119790807523⟩, ⟨114936818266, 124726712540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119275520 120586240 175308800 178257920 ⟨⟨121581988561, 121581988569⟩, ⟨116717783973, 126527876065⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 117964800) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 116654080) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 175308800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172359680) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 169410560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 119275520) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 175308800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
