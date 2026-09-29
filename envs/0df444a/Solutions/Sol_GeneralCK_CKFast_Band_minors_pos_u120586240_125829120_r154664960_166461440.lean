-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:28:39.960194+00:00
-- url     : https://prove2.me/submissions/348a45fe-d447-4b31-b9ed-f54c32443dcc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 154664960 157614080 ⟨⟨107921202990, 107921202994⟩, ⟨103168283252, 112756329700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 120586240 121896960 157614080 160563200 ⟨⟨109738736748, 109738736752⟩, ⟨104975024042, 114584435615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 121896960 123207680 154664960 157614080 ⟨⟨106948291778, 106948291786⟩, ⟨102232498089, 111745217799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 157614080 160563200 ⟨⟨108752724220, 108752724230⟩, ⟨104026141844, 113560227711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 121896960 160563200 163512320 ⟨⟨111549649377, 111549649381⟩, ⟨106775241547, 116405822120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 120586240 121896960 163512320 166461440 ⟨⟨113354010061, 113354010065⟩, ⟨108569003462, 118220559911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 121896960 123207680 160563200 163512320 ⟨⟨110550677543, 110550677553⟩, ⟨105813401879, 115368662631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 121896960 123207680 163512320 166461440 ⟨⟨112342218760, 112342218768⟩, ⟨107594343775, 117170591030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 124518400 154664960 157614080 ⟨⟨105987513781, 105987513789⟩, ⟨101308212897, 110746895989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 123207680 124518400 157614080 160563200 ⟨⟨107778935778, 107778935786⟩, ⟨103088852931, 112548897965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 124518400 125829120 154664960 157614080 ⟨⟨105038596740, 105038596748⟩, ⟨100395171591, 109761075133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 124518400 125829120 157614080 160563200 ⟨⟨106817098378, 106817098386⟩, ⟨102162900306, 111550156610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 124518400 160563200 163512320 ⟨⟨109564017541, 109564017549⟩, ⟨104863245740, 114344466203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 124518400 163512320 166461440 ⟨⟨111342823982, 111342823991⟩, ⟨106631454854, 116133667011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 124518400 125829120 160563200 163512320 ⟨⟨108589395620, 108589395630⟩, ⟨103924515290, 113332942505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 124518400 125829120 163512320 166461440 ⟨⟨110355551351, 110355551360⟩, ⟨105680078102, 115109497038⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 123207680) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 121896960) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 121896960) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 160563200) (by decide) (join_su (m := 124518400) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 124518400) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
