-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u44040192_46137344_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:41:30.040986+00:00
-- url     : https://prove2.me/submissions/4d146f84-4d09-4bc5-b8f9-7e303b1a0cdc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/400, 11/200]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 44040192 44564480 62914560 65945600 ⟨⟨103491831361, 103491831377⟩, ⟨97852350643, 109263918401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 44564480 45088768 62914560 65945600 ⟨⟨102712769336, 102712769349⟩, ⟨97122993075, 108433036834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 44040192 44564480 65945600 68976640 ⟨⟨107497126875, 107497126892⟩, ⟨101854070662, 113270684933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44564480 45088768 65945600 68976640 ⟨⟨106697098539, 106697098553⟩, ⟨101103435227, 112419208301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 45088768 45613056 62914560 65945600 ⟨⟨101945491896, 101945491913⟩, ⟨96404505320, 107614906851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 45613056 46137344 62914560 65945600 ⟨⟨101189714994, 101189715001⟩, ⟨95696628604, 106809217377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 45088768 45613056 65945600 68976640 ⟨⟨105909019209, 105909019225⟩, ⟨100363848340, 111580631235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 45613056 46137344 65945600 68976640 ⟨⟨105132604186, 105132604193⟩, ⟨99635049930, 110754642758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 44040192 44564480 68976640 72007680 ⟨⟨111443961331, 111443961345⟩, ⟨105798207283, 117218152594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 44564480 45088768 68976640 72007680 ⟨⟨110623854205, 110623854222⟩, ⟨105027168896, 116346979260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 44040192 44564480 72007680 75038720 ⟨⟨115334140987, 115334141000⟩, ⟨109686511481, 121108182339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 44564480 45088768 72007680 75038720 ⟨⟨114494799184, 114494799197⟩, ⟨108895903153, 120218165788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 45088768 45613056 68976640 72007680 ⟨⟨109815843175, 109815843188⟩, ⟨104267340547, 115488836134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 45613056 46137344 68976640 72007680 ⟨⟨109019643295, 109019643305⟩, ⟨103518461291, 114643412732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 45088768 45613056 72007680 75038720 ⟨⟨113667684490, 113667684504⟩, ⟨108116650329, 119341294058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 45613056 46137344 72007680 75038720 ⟨⟨112852512096, 112852512098⟩, ⟨107348491572, 118477257499⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 44040192 46137344 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 45088768) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 44564480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 44564480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 45613056) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 45613056) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 45088768) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 44564480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 44564480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 45613056) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 45613056) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/400 : ℝ) (11/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((44040192 : ℤ) : ℝ) / (D : ℝ)) = (21/400 : ℝ) := by norm_num [D]
  have e1 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
