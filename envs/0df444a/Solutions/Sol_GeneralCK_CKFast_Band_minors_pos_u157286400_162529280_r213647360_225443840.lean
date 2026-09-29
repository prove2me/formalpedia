-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r213647360_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:54:02.90984+00:00
-- url     : https://prove2.me/submissions/fc750154-bcda-4310-a557-25eeb0a67d5e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [163/640, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 213647360 216596480 ⟨⟨113507245547, 113507245555⟩, ⟨109405072612, 117667512081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 158597120 216596480 219545600 ⟨⟨114922536592, 114922536601⟩, ⟨110811135830, 119091970019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 158597120 159907840 213647360 216596480 ⟨⟨112589066790, 112589066798⟩, ⟨108511554392, 116724133236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 216596480 219545600 ⟨⟨113994888186, 113994888194⟩, ⟨109908164815, 118139108309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 158597120 219545600 222494720 ⟨⟨116334745074, 116334745083⟩, ⟨112214154262, 120513307074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 158597120 222494720 225443840 ⟨⟨117743894984, 117743894993⟩, ⟨113614151523, 121931547612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159907840 219545600 222494720 ⟨⟨115397689335, 115397689343⟩, ⟨111301791803, 119551025779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 158597120 159907840 222494720 225443840 ⟨⟨116797493555, 116797493564⟩, ⟨112692458311, 120959909328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 161218560 213647360 216596480 ⟨⟨111678770018, 111678770022⟩, ⟨107625602137, 115788961127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 161218560 216596480 219545600 ⟨⟨113075161893, 113075161898⟩, ⟨109012800827, 117194492422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161218560 162529280 213647360 216596480 ⟨⟨110776218752, 110776218759⟩, ⟨106747085462, 114861853000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161218560 162529280 216596480 219545600 ⟨⟨112163221016, 112163221025⟩, ⟨108124913219, 116257979433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 219545600 222494720 ⟨⟨114468594688, 114468594694⟩, ⟨110397076298, 118597028233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159907840 161218560 222494720 225443840 ⟨⟨115859091069, 115859091072⟩, ⟨111778450868, 119996591570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 162529280 219545600 222494720 ⟨⟨113547324241, 113547324249⟩, ⟨109499876865, 117651171354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 222494720 225443840 ⟨⟨114928550454, 114928550462⟩, ⟨110871998097, 119041451126⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 213647360 225443840 t = true :=
  ⟨_, (join_su (m := 159907840) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 158597120) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 219545600) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 216596480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161218560) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 222494720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (163/640 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
