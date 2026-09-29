-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u211025920_212336640_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:40.135932+00:00
-- url     : https://prove2.me/submissions/17f67cd7-1291-4007-ab37-6a268bdc25aa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [161/640, 81/320]`, `ρ ∈ [3/20, 401/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 211025920 211353600 125829120 127221760 ⟨⟨48889428005, 48889428011⟩, ⟨47981500855, 49801008788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 211353600 211681280 125829120 127221760 ⟨⟨48782540770, 48782540777⟩, ⟨47875854424, 49692872338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 211025920 211353600 127221760 128614400 ⟨⟨49410339201, 49410339207⟩, ⟨48501319505, 50323013220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211353600 211681280 127221760 128614400 ⟨⟨49302381828, 49302381835⟩, ⟨48394604650, 50213804927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211681280 212008960 125829120 127221760 ⟨⟨48675839885, 48675839890⟩, ⟨47770391128, 49584925482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212008960 212336640 125829120 127221760 ⟨⟨48569324597, 48569324600⟩, ⟨47665110229, 49477167452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211681280 212008960 127221760 128614400 ⟨⟨49194612264, 49194612271⟩, ⟨48288074387, 50104787692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212008960 212336640 127221760 128614400 ⟨⟨49087029753, 49087029756⟩, ⟨48181727976, 49995960738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 211025920 211681280 128614400 130007040 ⟨⟨49876370529, 49876370531⟩, ⟨48357891121, 51404764086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 211681280 130007040 131399680 ⟨⟨50396062591, 50396062593⟩, ⟨48875603714, 51926439978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 211681280 212008960 128614400 130007040 ⟨⟨49713045316, 49713045321⟩, ⟨48805419282, 50624309605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212008960 212336640 128614400 130007040 ⟨⟨49604397620, 49604397622⟩, ⟨48698009388, 50514415777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211681280 212336640 130007040 131399680 ⟨⟨50176260845, 50176260850⟩, ⟨48659321980, 51703078903⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 211025920 212336640 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 211681280) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 211353600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 211353600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 212008960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 212008960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211681280) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 130007040) (by decide) (join_su (m := 212008960) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (161/640 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((211025920 : ℤ) : ℝ) / (D : ℝ)) = (161/640 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
