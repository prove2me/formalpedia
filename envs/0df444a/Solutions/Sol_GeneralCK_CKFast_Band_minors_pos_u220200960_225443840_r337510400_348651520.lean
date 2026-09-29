-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:10:16.054987+00:00
-- url     : https://prove2.me/submissions/e352d081-48ad-4df6-adf5-1ab9370ab10a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [103/256, 133/320]` by 10 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 337510400 343080960 ⟨⟨118058891503, 118058891511⟩, ⟨113978566704, 122195427956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221511680 222822400 337510400 343080960 ⟨⟨117092231611, 117092231617⟩, ⟨113032950091, 121207352215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 343080960 348651520 ⟨⟨119872098762, 119872098770⟩, ⟨115776541585, 124023883165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 343080960 348651520 ⟨⟨118892403404, 118892403412⟩, ⟨114817936879, 123022727869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 337510400 340295680 ⟨⟨115682787341, 115682787349⟩, ⟨112232042982, 119172911714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222822400 224133120 340295680 343080960 ⟨⟨116577097939, 116577097946⟩, ⟨113119290981, 120074308642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 225443840 337510400 340295680 ⟨⟨114728253655, 114728253663⟩, ⟨111292478365, 118203194612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 225443840 340295680 343080960 ⟨⟨115616049463, 115616049471⟩, ⟨112173232467, 119098056847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 343080960 348651520 ⟨⟨117917190081, 117917190089⟩, ⟨113863645103, 122026227340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 225443840 343080960 348651520 ⟨⟨116946399883, 116946399891⟩, ⟨112913609535, 121034320426⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221511680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 343080960) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 340295680) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 224133120) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
