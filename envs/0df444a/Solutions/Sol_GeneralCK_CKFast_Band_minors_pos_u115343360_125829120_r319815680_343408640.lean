-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:32.826418+00:00
-- url     : https://prove2.me/submissions/9a61e24f-5052-4d93-89cb-e054787ac616

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 319815680 325713920 ⟨⟨207407406832, 207407406841⟩, ⟨196740981278, 218360168531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 117964800 325713920 331612160 ⟨⟨210517751114, 210517751123⟩, ⟨199824004262, 221495807960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 120586240 319815680 325713920 ⟨⟨204240639727, 204240639736⟩, ⟨193717854498, 215044804196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 325713920 331612160 ⟨⟨207320797514, 207320797523⟩, ⟨196770066684, 218151008436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 117964800 331612160 337510400 ⟨⟨213612126054, 213612126066⟩, ⟨202891418278, 224615121827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 117964800 337510400 343408640 ⟨⟨216690832733, 216690832744⟩, ⟨205943514418, 227718421251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 120586240 331612160 337510400 ⟨⟨210385505137, 210385505148⟩, ⟨199807179971, 221241413907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117964800 120586240 337510400 343408640 ⟨⟨213435049536, 213435049547⟩, ⟨202829471839, 224316317081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 123207680 319815680 325713920 ⟨⟨201132118765, 201132118774⟩, ⟨190749149916, 211791649640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 120586240 123207680 325713920 331612160 ⟨⟨204181995325, 204181995334⟩, ⟨193770510947, 214868262946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 125829120 319815680 325713920 ⟨⟨198079760080, 198079760083⟩, ⟨187832936554, 208598463194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123207680 125829120 325713920 331612160 ⟨⟨201099278820, 201099278827⟩, ⟨190823420746, 211645351817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 331612160 337510400 ⟨⟨207216927458, 207216927469⟩, ⟨196777269438, 217929591270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 120586240 123207680 337510400 343408640 ⟨⟨210237188604, 210237188615⟩, ⟨199769689866, 220975917095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 125829120 331612160 337510400 ⟨⟨204104345607, 204104345614⟩, ⟨193799785276, 214677456342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 337510400 343408640 ⟨⟨207095220990, 207095220996⟩, ⟨196762282212, 217695045889⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 319815680 343408640 t = true :=
  ⟨_, (join_su (m := 120586240) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 325713920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 117964800) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 337510400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331612160) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 325713920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 123207680) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 337510400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
