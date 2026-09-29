-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:53:58.941982+00:00
-- url     : https://prove2.me/submissions/71fdba55-8a6b-4775-aa54-36daabf524e3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 281804800 284590080 ⟨⟨99290158223, 99290158229⟩, ⟨95952286977, 102667359746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 284590080 287375360 ⟨⟨100213761207, 100213761214⟩, ⟨96868677295, 103598201979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 281804800 284590080 ⟨⟨98461171177, 98461171183⟩, ⟨95138067170, 101823366862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 284590080 287375360 ⟨⟨99377878456, 99377878462⟩, ⟨96047587129, 102747288984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 287375360 290160640 ⟨⟨101136510677, 101136510684⟩, ⟨97784219871, 104528184681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 221511680 290160640 292945920 ⟨⟨102058411154, 102058411161⟩, ⟨98698919190, 105457312408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 287375360 290160640 ⟨⟨100293751436, 100293751444⟩, ⟨96956278296, 103670371066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221511680 222822400 290160640 292945920 ⟨⟨101208794516, 101208794523⟩, ⟨97864145032, 104592617536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 281804800 284590080 ⟨⟨97636380345, 97636380352⟩, ⟨94327909569, 100983706928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222822400 224133120 284590080 287375360 ⟨⟨98546208080, 98546208086⟩, ⟨95230575542, 101900724870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 281804800 284590080 ⟨⟨96815727945, 96815727953⟩, ⟨93521758252, 100148320265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 225443840 284590080 287375360 ⟨⟨97718692200, 97718692207⟩, ⟨94417586502, 101058449865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 287375360 290160640 ⟨⟨99455220393, 99455220400⟩, ⟨96132431334, 102816921915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222822400 224133120 290160640 292945920 ⟨⟨100363421554, 100363421561⟩, ⟨97033481185, 103732302363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 287375360 290160640 ⟨⟨98620859569, 98620859576⟩, ⟨95312622851, 101967777365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 290160640 292945920 ⟨⟨99522234204, 99522234211⟩, ⟨96206871420, 102876306948⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290160640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 287375360) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 284590080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224133120) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290160640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
