-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:58.906888+00:00
-- url     : https://prove2.me/submissions/3bc6ccd8-9ab5-4336-aea3-9323d11adf80

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [351/640, 23/40]` by 15 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 460062720 465633280 ⟨⟨172552393643, 172552393652⟩, ⟨167868712905, 177296059182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205783040 207093760 460062720 465633280 ⟨⟨171252499978, 171252499981⟩, ⟨166592581090, 175972082949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205783040 465633280 471203840 ⟨⟨174446821512, 174446821520⟩, ⟨169748254885, 179205311104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 465633280 471203840 ⟨⟨173135202492, 173135202498⟩, ⟨168460407030, 177869604923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 208404480 460062720 465633280 ⟨⟨169958001333, 169958001341⟩, ⟨165321673975, 174653674206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 208404480 209715200 460062720 465633280 ⟨⟨168668831534, 168668831543⟩, ⟨164055927352, 173340764786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 465633280 471203840 ⟨⟨171828974207, 171828974216⟩, ⟨167177781093, 176539460345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 208404480 209715200 465633280 471203840 ⟨⟨170528070792, 170528070799⟩, ⟨165900313141, 175214809545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205783040 471203840 476774400 ⟨⟨176338222557, 176338222566⟩, ⟨171624802544, 181111502311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 207093760 471203840 476774400 ⟨⟨175014936948, 175014936954⟩, ⟨170325296416, 179764125954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 207093760 476774400 482344960 ⟨⟨177558510299, 177558510306⟩, ⟨169548970582, 185738133932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 208404480 471203840 476774400 ⟨⟨173697036970, 173697036979⟩, ⟨169031008617, 178422304483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209715200 471203840 476774400 ⟨⟨172384457073, 172384457081⟩, ⟨167741875498, 177085970430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 208404480 476774400 482344960 ⟨⟨175562225136, 175562225145⟩, ⟨170881391624, 180302242576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209715200 476774400 482344960 ⟨⟨174238025051, 174238025059⟩, ⟨169580648674, 178954282533⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205783040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 208404480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 207093760) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 476774400) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 208404480) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
