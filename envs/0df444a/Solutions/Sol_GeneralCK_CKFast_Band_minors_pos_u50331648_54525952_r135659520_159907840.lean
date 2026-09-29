-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_54525952_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:10:09.564569+00:00
-- url     : https://prove2.me/submissions/b52925e4-50ab-4292-b82c-6a37f04aac77

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 13/200]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 51380224 135659520 141721600 ⟨⟨174964803598, 174964803614⟩, ⟨164855156639, 185390645184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 51380224 52428800 135659520 141721600 ⟨⟨173045226387, 173045226400⟩, ⟨163069105006, 183330749478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 51380224 141721600 147783680 ⟨⟨180668890591, 180668890603⟩, ⟨170571786339, 191074195765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 51380224 52428800 141721600 147783680 ⟨⟨178717583745, 178717583761⟩, ⟨168752010047, 188984888428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 52428800 53477376 135659520 141721600 ⟨⟨171165429865, 171165429880⟩, ⟨161319332962, 181314358662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 53477376 54525952 135659520 141721600 ⟨⟨169324061200, 169324061216⟩, ⟨159604624637, 179339973173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 52428800 53477376 141721600 147783680 ⟨⟨176805971581, 176805971597⟩, ⟨166968536380, 186938875252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 53477376 54525952 141721600 147783680 ⟨⟨174932724922, 174932724934⟩, ⟨165220166785, 184934687591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 51380224 147783680 153845760 ⟨⟨186269937769, 186269937785⟩, ⟨176186887616, 196653444331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 51380224 52428800 147783680 153845760 ⟨⟨184288899998, 184288900011⟩, ⟨174335391500, 194536702134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 51380224 153845760 159907840 ⟨⟨191772342584, 191772342597⟩, ⟨181704702107, 202132934949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 51380224 52428800 153845760 159907840 ⟨⟨189763433704, 189763433717⟩, ⟨179823356383, 199990592379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 52428800 53477376 147783680 153845760 ⟨⟨182347431502, 182347431518⟩, ⟨172520178586, 192463008127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 53477376 54525952 147783680 153845760 ⟨⟨180444227206, 180444227222⟩, ⟨170740068364, 190430924636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 52428800 53477376 153845760 159907840 ⟨⟨187793934138, 187793934151⟩, ⟨177978236752, 197891021577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 53477376 54525952 153845760 159907840 ⟨⟨185862563166, 185862563178⟩, ⟨176168181317, 195832815734⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 54525952 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 52428800) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 51380224) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 51380224) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 53477376) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 53477376) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 52428800) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 51380224) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 51380224) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 53477376) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 53477376) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
