-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:33:32.465341+00:00
-- url     : https://prove2.me/submissions/c85f1d72-cbf5-433b-93f6-dd89245a0a63

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [127/640, 17/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 166461440 169410560 ⟨⟨103625061492, 103625061501⟩, ⟨99237168012, 108083175127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 137625600 169410560 172359680 ⟨⟨105271052121, 105271052128⟩, ⟨100872834155, 109739361535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 137625600 138936320 166461440 169410560 ⟨⟨102733820198, 102733820207⟩, ⟨98376505697, 107160547367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 169410560 172359680 ⟨⟨104368174060, 104368174068⟩, ⟨100000554078, 108805084162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 137625600 172359680 175308800 ⟨⟨106912121706, 106912121714⟩, ⟨102503647395, 111390558142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 137625600 175308800 178257920 ⟨⟨108548315476, 108548315485⟩, ⟨104129652099, 113036811050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138936320 172359680 175308800 ⟨⟨105997710358, 105997710367⟩, ⟨101619851298, 110444736364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 137625600 138936320 175308800 178257920 ⟨⟨107622472956, 107622472964⟩, ⟨103234440391, 112079548675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 140247040 166461440 169410560 ⟨⟨101852231076, 101852231084⟩, ⟨97525030110, 106248053068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 140247040 169410560 172359680 ⟨⟨103475020040, 103475020049⟩, ⟨99137534006, 107881010503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140247040 141557760 166461440 169410560 ⟨⟨100980098908, 100980098910⟩, ⟨96682556656, 105345485967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 141557760 169410560 172359680 ⟨⟨102591394199, 102591394204⟩, ⟨98283588627, 106966933729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 172359680 175308800 ⟨⟨105093092774, 105093092781⟩, ⟨100745386373, 109509186367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138936320 140247040 175308800 178257920 ⟨⟨106706491816, 106706491823⟩, ⟨102348628955, 111132624012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 141557760 172359680 175308800 ⟨⟨104198072493, 104198072499⟩, ⟨99880066638, 108583700813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 175308800 178257920 ⟨⟨105800175049, 105800175054⟩, ⟨101472031182, 110195829255⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 138936320) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 137625600) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 175308800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172359680) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 169410560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140247040) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 175308800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
