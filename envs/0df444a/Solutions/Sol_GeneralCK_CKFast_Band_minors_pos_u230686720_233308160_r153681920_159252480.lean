-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:52:01.667987+00:00
-- url     : https://prove2.me/submissions/9bf1d59f-6eed-4c12-ba1f-b7ce319dd26e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 153681920 155074560 ⟨⟨51861836828, 51861836832⟩, ⟨50408391294, 53324229683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 155074560 156467200 ⟨⟨52315848125, 52315848129⟩, ⟨50860596140, 53780052764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 153681920 155074560 ⟨⟨51629262159, 51629262166⟩, ⟨50178906379, 53088534094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 155074560 156467200 ⟨⟨52081352443, 52081352450⟩, ⟨50629195050, 53542431356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 156467200 157859840 ⟨⟨52769634320, 52769634324⟩, ⟨51312576506, 54235650107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231342080 157859840 159252480 ⟨⟨53223195963, 53223195967⟩, ⟨51764332944, 54691022264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231997440 156467200 157859840 ⟨⟨52533220428, 52533220434⟩, ⟨51079262027, 53996105703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231342080 231997440 157859840 159252480 ⟨⟨52984866657, 52984866663⟩, ⟨51529107851, 54449557678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 153681920 155074560 ⟨⟨51397361179, 51397361185⟩, ⟨49950079790, 52853527763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 155074560 156467200 ⟨⟨51847534594, 51847534599⟩, ⟨50398456423, 53305503357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 153681920 155074560 ⟨⟨51166128803, 51166128808⟩, ⟨49721906560, 52619205487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 155074560 156467200 ⟨⟨51614389467, 51614389473⟩, ⟨50168375264, 53069263542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 156467200 157859840 ⟨⟨52297488484, 52297488490⟩, ⟨50846614118, 53757258830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231997440 232652800 157859840 159252480 ⟨⟨52747223386, 52747223391⟩, ⟨51294553407, 54208794717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 233308160 156467200 157859840 ⟨⟨52062433354, 52062433359⟩, ⟨50614627759, 53519104240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 157859840 159252480 ⟨⟨52510260989, 52510260994⟩, ⟨51060664568, 53968728108⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 232652800) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 157859840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
