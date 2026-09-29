-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:27:19.203023+00:00
-- url     : https://prove2.me/submissions/e8382502-bccc-4278-8435-ea9005cd980b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [537/2560, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 175964160 177356800 ⟨⟨59099312236, 59099312240⟩, ⟨57617037395, 60590618238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 177356800 178749440 ⟨⟨59549787462, 59549787466⟩, ⟨58065715956, 61042895265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 175964160 177356800 ⟨⟨58836332967, 58836332973⟩, ⟨57357223108, 60324443374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 177356800 178749440 ⟨⟨59284931008, 59284931015⟩, ⟨57804029032, 60774838703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 178749440 180142080 ⟨⟨60000046273, 60000046277⟩, ⟨58514178699, 61494955267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231342080 180142080 181534720 ⟨⟨60450089204, 60450089205⟩, ⟨58962426157, 61946798776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231997440 178749440 180142080 ⟨⟨59733315303, 59733315308⟩, ⟨58250621788, 61225019693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231342080 231997440 180142080 181534720 ⟨⟨60181486374, 60181486379⟩, ⟨58697001902, 61674986867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 175964160 177356800 ⟨⟨58574090288, 58574090294⟩, ⟨57098129941, 60059020766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 177356800 178749440 ⟨⟨59020814841, 59020814846⟩, ⟨57543066920, 60507538098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 175964160 177356800 ⟨⟨58312578737, 58312578743⟩, ⟨56839752548, 59794344836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 177356800 178749440 ⟨⟨58757433474, 58757433480⟩, ⟨57282824251, 60240987849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 178749440 180142080 ⟨⟨59467328286, 59467328291⟩, ⟨57987793355, 60955843747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231997440 232652800 180142080 181534720 ⟨⟨59913631140, 59913631145⟩, ⟨58432309762, 61403938232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 233308160 178749440 180142080 ⟨⟨59202079718, 59202079723⟩, ⟨57725688007, 60687421810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 180142080 181534720 ⟨⟨59646517977, 59646517982⟩, ⟨58168344322, 61133647228⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 180142080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 178749440) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 177356800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 232652800) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 180142080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
