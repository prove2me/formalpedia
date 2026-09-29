-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:56:29.484313+00:00
-- url     : https://prove2.me/submissions/5823c0c5-e0bd-4313-accc-e8fcd92f618c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 159252480 160645120 ⟨⟨53676533609, 53676533611⟩, ⟨52215866003, 55146169791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 160645120 162037760 ⟨⟨54129647803, 54129647807⟩, ⟨52667176229, 55601093237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 159252480 160645120 ⟨⟨53436291673, 53436291679⟩, ⟨51978733065, 54902787826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 160645120 162037760 ⟨⟨53887496018, 53887496023⟩, ⟨52428138206, 55355796691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 162037760 163430400 ⟨⟨54582539096, 54582539100⟩, ⟨53118264171, 56055793152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231342080 163430400 164823040 ⟨⟨55035208035, 55035208039⟩, ⟨53569130376, 56510270085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231997440 162037760 163430400 ⟨⟨54338480229, 54338480235⟩, ⟨52877323813, 55808584812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231342080 231997440 163430400 164823040 ⟨⟨54789244847, 54789244852⟩, ⟨53326290424, 56261152729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 159252480 160645120 ⟨⟨53196739831, 53196739837⟩, ⟨51742274826, 54660111553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 160645120 162037760 ⟨⟨53646038353, 53646038360⟩, ⟨52189778902, 55111209871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 159252480 160645120 ⟨⟨52957872897, 52957872902⟩, ⟨51506486216, 54418135670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 160645120 162037760 ⟨⟨53405269603, 53405269608⟩, ⟨51952093226, 54867327455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 162037760 163430400 ⟨⟨54095119484, 54095119490⟩, ⟨52637066169, 55562090205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231997440 232652800 163430400 164823040 ⟨⟨54543983754, 54543983759⟩, ⟨53084137152, 56012753086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 233308160 162037760 163430400 ⟨⟨53852451629, 53852451634⟩, ⟨52397486119, 55316303985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 163430400 164823040 ⟨⟨54299419496, 54299419503⟩, ⟨52842665417, 55765065784⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 160645120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 232652800) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
