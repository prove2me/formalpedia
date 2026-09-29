-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r549191680_571473920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:32:19.419492+00:00
-- url     : https://prove2.me/submissions/1dfc373c-d51e-435c-8eba-d195d39422a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [419/640, 109/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 549191680 554762240 ⟨⟨173831465427, 173831465436⟩, ⟨169363248960, 178353769579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 549191680 554762240 ⟨⟨172444581239, 172444581243⟩, ⟨167997518645, 176945502531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 554762240 560332800 ⟨⟨175461545082, 175461545090⟩, ⟨170979090273, 179998086070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 554762240 560332800 ⟨⟨174063531869, 174063531873⟩, ⟨169602253604, 178578670708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 549191680 554762240 ⟨⟨171061851241, 171061851250⟩, ⟨166635823273, 175541509724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 549191680 554762240 ⟨⟨169683227531, 169683227537⟩, ⟨165278116060, 174141742123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 554762240 560332800 ⟨⟨172669663693, 172669663701⟩, ⟨168229443850, 177163519244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234618880 235929600 554762240 560332800 ⟨⟨171279892895, 171279892903⟩, ⟨166860614448, 175752582915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231997440 560332800 565903360 ⟨⟨177089972608, 177089972616⟩, ⟨172593290791, 181640737969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 233308160 560332800 565903360 ⟨⟨175680865424, 175680865428⟩, ⟨171205382195, 180210209988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231997440 565903360 571473920 ⟨⟨178716768618, 178716768626⟩, ⟨174205870918, 183281746087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231997440 233308160 565903360 571473920 ⟨⟨177296602014, 177296602018⟩, ⟨172806924328, 181840140677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 560332800 565903360 ⟨⟨174275893614, 174275893622⟩, ⟨169821491985, 178783935050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 560332800 565903360 ⟨⟨172875009773, 172875009781⟩, ⟨168441573826, 177361864661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 565903360 571473920 ⟨⟨175880560627, 175880560636⟩, ⟨171411987105, 180402776946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 565903360 571473920 ⟨⟨174468597302, 174468597310⟩, ⟨170021013147, 178969606679⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 549191680 571473920 t = true :=
  ⟨_, (join_sr (m := 560332800) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 554762240) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 554762240) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234618880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233308160) (by decide) (join_sr (m := 565903360) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231997440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 565903360) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234618880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (419/640 : ℝ) (109/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  have e3 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
