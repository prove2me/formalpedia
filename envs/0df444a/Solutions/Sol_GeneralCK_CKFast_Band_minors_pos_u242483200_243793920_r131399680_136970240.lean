-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u242483200_243793920_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:25:20.454976+00:00
-- url     : https://prove2.me/submissions/21c1df65-8f79-4491-b848-6475cff252e0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/128, 93/320]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 242483200 242810880 131399680 132792320 ⟨⟨41077035480, 41077035486⟩, ⟨40271530106, 41885515692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242810880 243138560 131399680 132792320 ⟨⟨40981269700, 40981269706⟩, ⟨40176754961, 41788753288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 242810880 132792320 134184960 ⟨⟨41500473487, 41500473492⟩, ⟨40694031768, 42309891481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242810880 243138560 132792320 134184960 ⟨⟨41403762531, 41403762536⟩, ⟨40598312939, 42212182417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243138560 243466240 131399680 132792320 ⟨⟨40885636110, 40885636112⟩, ⟨40082109801, 41692125297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243466240 243793920 131399680 132792320 ⟨⟨40790134203, 40790134210⟩, ⟨39987594129, 41595631211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243138560 243466240 132792320 134184960 ⟨⟨41307184797, 41307184801⟩, ⟨40502725125, 42114608796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243466240 243793920 132792320 134184960 ⟨⟨41210739778, 41210739783⟩, ⟨40407267827, 42017170116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 242810880 134184960 135577600 ⟨⟨41923725297, 41923725302⟩, ⟨41116347539, 42734080766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242810880 243138560 134184960 135577600 ⟨⟨41826070388, 41826070393⟩, ⟨41019686242, 42635426267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 242483200 242810880 135577600 136970240 ⟨⟨42346791338, 42346791344⟩, ⟨41538477844, 43158083978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242810880 243138560 135577600 136970240 ⟨⟨42248193694, 42248193700⟩, ⟨41440875294, 43058485267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243138560 243466240 134184960 135577600 ⟨⟨41728549725, 41728549729⟩, ⟨40923156985, 42536908241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243466240 243793920 134184960 135577600 ⟨⟨41631162801, 41631162806⟩, ⟨40826759262, 42438526177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243466240 135577600 136970240 ⟨⟨42149731316, 42149731320⟩, ⟨41343405800, 42959024051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243466240 243793920 135577600 136970240 ⟨⟨42051403692, 42051403698⟩, ⟨41246068856, 42859699816⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 242483200 243793920 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242810880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243466240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243138560) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242810880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243466240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/128 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
