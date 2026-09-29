-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r128614400_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:48:24.210978+00:00
-- url     : https://prove2.me/submissions/f7285596-39b3-47db-9080-fd71fa335bbe

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [157/1024, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 128614400 129310720 ⟨⟨37911244990, 37911244997⟩, ⟨37241633548, 38582853908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250347520 250675200 129310720 130007040 ⟨⟨38111960036, 38111960041⟩, ⟨37441930840, 38783987486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250675200 251002880 128614400 129310720 ⟨⟨37820594494, 37820594499⟩, ⟨37151633441, 38491549763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 129310720 130007040 ⟨⟨38020847536, 38020847542⟩, ⟨37351469331, 38692220741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 250675200 130007040 130703360 ⟨⟨38312635186, 38312635191⟩, ⟨37642188259, 38985081146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 250675200 130703360 131399680 ⟨⟨38513270481, 38513270486⟩, ⟨37842405846, 39186134929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250675200 251002880 130007040 130703360 ⟨⟨38221060953, 38221060958⟩, ⟨37551265618, 38892852068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250675200 251002880 130703360 131399680 ⟨⟨38421234787, 38421234792⟩, ⟨37751022343, 39093443792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 251002880 251330560 128614400 129310720 ⟨⟨37730062548, 37730062553⟩, ⟨37061750352, 38400365719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 251002880 251330560 129310720 130007040 ⟨⟨37929854074, 37929854079⟩, ⟨37261125325, 38600574579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251330560 251658240 128614400 129310720 ⟨⟨37639648711, 37639648714⟩, ⟨36971983842, 38309301317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251330560 251658240 129310720 130007040 ⟨⟨37838979200, 37838979204⟩, ⟨37170898379, 38509048544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251330560 130007040 130703360 ⟨⟨38129606241, 38129606246⟩, ⟨37460460959, 38800744060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251330560 130703360 131399680 ⟨⟨38329319094, 38329319099⟩, ⟨37659757302, 39000874205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251330560 251658240 130007040 130703360 ⟨⟨38038270601, 38038270602⟩, ⟨37369773844, 38708756660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251330560 251658240 130703360 131399680 ⟨⟨38237522951, 38237522955⟩, ⟨37568610283, 38908425707⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 128614400 131399680 t = true :=
  ⟨_, (join_su (m := 251002880) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 250675200) (by decide) (join_sr (m := 129310720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 129310720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 250675200) (by decide) (join_sr (m := 130703360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130703360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 130007040) (by decide) (join_su (m := 251330560) (by decide) (join_sr (m := 129310720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 129310720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251330560) (by decide) (join_sr (m := 130703360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130703360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (157/1024 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
