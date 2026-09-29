-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r549191680_571473920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:52:02.483543+00:00
-- url     : https://prove2.me/submissions/e7efc99e-547a-4d9e-8e20-31b406fcfcc9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [419/640, 109/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 549191680 554762240 ⟨⟨179421521074, 179421521078⟩, ⟨174867473484, 184030580176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 549191680 554762240 ⟨⟨178017530267, 178017530276⟩, ⟨173485125148, 182604714765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 554762240 560332800 ⟨⟨181096020184, 181096020188⟩, ⟨176527655231, 185719380957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 554762240 560332800 ⟨⟨179680939536, 179680939544⟩, ⟨175134235014, 184282411393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 549191680 554762240 ⟨⟨176617890689, 176617890697⟩, ⟨172107004123, 181183325282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229376000 230686720 549191680 554762240 ⟨⟨175222552250, 175222552259⟩, ⟨170733061511, 179766360451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228065280 229376000 554762240 560332800 ⟨⟨178270199923, 178270199932⟩, ⟨173745033127, 182849906282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 554762240 560332800 ⟨⟨176863751527, 176863751534⟩, ⟨172360000918, 181421814644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226754560 560332800 565903360 ⟨⟨182768721808, 182768721812⟩, ⟨178186053420, 187406369126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 228065280 560332800 565903360 ⟨⟨181342588437, 181342588444⟩, ⟨176781597780, 185958333205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226754560 565903360 571473920 ⟨⟨184439648654, 184439648658⟩, ⟨179842690518, 189091567627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226754560 228065280 565903360 571473920 ⟨⟨183002499139, 183002499148⟩, ⟨178427235382, 187632502596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 560332800 565903360 ⟨⟨179920785387, 179920785395⟩, ⟨175381350974, 184514749733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 560332800 565903360 ⟨⟨178503263110, 178503263118⟩, ⟨173985264601, 183075568027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 229376000 565903360 571473920 ⟨⟨181569668720, 181569668728⟩, ⟨177015979081, 186177877492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 565903360 571473920 ⟨⟨180141108121, 180141108130⟩, ⟨175608873466, 184727641931⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 549191680 571473920 t = true :=
  ⟨_, (join_sr (m := 560332800) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 554762240) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 554762240) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229376000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228065280) (by decide) (join_sr (m := 565903360) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226754560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 565903360) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229376000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (419/640 : ℝ) (109/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  have e3 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
