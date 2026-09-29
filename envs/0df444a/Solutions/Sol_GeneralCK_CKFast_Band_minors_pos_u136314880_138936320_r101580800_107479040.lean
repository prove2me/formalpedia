-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:08:48.532184+00:00
-- url     : https://prove2.me/submissions/f7d0b657-0fec-4488-8ff8-3b9b1af1a462

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 101580800 103055360 ⟨⟨65778701728, 65778701735⟩, ⟨63696599388, 67879087714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 136970240 103055360 104529920 ⟨⟨66665462900, 66665462906⟩, ⟨64580333517, 68768861868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136970240 137625600 101580800 103055360 ⟨⟨65475629526, 65475629533⟩, ⟨63401054449, 67568368707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 103055360 104529920 ⟨⟨66358779132, 66358779139⟩, ⟨64281185402, 68454523301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 136970240 104529920 106004480 ⟨⟨67550687658, 67550687665⟩, ⟨65462542845, 69657087935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 136970240 106004480 107479040 ⟨⟨68434383530, 68434383537⟩, ⟨66343234818, 70543773524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 136970240 137625600 104529920 106004480 ⟨⟨67240410217, 67240410224⟩, ⟨65159809272, 69339147876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 136970240 137625600 106004480 107479040 ⟨⟨68120530184, 68120530190⟩, ⟨66036933384, 70222249910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 137625600 138280960 101580800 103055360 ⟨⟨65174437448, 65174437455⟩, ⟨63107327302, 67259593484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138280960 103055360 104529920 ⟨⟨66053992433, 66053992441⟩, ⟨63983872041, 68142145441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138280960 138936320 101580800 103055360 ⟨⟨64875104293, 64875104299⟩, ⟨62815397535, 66952740042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138280960 138936320 103055360 104529920 ⟨⟨65751081461, 65751081468⟩, ⟨63688372876, 67831706145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 137625600 138280960 104529920 106004480 ⟨⟨66932046573, 66932046579⟩, ⟨64858927200, 69023185224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 137625600 138280960 106004480 107479040 ⟨⟨67808607142, 67808607150⟩, ⟨65732499980, 69902720185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138280960 138936320 104529920 106004480 ⟨⟨66625575242, 66625575249⟩, ⟨64559875928, 68709177699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 138280960 138936320 106004480 107479040 ⟨⟨67498592789, 67498592797⟩, ⟨65429913770, 69585161933⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 137625600) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 136970240) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 136970240) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 138280960) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 138280960) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
