-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:56:18.110924+00:00
-- url     : https://prove2.me/submissions/8cb536d6-e4f4-4efa-8a62-8aa1b7b2fdd2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 136970240 138362880 ⟨⟨40804205759, 40804205766⟩, ⟨40014476822, 41596799521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 136970240 138362880 ⟨⟨40707296854, 40707296859⟩, ⟨39918521724, 41498931211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 138362880 139755520 ⟨⟨41208282920, 41208282925⟩, ⟨40417647933, 42001784253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 138362880 139755520 ⟨⟨41110453224, 41110453229⟩, ⟨40320773480, 41902993723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 136970240 138362880 ⟨⟨40610514334, 40610514337⟩, ⟨39822690958, 41401191360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 136970240 138362880 ⟨⟨40513857724, 40513857731⟩, ⟨39726984051, 41303579490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250019840 138362880 139755520 ⟨⟨41012750859, 41012750860⟩, ⟨40224024300, 41804332596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250019840 250347520 138362880 139755520 ⟨⟨40915175341, 40915175346⟩, ⟨40127399917, 41705800393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249364480 139755520 141148160 ⟨⟨41612198560, 41612198565⟩, ⟨40820657734, 42406607252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249364480 249692160 139755520 141148160 ⟨⟨41513449159, 41513449164⟩, ⟨40722865007, 42306895590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249364480 141148160 142540800 ⟨⟨42015953040, 42015953045⟩, ⟨41223506585, 42811268876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249364480 249692160 141148160 142540800 ⟨⟨41916285014, 41916285019⟩, ⟨41124796660, 42710637168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 139755520 141148160 ⟨⟨41414828024, 41414828027⟩, ⟨40625198486, 42207314270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250019840 250347520 139755520 141148160 ⟨⟨41316334673, 41316334678⟩, ⟨40527657697, 42107862809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249692160 250019840 141148160 142540800 ⟨⟨41816746187, 41816746189⟩, ⟨41026213872, 42610136734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 141148160 142540800 ⟨⟨41717336071, 41717336077⟩, ⟨40927757741, 42509767091⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250019840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249692160) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249364480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250019840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
