-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_239861760_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:44:03.012035+00:00
-- url     : https://prove2.me/submissions/149ea022-1445-40fd-a1ca-e3ba0aaed42a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 183/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 238878720 136970240 138362880 ⟨⟨43974961849, 43974961855⟩, ⟨43153578372, 44799399055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238878720 239206400 136970240 138362880 ⟨⟨43873746450, 43873746455⟩, ⟨43053386760, 44697153660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 238878720 138362880 139755520 ⟨⟨44409021044, 44409021050⟩, ⟨43586684631, 45234412545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 238878720 239206400 138362880 139755520 ⟨⟨44306853001, 44306853006⟩, ⟨43485541869, 45131213018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239206400 239534080 136970240 138362880 ⟨⟨43772673668, 43772673673⟩, ⟨42953335450, 44595053220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239534080 239861760 136970240 138362880 ⟨⟨43671742963, 43671742969⟩, ⟨42853423910, 44493097185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239534080 138362880 139755520 ⟨⟨44204828620, 44204828626⟩, ⟨43384540453, 45028159494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239534080 239861760 138362880 139755520 ⟨⟨44102947362, 44102947367⟩, ⟨43283679848, 44925251420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 238878720 139755520 141148160 ⟨⟨44842880739, 44842880745⟩, ⟨44019591753, 45669226172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238878720 239206400 139755520 141148160 ⟨⟨44739761339, 44739761345⟩, ⟨43917499122, 45565073806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 238878720 141148160 142540800 ⟨⟨45276541404, 45276541409⟩, ⟨44452300202, 46103840403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238878720 239206400 141148160 142540800 ⟨⟨45172471932, 45172471937⟩, ⟨44349258984, 45998736488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239206400 239534080 139755520 141148160 ⟨⟨44636786643, 44636786649⟩, ⟨43815548876, 45461068485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239534080 239861760 139755520 141148160 ⟨⟨44533956104, 44533956109⟩, ⟨43713740477, 45357209651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239206400 239534080 141148160 142540800 ⟨⟨45068548196, 45068548203⟩, ⟨44246361181, 45893780651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239534080 239861760 141148160 142540800 ⟨⟨44964769648, 44964769653⟩, ⟨44143606251, 45788972335⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 239861760 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 238878720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239534080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239206400) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 238878720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239534080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (183/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
