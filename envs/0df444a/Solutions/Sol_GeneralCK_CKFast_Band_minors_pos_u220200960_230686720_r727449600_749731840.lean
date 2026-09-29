-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r727449600_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:08:41.922396+00:00
-- url     : https://prove2.me/submissions/7eba8e96-7712-4d7c-878f-d4172b47a773

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [111/128, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 727449600 733020160 ⟨⟨238353073388, 238353073398⟩, ⟨229526247209, 247341165832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 733020160 738590720 ⟨⟨240016044833, 240016044842⟩, ⟨231162572682, 249030662560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 727449600 733020160 ⟨⟨234843766314, 234843766324⟩, ⟨226081749756, 243766766829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 733020160 738590720 ⟨⟨236486581685, 236486581694⟩, ⟨227697911668, 245436139661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 738590720 744161280 ⟨⟨241677808172, 241677808182⟩, ⟨232797699757, 250718936710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 744161280 749731840 ⟨⟨243338384135, 243338384144⟩, ⟨234431648794, 252406009353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 738590720 744161280 ⟨⟨238128234449, 238128234459⟩, ⟨229312919118, 247104337085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 744161280 749731840 ⟨⟨239768744466, 239768744475⟩, ⟨230926791618, 248771379285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 727449600 733020160 ⟨⟨231350116529, 231350116538⟩, ⟨222652442655, 240208477316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 733020160 738590720 ⟨⟨232972682407, 232972682416⟩, ⟨224248356994, 241857622808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 727449600 733020160 ⟨⟨227871794940, 227871794945⟩, ⟨219238003913, 236665961621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 733020160 738590720 ⟨⟨229474020580, 229474020584⟩, ⟨220813589122, 238294779227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 738590720 744161280 ⟨⟨234594130132, 234594130141⟩, ⟨225843159788, 243505638994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 744161280 749731840 ⟨⟨236214478721, 236214478730⟩, ⟨227436869724, 245152545199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 738590720 744161280 ⟨⟨231075171475, 231075171478⟩, ⟨222388104681, 239922512564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 744161280 749731840 ⟨⟨232675265826, 232675265831⟩, ⟨223961568482, 241549180122⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 727449600 749731840 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 733020160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 733020160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 744161280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 744161280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 738590720) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 733020160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 733020160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 744161280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 744161280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (111/128 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
