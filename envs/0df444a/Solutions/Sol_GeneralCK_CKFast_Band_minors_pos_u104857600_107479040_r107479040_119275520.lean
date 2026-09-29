-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_107479040_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:09:48.380679+00:00
-- url     : https://prove2.me/submissions/68708de7-f822-44c9-9ad5-463eb8539601

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 41/320]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 105512960 107479040 110428160 ⟨⟨87905131244, 87905131252⟩, ⟨84638321858, 91214515784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 105512960 106168320 107479040 110428160 ⟨⟨87458112609, 87458112617⟩, ⟨84207435724, 90750993505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 105512960 110428160 113377280 ⟨⟨90044612902, 90044612912⟩, ⟨86770427278, 93361187766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 105512960 106168320 110428160 113377280 ⟨⟨89588676791, 89588676800⟩, ⟨86330626883, 92888748733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 106168320 106823680 107479040 110428160 ⟨⟨87014644849, 87014644851⟩, ⟨83779936641, 90291191022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 106823680 107479040 107479040 110428160 ⟨⟨86574679307, 86574679315⟩, ⟨83355778509, 89835057044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 106823680 110428160 113377280 ⟨⟨89136338370, 89136338374⟩, ⟨85894260988, 92420075590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106823680 107479040 110428160 113377280 ⟨⟨88687548614, 88687548624⟩, ⟨85461283105, 91955116700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 105512960 113377280 116326400 ⟨⟨92173551084, 92173551092⟩, ⟨88892108217, 95497197593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 105512960 106168320 113377280 116326400 ⟨⟨91708824465, 91708824473⟩, ⟨88443518832, 95015970442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 105512960 116326400 119275520 ⟨⟨94292079719, 94292079729⟩, ⟨91003496170, 97622681646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 105512960 106168320 116326400 119275520 ⟨⟨93818687145, 93818687155⟩, ⟨90546240709, 97132792545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 106168320 106823680 113377280 116326400 ⟨⟨91247740649, 91247740653⟩, ⟨87998409722, 94538553550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 106823680 107479040 113377280 116326400 ⟨⟨90790250270, 90790250280⟩, ⟨87556734029, 94064894967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 106168320 106823680 116326400 119275520 ⟨⟨93348980834, 93348980838⟩, ⟨90092509663, 96646756399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 106823680 107479040 116326400 119275520 ⟨⟨92882911108, 92882911116⟩, ⟨89642255837, 96164520967⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 107479040 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 105512960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 105512960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 106823680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 106823680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 106168320) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 105512960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 105512960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 106823680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 106823680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (41/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
