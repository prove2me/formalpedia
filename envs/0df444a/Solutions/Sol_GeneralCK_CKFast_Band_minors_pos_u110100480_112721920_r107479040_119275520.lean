-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_112721920_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:11:12.285464+00:00
-- url     : https://prove2.me/submissions/efd4dfb8-c5ab-4612-9b2e-f076c48f8ff5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 43/320]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 110755840 107479040 110428160 ⟨⟨84425743999, 84425744007⟩, ⟨81283546788, 87607684919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110755840 111411200 107479040 110428160 ⟨⟨84005819055, 84005819063⟩, ⟨80878512308, 87172536646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 110755840 110428160 113377280 ⟨⟨86495176189, 86495176197⟩, ⟨83345645052, 89684294308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110755840 111411200 110428160 113377280 ⟨⟨86066698088, 86066698096⟩, ⟨82932065134, 89240588459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 111411200 112066560 107479040 110428160 ⟨⟨83589079812, 83589079820⟩, ⟨80476518705, 86740723297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112066560 112721920 107479040 110428160 ⟨⟨83175484254, 83175484262⟩, ⟨80077526126, 86312200614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 111411200 112066560 110428160 113377280 ⟨⟨85641449610, 85641449620⟩, ⟨82521570495, 88800260911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112066560 112721920 110428160 113377280 ⟨⟨85219388389, 85219388399⟩, ⟨82114120913, 88363267068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 110755840 113377280 116326400 ⟨⟨88555034474, 88555034482⟩, ⟨85398275486, 91751223852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110755840 111411200 113377280 116326400 ⟨⟨88118117298, 88118117308⟩, ⟨84976262699, 91299076010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 110755840 116326400 119275520 ⟨⟨90605434771, 90605434779⟩, ⟨87441551974, 93808591516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 110755840 111411200 116326400 119275520 ⟨⟨90160190552, 90160190560⟩, ⟨87011216877, 93348115164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 111411200 112066560 113377280 116326400 ⟨⟨87684472174, 87684472184⟩, ⟨84557378117, 90850348324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112066560 112721920 113377280 116326400 ⟨⟨87254056402, 87254056412⟩, ⟨84141581172, 90404995892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 111411200 112066560 116326400 119275520 ⟨⟨89718259351, 89718259359⟩, ⟨86584051472, 92891099344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112066560 112721920 116326400 119275520 ⟨⟨89279598164, 89279598172⟩, ⟨86160014869, 92437498869⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 112721920 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 111411200) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 110755840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112066560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 111411200) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 110755840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112066560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (43/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
