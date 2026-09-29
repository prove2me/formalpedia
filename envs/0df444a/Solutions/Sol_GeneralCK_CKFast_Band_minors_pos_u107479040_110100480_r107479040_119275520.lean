-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u107479040_110100480_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:09:59.136988+00:00
-- url     : https://prove2.me/submissions/a81ae25d-bf13-446b-bb49-32508ed311d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/320, 21/160]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 107479040 108134400 107479040 110428160 ⟨⟨86138168242, 86138168250⟩, ⟨82934916076, 89382541228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 108134400 108789760 107479040 110428160 ⟨⟨85705064777, 85705064784⟩, ⟨82517304915, 88933594165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 108134400 110428160 113377280 ⟨⟨88242259417, 88242259425⟩, ⟨85031647593, 91493821380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 108134400 108789760 110428160 113377280 ⟨⟨87800423537, 87800423545⟩, ⟨84605309640, 91036139881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 108789760 109445120 107479040 110428160 ⟨⟨85275322898, 85275322906⟩, ⟨82102901406, 88488167357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 109445120 110100480 107479040 110428160 ⟨⟨84848897429, 84848897431⟩, ⟨81691662718, 88046213190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 108789760 109445120 110428160 113377280 ⟨⟨87361994594, 87361994604⟩, ⟨84182225246, 90582023359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 109445120 110100480 110428160 113377280 ⟨⟨86926927054, 86926927059⟩, ⟨83762351196, 90131423862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108134400 113377280 116326400 ⟨⟨90336304883, 90336304892⟩, ⟨87118445754, 93594943690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 108134400 108789760 113377280 116326400 ⟨⟨89885856906, 89885856916⟩, ⟨86683499727, 93128649653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 107479040 108134400 116326400 119275520 ⟨⟨92420429201, 92420429209⟩, ⟨89195432898, 95686034955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108134400 108789760 116326400 119275520 ⟨⟨91961487223, 91961487230⟩, ⟨88751995336, 95211248008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 108789760 109445120 113377280 116326400 ⟨⟨89438859626, 89438859634⟩, ⟨86251851589, 92665963701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 109445120 110100480 113377280 116326400 ⟨⟨88995267168, 88995267172⟩, ⟨85823457772, 92206837565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 109445120 116326400 119275520 ⟨⟨91506038145, 91506038153⟩, ⟨88311898464, 94740110678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 109445120 110100480 116326400 119275520 ⟨⟨91054035784, 91054035788⟩, ⟨87875098384, 94272574410⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 107479040 110100480 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 108134400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 108134400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 109445120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 109445120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 108789760) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 108134400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 108134400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 109445120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 109445120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/320 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
