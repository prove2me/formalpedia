-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r256901120_281149440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:54:19.316536+00:00
-- url     : https://prove2.me/submissions/929c5af6-fe61-4ee2-8108-7ac490b63d34

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [49/160, 429/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 256901120 262963200 ⟨⟨239559065081, 239559065092⟩, ⟨227201572172, 252277340349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 69206016 262963200 269025280 ⟨⟨243631453392, 243631453406⟩, ⟨231273169767, 256344656599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 71303168 256901120 262963200 ⟨⟨235933243368, 235933243379⟩, ⟨223780012454, 248439137839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 262963200 269025280 ⟨⟨239979184564, 239979184576⟩, ⟨227822937532, 252482549924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 69206016 269025280 281149440 ⟨⟨249666620818, 249666620832⟩, ⟨233251803747, 266685150469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 69206016 71303168 269025280 281149440 ⟨⟨245976553520, 245976553533⟩, ⟨229837864441, 262705431649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 73400320 256901120 262963200 ⟨⟨232396621582, 232396621595⟩, ⟨220440933794, 244697133886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 71303168 73400320 262963200 269025280 ⟨⟨236415558826, 236415558841⟩, ⟨224454785147, 248715910820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 75497472 256901120 262963200 ⟨⟨228945341380, 228945341391⟩, ⟨217180811155, 241047124993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 73400320 75497472 262963200 269025280 ⟨⟨232936778482, 232936778496⟩, ⟨221165237155, 245040608757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 71303168 73400320 269025280 275087360 ⟨⟨240397150148, 240397150161⟩, ⟨228431863732, 252696851549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 71303168 73400320 275087360 281149440 ⟨⟨244342422177, 244342422189⟩, ⟨232373162993, 256641014096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 73400320 75497472 269025280 275087360 ⟨⟨236891841837, 236891841851⟩, ⟨225113870700, 248997212233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 73400320 75497472 275087360 281149440 ⟨⟨240811515395, 240811515409⟩, ⟨229027663589, 252917949984⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 256901120 281149440 t = true :=
  ⟨_, (join_su (m := 71303168) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 262963200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262963200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 69206016) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 269025280) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 262963200) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 262963200) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 73400320) (by decide) (join_sr (m := 275087360) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 275087360) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (429/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((281149440 : ℤ) : ℝ) / (D : ℝ)) = (429/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
