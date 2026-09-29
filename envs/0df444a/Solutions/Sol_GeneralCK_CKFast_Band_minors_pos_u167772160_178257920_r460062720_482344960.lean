-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:57.230024+00:00
-- url     : https://prove2.me/submissions/76a72f43-085a-42d2-a452-a072779faa52

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 460062720 465633280 ⟨⟨210698717627, 210698717636⟩, ⟨201692694442, 219897565934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 465633280 471203840 ⟨⟨212912398841, 212912398851⟩, ⟨203878957706, 222138162889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 460062720 465633280 ⟨⟨207749865780, 207749865790⟩, ⟨198829385835, 216861409720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 465633280 471203840 ⟨⟨209940644580, 209940644590⟩, ⟨200992616043, 219079276182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 471203840 476774400 ⟨⟨215121092131, 215121092141⟩, ⟨206060333271, 224373666405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 170393600 476774400 482344960 ⟨⟨217324867091, 217324867101⟩, ⟨208236889094, 226604147730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 471203840 476774400 ⟨⟨212126601901, 212126601910⟩, ⟨203151120913, 221292219687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 170393600 173015040 476774400 482344960 ⟨⟨214307804364, 214307804374⟩, ⟨205304965524, 223500308418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 460062720 465633280 ⟨⟨204831211268, 204831211278⟩, ⟨195994848628, 213856900380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173015040 175636480 465633280 471203840 ⟨⟨206999020242, 206999020249⟩, ⟨198134994910, 216051950869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 460062720 465633280 ⟨⟨201941975026, 201941975028⟩, ⟨193188341134, 210883221253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 175636480 178257920 465633280 471203840 ⟨⟨204086752016, 204086752022⟩, ⟨195305357170, 213055376320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 471203840 476774400 ⟨⟨209162170268, 209162170278⟩, ⟨200270574333, 218242244968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 173015040 175636480 476774400 482344960 ⟨⟨211320725115, 211320725122⟩, ⟨202401649195, 220427847910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 178257920 471203840 476774400 ⟨⟨206227028729, 206227028733⟩, ⟨197417960982, 215222937679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 476774400 482344960 ⟨⟨208362866169, 208362866174⟩, ⟨199526212199, 217385967725⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 460062720 482344960 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 471203840) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 465633280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 476774400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 471203840) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 465633280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 175636480) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 476774400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
