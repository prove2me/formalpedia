-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.244173+00:00
-- url     : https://prove2.me/submissions/0576c4aa-5c03-4395-885c-dc3a36e760b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 304087040 309657600 ⟨⟨138183776234, 138183776240⟩, ⟨133423358947, 143015473758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 179568640 180879360 304087040 309657600 ⟨⟨137121213632, 137121213636⟩, ⟨132388653330, 141924487753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 179568640 309657600 315228160 ⟨⟨140460818114, 140460818122⟩, ⟨135683765676, 145309014598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 309657600 315228160 ⟨⟨139383930864, 139383930868⟩, ⟨134634751723, 144203694818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 182190080 304087040 309657600 ⟨⟨136065442502, 136065442510⟩, ⟨131360460759, 140840578564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182190080 183500800 304087040 309657600 ⟨⟨135016363379, 135016363385⟩, ⟨130338686104, 139763642261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 309657600 315228160 ⟨⟨138313861727, 138313861734⟩, ⟨133592279363, 143105476406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182190080 183500800 309657600 315228160 ⟨⟨137250511378, 137250511385⟩, ⟨132556253554, 142014255634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 179568640 315228160 320798720 ⟨⟨142731524075, 142731524082⟩, ⟨137937921635, 147596132692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 179568640 180879360 315228160 320798720 ⟨⟨141640435328, 141640435332⟩, ⟨136874720347, 146476604441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 179568640 320798720 326369280 ⟨⟨144995975642, 144995975650⟩, ⟨140185907004, 149876910932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 179568640 180879360 320798720 326369280 ⟨⟨143890806465, 143890806467⟩, ⟨139108637341, 148743297377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 315228160 320798720 ⟨⟨140556189375, 140556189384⟩, ⟨135818087272, 145364200119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 315228160 320798720 ⟨⟨139478687062, 139478687070⟩, ⟨134767927479, 144258816234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 180879360 182190080 320798720 326369280 ⟨⟨142792502853, 142792502861⟩, ⟨138037960636, 147616828377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 320798720 326369280 ⟨⟨141700965849, 141700965858⟩, ⟨136973782086, 146497400701⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 179568640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182190080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 180879360) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 179568640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182190080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
