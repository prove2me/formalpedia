-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:10:25.18085+00:00
-- url     : https://prove2.me/submissions/b937e0b2-7cd1-480a-afe4-f18803ec5af4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [277/1280, 571/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 181534720 182927360 ⟨⟨53593379056, 53593379063⟩, ⟨52187544858, 55007481193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 182927360 184320000 ⟨⟨53992019115, 53992019122⟩, ⟨52584514372, 55407797712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 181534720 182927360 ⟨⟨53341984674, 53341984681⟩, ⟨51938939567, 54753272199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 182927360 184320000 ⟨⟨53738851196, 53738851201⟩, ⟨52334139889, 55151810857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 184320000 185712640 ⟨⟨54390509354, 54390509361⟩, ⟨52981334246, 55807964223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 185712640 187105280 ⟨⟨54788850113, 54788850119⟩, ⟨53378004819, 56207981065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 184320000 185712640 ⟨⟨54135569873, 54135569878⟩, ⟨52729192536, 55550201492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 185712640 187105280 ⟨⟨54532141036, 54532141042⟩, ⟨53124097839, 55948444439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 181534720 182927360 ⟨⟨53091201958, 53091201961⟩, ⟨51690933256, 54499687708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 182927360 184320000 ⟨⟨53486297991, 53486297993⟩, ⟨52084367433, 54896451556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 181534720 182927360 ⟨⟨52841026461, 52841026467⟩, ⟨51443521575, 54246723189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 182927360 184320000 ⟨⟨53234355036, 53234355043⟩, ⟨51835192630, 54641715266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 184320000 185712640 ⟨⟨53881248132, 53881248135⟩, ⟨52477655875, 55293069350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 185712640 187105280 ⟨⟨54276052710, 54276052713⟩, ⟨52870798911, 55689541414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 184320000 185712640 ⟨⟨53627539654, 53627539660⟩, ⟨52226719874, 55036563231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 185712640 187105280 ⟨⟨54020580637, 54020580642⟩, ⟨52618103627, 55431267411⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 185712640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184320000) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 182927360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 185712640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
