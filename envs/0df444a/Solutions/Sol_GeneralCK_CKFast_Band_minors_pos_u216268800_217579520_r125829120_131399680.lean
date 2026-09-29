-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u216268800_217579520_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:16:31.517695+00:00
-- url     : https://prove2.me/submissions/8ac68784-03fb-46fa-b322-082399d2bd16

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/128, 83/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 216268800 216596480 125829120 127221760 ⟨⟨47201179412, 47201179419⟩, ⟨46312726878, 48093154646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216596480 216924160 125829120 127221760 ⟨⟨47097185500, 47097185506⟩, ⟨46209923924, 47987961844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 216596480 127221760 128614400 ⟨⟨47705140834, 47705140840⟩, ⟨46815622946, 48598182284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216596480 216924160 127221760 128614400 ⟨⟨47600099558, 47600099564⟩, ⟨46711774309, 48491940448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216924160 217251840 125829120 127221760 ⟨⟨46993366330, 46993366332⟩, ⟨46107292707, 47882946816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217251840 217579520 125829120 127221760 ⟨⟨46889721199, 46889721205⟩, ⟨46004832536, 47778108856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216924160 217251840 127221760 128614400 ⟨⟨47495234407, 47495234410⟩, ⟨46608098792, 48385877769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217251840 217579520 127221760 128614400 ⟨⟨47390544675, 47390544682⟩, ⟨46504595697, 48279993540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 216268800 216596480 128614400 130007040 ⟨⟨48208790531, 48208790537⟩, ⟨47318208124, 49102897357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216596480 216924160 128614400 130007040 ⟨⟨48102703786, 48102703793⟩, ⟨47213315693, 48995608389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216268800 216596480 130007040 131399680 ⟨⟨48712129330, 48712129336⟩, ⟨47820483237, 49607300693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216596480 216924160 130007040 131399680 ⟨⟨48604999004, 48604999010⟩, ⟨47714548891, 49498966489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216924160 217251840 128614400 130007040 ⟨⟨47996794540, 47996794543⟩, ⟨47108597751, 48888499952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217251840 217579520 128614400 130007040 ⟨⟨47891062081, 47891062086⟩, ⟨47004053598, 48781571338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216924160 217251840 130007040 131399680 ⟨⟨48498047540, 48498047543⟩, ⟨47608790393, 49390814183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217251840 217579520 130007040 131399680 ⟨⟨48391274223, 48391274228⟩, ⟨47503207043, 49282843058⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 216268800 217579520 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 216924160) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 217251840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 217251840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216924160) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 216596480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 216596480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 217251840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 217251840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/128 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((216268800 : ℤ) : ℝ) / (D : ℝ)) = (33/128 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
