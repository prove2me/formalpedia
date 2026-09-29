-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:55.08569+00:00
-- url     : https://prove2.me/submissions/86274d68-d0bf-45cf-8476-dbf5d9052943

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 159252480 160645120 ⟨⟨47250258383, 47250258388⟩, ⟨46446057663, 48057347958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 159252480 160645120 ⟨⟨47138745307, 47138745312⟩, ⟨46335520861, 47944853086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 160645120 162037760 ⟨⟨47651794071, 47651794077⟩, ⟨46846690612, 48459787865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 160645120 162037760 ⟨⟨47539377201, 47539377206⟩, ⟨46735251385, 48346387834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 159252480 160645120 ⟨⟨47027373012, 47027373014⟩, ⟨46225122758, 47832501091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 159252480 160645120 ⟨⟨46916140975, 46916140980⟩, ⟨46114862837, 47720291450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250019840 160645120 162037760 ⟨⟨47427101964, 47427101967⟩, ⟨46623951709, 48233131532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250019840 250347520 160645120 162037760 ⟨⟨47314967833, 47314967839⟩, ⟨46512791061, 48120018436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249364480 162037760 163430400 ⟨⟨48053173923, 48053173928⟩, ⟨47247167928, 48862071731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249364480 249692160 162037760 163430400 ⟨⟨47939854297, 47939854302⟩, ⟨47134827309, 48747767582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249364480 163430400 164823040 ⟨⟨48454398289, 48454398295⟩, ⟨47647489958, 49264199906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249364480 249692160 163430400 164823040 ⟨⟨48340176940, 48340176947⟩, ⟨47534248980, 49148992679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 162037760 163430400 ⟨⟨47826677149, 47826677152⟩, ⟨47022627087, 48633608010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250019840 250347520 162037760 163430400 ⟨⟨47713641951, 47713641957⟩, ⟨46910566735, 48519592489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249692160 250019840 163430400 164823040 ⟨⟨48226098912, 48226098915⟩, ⟨47421149236, 49033930869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 163430400 164823040 ⟨⟨48112163671, 48112163676⟩, ⟨47308190200, 48919013951⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250019840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249692160) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249364480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163430400) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250019840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
