-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u242483200_243793920_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:49.632451+00:00
-- url     : https://prove2.me/submissions/0b1bb7b5-82bf-46b9-8006-2867848ff34d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/128, 93/320]`, `ρ ∈ [243/1280, 503/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 242483200 242810880 159252480 160645120 ⟨⟨49510902720, 49510902726⟩, ⟨48686727329, 50338081136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242810880 243138560 159252480 160645120 ⟨⟨49396461652, 49396461657⟩, ⟨48573305808, 50222614641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 242810880 160645120 162037760 ⟨⟨49930697255, 49930697261⟩, ⟨49105591451, 50758807461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242810880 243138560 160645120 162037760 ⟨⟨49815334795, 49815334801⟩, ⟨48991249935, 50642418183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243138560 243466240 159252480 160645120 ⟨⟨49282172207, 49282172208⟩, ⟨48460033671, 50107302020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243466240 243793920 159252480 160645120 ⟨⟨49168033815, 49168033820⟩, ⟨48346910358, 49992142710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243138560 243466240 160645120 162037760 ⟨⟨49700124863, 49700124867⟩, ⟨48877058707, 50526183687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243466240 243793920 160645120 162037760 ⟨⟨49585066889, 49585066894⟩, ⟨48763017204, 50410103405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 242810880 162037760 163430400 ⟨⟨50350314005, 50350314011⟩, ⟨49524278076, 51179355708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242810880 243138560 162037760 163430400 ⟨⟨50234031306, 50234031312⟩, ⟨49409017712, 51062044806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 242483200 243138560 163430400 164823040 ⟨⟨50711133160, 50711133167⟩, ⟨49299005442, 52131718464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243466240 162037760 163430400 ⟨⟨50117902035, 50117902039⟩, ⟨49293908536, 50944889586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243466240 243793920 162037760 163430400 ⟨⟨50001925619, 50001925625⟩, ⟨49178949981, 50827889479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243138560 243466240 163430400 164823040 ⟨⟨50535504127, 50535504131⟩, ⟨49710583563, 51363420124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243466240 243793920 163430400 164823040 ⟨⟨50418610408, 50418610413⟩, ⟨49594709090, 51245501334⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 242483200 243793920 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242810880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243466240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243138560) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 163430400) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 243466240) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/128 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
