-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_71303168_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:20.382668+00:00
-- url     : https://prove2.me/submissions/b03af34a-3f9b-4547-8b1a-187f7ef2c097

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 17/200]`, `ρ ∈ [133/1280, 303/2560]` by 18 cells of the computing
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
theorem cell0 : cellOK 67108864 68157440 87162880 90193920 ⟨⟨102214448436, 102214448446⟩, ⟨96185592190, 108389576831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 68157440 90193920 93224960 ⟨⟨105198186755, 105198186765⟩, ⟨99157830108, 111383567256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 68157440 69206016 87162880 90193920 ⟨⟨101122739329, 101122739339⟩, ⟨95162252864, 107226525317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 68157440 69206016 90193920 93224960 ⟨⟨104082737808, 104082737820⟩, ⟨98110592849, 110196986208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 68157440 93224960 96256000 ⟨⟨108155483633, 108155483646⟩, ⟨102104098688, 114350654190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 68157440 96256000 99287040 ⟨⟨111086875698, 111086875709⟩, ⟨105024917429, 117291391446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 68157440 69206016 93224960 96256000 ⟨⟨107016904419, 107016904430⟩, ⟨101033561335, 113141164107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 68157440 69206016 96256000 99287040 ⟨⟨109925756626, 109925756639⟩, ⟨103931659392, 116059592945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 69206016 69730304 87162880 90193920 ⟨⟨100318008156, 100318008166⟩, ⟨96277534853, 104423208925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69730304 70254592 87162880 90193920 ⟨⟨99788050258, 99788050269⟩, ⟨95771107254, 103869047824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 69206016 70254592 90193920 93224960 ⟨⟨102988908957, 102988908967⟩, ⟨97083320633, 109033773959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 70254592 70778880 87162880 90193920 ⟨⟨99263218681, 99263218691⟩, ⟨95269524144, 103320305721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 70778880 71303168 87162880 90193920 ⟨⟨98743432044, 98743432054⟩, ⟨94772709253, 102776895884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 70254592 71303168 90193920 93224960 ⟨⟨101916016706, 101916016719⟩, ⟨96075390029, 107893182910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 69206016 70254592 93224960 96256000 ⟨⟨105900195353, 105900195366⟩, ⟨99983253600, 111955275872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 69206016 70254592 96256000 99287040 ⟨⟨108786741558, 108786741571⟩, ⟨102858879571, 114851612976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 70254592 71303168 93224960 96256000 ⟨⟨104804670498, 104804670508⟩, ⟨98952548665, 110792240522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 70254592 71303168 96256000 99287040 ⟨⟨107669142641, 107669142651⟩, ⟨101805948305, 113666701727⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 71303168 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 69206016) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 68157440) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 68157440) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 70254592) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 69730304) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 90193920) (by decide) (join_su (m := 70778880) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 70254592) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 96256000) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
