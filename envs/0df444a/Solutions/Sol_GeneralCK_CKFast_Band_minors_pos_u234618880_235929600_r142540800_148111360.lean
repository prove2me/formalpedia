-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u234618880_235929600_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:34:42.572269+00:00
-- url     : https://prove2.me/submissions/1e5b4a6b-09e9-4f06-b7b7-49db6bcfe6e8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [179/640, 9/32]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 234618880 234946560 142540800 143933440 ⟨⟨46981874991, 46981874996⟩, ⟨46144140841, 47822744106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 234946560 235274240 142540800 143933440 ⟨⟨46875051511, 46875051515⟩, ⟨46038375649, 47714855904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 234618880 234946560 143933440 145326080 ⟨⟨47426589869, 47426589876⟩, ⟨46587886419, 48268429559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234946560 235274240 143933440 145326080 ⟨⟨47318806388, 47318806392⟩, ⟨46481162717, 48159579868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235274240 235601920 142540800 143933440 ⟨⟨46768381625, 46768381630⟩, ⟨45932761619, 47607123751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235601920 235929600 142540800 143933440 ⟨⟨46661864751, 46661864758⟩, ⟨45827298184, 47499547048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 235274240 235601920 143933440 145326080 ⟨⟨47211177557, 47211177564⟩, ⟨46374591234, 48050887285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235601920 235929600 143933440 145326080 ⟨⟨47103702796, 47103702801⟩, ⟨46268171400, 47942351211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 234946560 145326080 146718720 ⟨⟨47871091307, 47871091313⟩, ⟨47031418977, 48713901144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234946560 235274240 145326080 146718720 ⟨⟨47762349180, 47762349181⟩, ⟨46923738115, 48604091325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 234946560 146718720 148111360 ⟨⟨48315379816, 48315379821⟩, ⟨47474739027, 49159159374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234946560 235274240 146718720 148111360 ⟨⟨48205680392, 48205680396⟩, ⟨47366102352, 49048390786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235601920 145326080 146718720 ⟨⟨47653762754, 47653762760⟩, ⟨46816210524, 48494439668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235601920 235929600 145326080 146718720 ⟨⟨47545331447, 47545331452⟩, ⟨46708835628, 48384945572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235274240 235601920 146718720 148111360 ⟨⟨48096137718, 48096137723⟩, ⟨47257619991, 48937781407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235601920 235929600 146718720 148111360 ⟨⟨47986751202, 47986751208⟩, ⟨47149291367, 48827330628⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 234618880 235929600 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 234946560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235601920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 235274240) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234946560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235601920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (179/640 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
