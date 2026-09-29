-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:33.220671+00:00
-- url     : https://prove2.me/submissions/e0574073-1cb2-4ece-aa97-690f267b060d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 214958080 217743360 ⟨⟨100219784434, 100219784442⟩, ⟨96519437756, 103969220079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 217743360 220528640 ⟨⟨101416960153, 101416960161⟩, ⟨97708296354, 105174701655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 214958080 217743360 ⟨⟨99409205385, 99409205389⟩, ⟨95728688992, 103138406306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 217743360 220528640 ⟨⟨100598033527, 100598033529⟩, ⟨96909225702, 104335516677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 220528640 223313920 ⟨⟨102612167616, 102612167624⟩, ⟨98895207932, 106378193308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 179568640 223313920 226099200 ⟨⟨103805419609, 103805419615⟩, ⟨100080185112, 107579707985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180879360 220528640 223313920 ⟨⟨101784934550, 101784934553⟩, ⟨98087855912, 105530678888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180879360 223313920 226099200 ⟨⟨102969920882, 102969920885⟩, ⟨99264591889, 106723905525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 182190080 214958080 217743360 ⟨⟨98604661742, 98604661749⟩, ⟨94943745334, 102313864236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 182190080 217743360 220528640 ⟨⟨99785176062, 99785176070⟩, ⟨96115994336, 103502636678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182190080 183500800 214958080 217743360 ⟨⟨97806056673, 97806056681⟩, ⟨94164513962, 101495492898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 217743360 220528640 ⟨⟨98978290673, 98978290681⟩, ⟨95328509156, 102675960454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 220528640 223313920 ⟨⟨100963803648, 100963803654⟩, ⟨97286376610, 104689501958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180879360 182190080 223313920 226099200 ⟨⟨102140556572, 102140556580⟩, ⟨98454904082, 105874472301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 183500800 220528640 223313920 ⟨⟨100148677576, 100148677584⟩, ⟨96490676664, 103854561088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 223313920 226099200 ⟨⟨101317229116, 101317229124⟩, ⟨97651028077, 105031306678⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 214958080 226099200 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 223313920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 217743360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182190080) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 223313920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
