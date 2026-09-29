-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_69206016_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:22:10.643419+00:00
-- url     : https://prove2.me/submissions/b1cc2de2-70b9-4b3f-9f84-0b87b3f78f91

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 33/400]`, `ρ ∈ [3/40, 421/5120]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 67633152 62914560 64430080 ⟨⟨76734085949, 76734085959⟩, ⟨73749069282, 79758556595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 67633152 64430080 65945600 ⟨⟨78354102419, 78354102429⟩, ⟨75365089399, 81382401451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67633152 68157440 62914560 64430080 ⟨⟨76294480056, 76294480069⟩, ⟨73327184708, 79300792362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 67633152 68157440 64430080 65945600 ⟨⟨77906986261, 77906986274⟩, ⟨74935689225, 80917136086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 67633152 65945600 67461120 ⟨⟨79966098735, 79966098747⟩, ⟨76973171939, 82998144136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 67633152 67461120 68976640 ⟨⟨81570163440, 81570163452⟩, ⟨78573403846, 84605874801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 67633152 68157440 65945600 67461120 ⟨⟨79511575774, 79511575784⟩, ⟨76536358358, 82525482342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 67633152 68157440 67461120 68976640 ⟨⟨81108335367, 81108335377⟩, ⟨78129277317, 84125919470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 68157440 68681728 62914560 64430080 ⟨⟨75859591385, 75859591394⟩, ⟨72909785437, 78847985018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 68157440 68681728 64430080 65945600 ⟨⟨77464644570, 77464644579⟩, ⟨74510832331, 80456884020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 68681728 69206016 62914560 64430080 ⟨⟨75429337695, 75429337705⟩, ⟨72496793831, 78400047538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 68681728 69206016 64430080 65945600 ⟨⟨77026994473, 77026994485⟩, ⟨74090440417, 80001557631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 68157440 68681728 65945600 67461120 ⟨⟨79061882837, 79061882850⟩, ⟨76104144368, 82057888552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 68157440 68681728 67461120 68976640 ⟨⟨80651391241, 80651391254⟩, ⟨77689805077, 83651085200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 68681728 69206016 65945600 67461120 ⟨⟨78616936466, 78616936476⟩, ⟨75676451051, 81595274587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 68681728 69206016 67461120 68976640 ⟨⟨80199247040, 80199247050⟩, ⟨77254907614, 83181283268⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 69206016 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 68157440) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 67633152) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 67633152) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 67461120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 65945600) (by decide) (join_su (m := 68681728) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 64430080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 68681728) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 67461120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (33/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
