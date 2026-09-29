-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u31457280_33554432_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:21:34.49862+00:00
-- url     : https://prove2.me/submissions/fe80a4ba-d058-418a-a6c8-92a8fbc7661a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/80, 1/25]`, `ρ ∈ [3/40, 229/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 31457280 31981568 62914560 65945600 ⟨⟨126675384623, 126675384644⟩, ⟨119481246487, 134074824736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 31981568 32505856 62914560 65945600 ⟨⟨125494897895, 125494897912⟩, ⟨118383423709, 132807504951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 31457280 31981568 65945600 68976640 ⟨⟨131232426106, 131232426128⟩, ⟨124049004852, 138616614099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 31981568 32505856 65945600 68976640 ⟨⟨130027243741, 130027243762⟩, ⟨122925501642, 137325741576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 32505856 33030144 62914560 65945600 ⟨⟨124337275127, 124337275135⟩, ⟨117306501569, 131565142933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33030144 33554432 62914560 65945600 ⟨⟨123201815969, 123201815989⟩, ⟨116249849063, 130346963540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 32505856 33030144 65945600 68976640 ⟨⟨128845047526, 128845047534⟩, ⟨121823069206, 136059894058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 33030144 33554432 65945600 68976640 ⟨⟨127685143080, 127685143101⟩, ⟨120741079946, 134818305315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 31457280 32505856 68976640 72007680 ⟨⟨135086082405, 135086082425⟩, ⟨124858459914, 145725154799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 31457280 32505856 72007680 75038720 ⟨⟨139463067365, 139463067382⟩, ⟨129247315922, 150081848728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 32505856 33554432 68976640 72007680 ⟨⟨132675227442, 132675227463⟩, ⟨122669374103, 143076893393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 32505856 33554432 72007680 75038720 ⟨⟨137008600090, 137008600106⟩, ⟨127012114704, 147393041638⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 31457280 33554432 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 32505856) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 31981568) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 31981568) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 33030144) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 33030144) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 32505856) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 72007680) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/80 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((31457280 : ℤ) : ℝ) / (D : ℝ)) = (3/80 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
