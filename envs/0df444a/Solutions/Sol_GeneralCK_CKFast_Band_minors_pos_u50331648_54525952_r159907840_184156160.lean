-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_54525952_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:13:31.955659+00:00
-- url     : https://prove2.me/submissions/0accbc0a-febb-4238-9634-6b4ff636bb62

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 13/200]`, `ρ ∈ [61/320, 281/1280]` by 10 cells of the computing
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
theorem cell0 : cellOK 50331648 51380224 159907840 165969920 ⟨⟨197180247319, 197180247335⟩, ⟨187129230903, 207516942190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 51380224 52428800 159907840 165969920 ⟨⟨195145199496, 195145199509⟩, ⟨185219781722, 205350703284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 52428800 165969920 172032000 ⟨⟨201462817526, 201462817539⟩, ⟨186882043003, 216653157165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 53477376 159907840 165969920 ⟨⟨193149370748, 193149370760⟩, ⟨183346468127, 203226933502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 53477376 54525952 159907840 165969920 ⟨⟨191191504829, 191191504841⟩, ⟨181508147241, 201144256654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 52428800 54525952 165969920 172032000 ⟨⟨197421370194, 197421370210⟩, ⟨183181926435, 212248229283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 50331648 52428800 172032000 178094080 ⟨⟨206681743963, 206681743979⟩, ⟨192114057408, 221845202456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 50331648 52428800 178094080 184156160 ⟨⟨211817953059, 211817953072⟩, ⟨197264795104, 226953472539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 54525952 172032000 178094080 ⟨⟨202593787460, 202593787475⟩, ⟨188362541235, 217399665886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52428800 54525952 178094080 184156160 ⟨⟨207686260292, 207686260307⟩, ⟨193464689667, 222470017758⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 54525952 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 52428800) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 51380224) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 165969920) (by decide) (join_su (m := 53477376) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 52428800) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 178094080) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
