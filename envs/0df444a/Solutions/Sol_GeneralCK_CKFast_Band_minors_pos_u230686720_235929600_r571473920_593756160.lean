-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:38:29.33916+00:00
-- url     : https://prove2.me/submissions/f569b196-d74d-4497-9a01-5e3602fa6abd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 571473920 577044480 ⟨⟨180341953606, 180341953615⟩, ⟨175816850944, 184921131122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 571473920 577044480 ⟨⟨178910761641, 178910761644⟩, ⟨174406899805, 183468482970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 577044480 582615040 ⟨⟨181965547953, 181965547961⟩, ⟨177426251044, 186558913654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 577044480 582615040 ⟨⟨180523364191, 180523364196⟩, ⟨176005328315, 185095256950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 571473920 577044480 ⟨⟨177483684245, 177483684253⟩, ⟨173000948534, 182020064638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 571473920 577044480 ⟨⟨176060674520, 176060674528⟩, ⟨171598951263, 180575828189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 577044480 582615040 ⟨⟨179085283875, 179085283883⟩, ⟨174588395487, 183635817718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234618880 235929600 577044480 582615040 ⟨⟨177651260362, 177651260370⟩, ⟨173175406928, 182180548305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231997440 582615040 588185600 ⟨⟨183587571924, 183587571933⟩, ⟨179034091282, 188195114154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 233308160 582615040 588185600 ⟨⟨182134429448, 182134429452⟩, ⟨177602229446, 186720482589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231997440 588185600 593756160 ⟨⟨185208045679, 185208045687⟩, ⟨180640391608, 189829752977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231997440 233308160 588185600 593756160 ⟨⟨183743977083, 183743977087⟩, ⟨179197622674, 188344179756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 582615040 588185600 ⟨⟨180685378819, 180685378827⟩, ⟨176174347079, 185250055676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 582615040 588185600 ⟨⟨179240373660, 179240373669⟩, ⟨174750398790, 183783786040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 588185600 593756160 ⟨⟨182283988278, 182283988287⟩, ⟨177758822319, 186862797895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 588185600 593756160 ⟨⟨180828033152, 180828033160⟩, ⟨176323945405, 185385560307⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 571473920 593756160 t = true :=
  ⟨_, (join_sr (m := 582615040) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 577044480) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 577044480) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234618880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233308160) (by decide) (join_sr (m := 588185600) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231997440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 588185600) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234618880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
