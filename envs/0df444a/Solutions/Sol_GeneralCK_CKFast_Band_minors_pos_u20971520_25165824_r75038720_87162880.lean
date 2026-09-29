-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:17:32.245503+00:00
-- url     : https://prove2.me/submissions/04df9d1b-6a96-454d-a1fc-1fe472bba5a6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/40, 3/100]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 20971520 22020096 75038720 78069760 ⟨⟨175060038263, 175060038284⟩, ⟨161972481912, 188753038223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 22020096 78069760 81100800 ⟨⟨179653783312, 179653783333⟩, ⟨166625585881, 193270496166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 22020096 23068672 75038720 78069760 ⟨⟨171283436114, 171283436134⟩, ⟨158560326366, 184583764108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 22020096 23068672 78069760 81100800 ⟨⟨175843555360, 175843555380⟩, ⟨163173021948, 189075724839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 22020096 81100800 84131840 ⟨⟨184147413737, 184147413764⟩, ⟨171179231509, 197687837553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 20971520 22020096 84131840 87162880 ⟨⟨188545504054, 188545504081⟩, ⟨175637837484, 202009761081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 22020096 23068672 81100800 84131840 ⟨⟨180306648337, 180306648357⟩, ⟨167689480360, 193470449358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 22020096 23068672 84131840 87162880 ⟨⟨184677043774, 184677043794⟩, ⟨172113877787, 197772392233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 23068672 24117248 75038720 78069760 ⟨⟨167678375556, 167678375581⟩, ⟨155298984877, 180608764695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 23068672 24117248 78069760 81100800 ⟨⟨172203515753, 172203515778⟩, ⟨159870599875, 185073059305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 24117248 25165824 75038720 78069760 ⟨⟨164232620625, 164232620649⟩, ⟨152177949407, 176813889111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 24117248 25165824 78069760 81100800 ⟨⟨168721698023, 168721698047⟩, ⟨156708002437, 181248713102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 23068672 24117248 81100800 84131840 ⟨⟨176634633065, 176634633090⟩, ⟨164349087171, 189442949667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 23068672 24117248 84131840 87162880 ⟨⟨180975824977, 180975824997⟩, ⟨168738395795, 193722659114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 24117248 25165824 81100800 84131840 ⟨⟨173119667508, 173119667533⟩, ⟨161147926499, 185591907102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 24117248 25165824 84131840 87162880 ⟨⟨177430409099, 177430409124⟩, ⟨165501457836, 189847475743⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 20971520 25165824 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 23068672) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 22020096) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 22020096) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 24117248) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 78069760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 24117248) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
