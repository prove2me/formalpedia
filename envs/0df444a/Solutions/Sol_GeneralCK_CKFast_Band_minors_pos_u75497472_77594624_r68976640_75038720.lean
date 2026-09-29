-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_77594624_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:30:13.774368+00:00
-- url     : https://prove2.me/submissions/5d58eeeb-9bd6-43b3-bd08-e15eb4104c2c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 37/400]`, `ρ ∈ [421/5120, 229/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 75497472 76021760 68976640 70492160 ⟨⟨76210186011, 76210186021⟩, ⟨73467599008, 78985600185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 76021760 70492160 72007680 ⟨⟨77690755690, 77690755701⟩, ⟨74944412327, 80469809482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 76021760 76546048 68976640 70492160 ⟨⟨75810988172, 75810988181⟩, ⟨73082909974, 78571570908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76021760 76546048 70492160 72007680 ⟨⟨77285205205, 77285205217⟩, ⟨74553370330, 80049430330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 76021760 72007680 75038720 ⟨⟨79899826048, 79899826058⟩, ⟨76163453738, 83695906651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 76021760 76546048 72007680 75038720 ⟨⟨79484887838, 79484887848⟩, ⟨75769088718, 83259790836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76546048 77070336 68976640 70492160 ⟨⟨75415580231, 75415580240⟩, ⟨72701841497, 78161505982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 76546048 77070336 70492160 72007680 ⟨⟨76883487833, 76883487845⟩, ⟨74165992540, 79633058246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77070336 77594624 68976640 70492160 ⟨⟨75023903128, 75023903137⟩, ⟨72324337504, 77755343229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77070336 77594624 70492160 72007680 ⟨⟨76485544075, 76485544086⟩, ⟨73782222430, 79220630638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 76546048 77070336 72007680 75038720 ⟨⟨79073845474, 79073845486⟩, ⟨75378384117, 82827815799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 77070336 77594624 72007680 75038720 ⟨⟨78666638842, 78666638852⟩, ⟨74991283932, 82399917097⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 77594624 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 76546048) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 76021760) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 70492160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 76021760) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 72007680) (by decide) (join_su (m := 77070336) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 70492160) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 77070336) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (37/400 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
