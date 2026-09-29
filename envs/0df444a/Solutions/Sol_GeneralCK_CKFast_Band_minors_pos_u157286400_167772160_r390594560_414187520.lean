-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r390594560_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:06:45.222211+00:00
-- url     : https://prove2.me/submissions/3124bb09-2683-4040-be14-ce26a3981697

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [149/320, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 390594560 396492800 ⟨⟨193630912470, 193630912479⟩, ⟨184501216683, 202974177678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 396492800 402391040 ⟨⟨196153544038, 196153544047⟩, ⟨186993726681, 205526242655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 390594560 396492800 ⟨⟨190850537644, 190850537653⟩, ⟨181816611791, 200095476005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 396492800 402391040 ⟨⟨193346537173, 193346537181⟩, ⟨184282333753, 202621119107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 402391040 408289280 ⟨⟨198668541295, 198668541305⟩, ⟨189478767209, 208070502637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 159907840 408289280 414187520 ⟨⟨201176019394, 201176019402⟩, ⟨191956450375, 210607075865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 402391040 408289280 ⟨⟨195835161321, 195835161330⟩, ⟨186740838788, 205139222384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 162529280 408289280 414187520 ⟨⟨198316520066, 198316520074⟩, ⟨189192234003, 207649898724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 390594560 396492800 ⟨⟨188104493098, 188104493103⟩, ⟨179164468305, 197253023606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 165150720 396492800 402391040 ⟨⟨190573829232, 190573829237⟩, ⟨181603391956, 199752190103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 390594560 396492800 ⟨⟨185391811345, 185391811354⟩, ⟨176543874581, 194445796009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165150720 167772160 396492800 402391040 ⟨⟨187834458937, 187834458946⟩, ⟨178955994784, 196918438548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 402391040 408289280 ⟨⟨193036042278, 193036042283⟩, ⟨184035344638, 202244075284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 162529280 165150720 408289280 414187520 ⟨⟨195491237248, 195491237251⟩, ⟨186460428661, 204728786903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 167772160 402391040 408289280 ⟨⟨190270229198, 190270229206⟩, ⟨181361383508, 199384051707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 408289280 414187520 ⟨⟨192699222376, 192699222384⟩, ⟨183760138456, 201842738319⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 390594560 414187520 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396492800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 408289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 402391040) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 396492800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 165150720) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 408289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (149/320 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
