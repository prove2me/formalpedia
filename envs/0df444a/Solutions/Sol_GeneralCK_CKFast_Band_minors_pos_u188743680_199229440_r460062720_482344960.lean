-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:52.776984+00:00
-- url     : https://prove2.me/submissions/4aad7f52-4123-4cd1-b078-aff039da74d0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 460062720 465633280 ⟨⟨187911461678, 187911461681⟩, ⟨179551863373, 196450444639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 465633280 471203840 ⟨⟨189940311117, 189940311122⟩, ⟨181552675284, 198507119984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 460062720 465633280 ⟨⟨185183678298, 185183678307⟩, ⟨176899193281, 193645969283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 465633280 471203840 ⟨⟨187189218099, 187189218107⟩, ⟨178876679052, 195679382034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 471203840 476774400 ⟨⟨191965397071, 191965397077⟩, ⟨183549792280, 200559958047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 476774400 482344960 ⟨⟨193986768253, 193986768259⟩, ⟨185543262061, 202609008558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 471203840 476774400 ⟨⟨189191130793, 189191130802⟩, ⟨180850602555, 197709097676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 476774400 482344960 ⟨⟨191189462910, 191189462919⟩, ⟨182821009370, 199735163688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 460062720 465633280 ⟨⟨182480491194, 182480491203⟩, ⟨174269959141, 190867272190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 465633280 471203840 ⟨⟨184462688712, 184462688721⟩, ⟨176224097806, 192877376890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 460062720 465633280 ⟨⟨179801290676, 179801290685⟩, ⟨171663579692, 188113714966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 465633280 471203840 ⟨⟨181760116596, 181760116605⟩, ⟨173594353128, 190100470013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 471203840 476774400 ⟨⟨186441391958, 186441391968⟩, ⟨178174803375, 194883921050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 476774400 482344960 ⟨⟨188416645362, 188416645370⟩, ⟨180122119384, 196886949992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 471203840 476774400 ⟨⟨183715577586, 183715577595⟩, ⟨175521819211, 192083797541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 476774400 482344960 ⟨⟨185667716056, 185667716065⟩, ⟨177446019515, 194063740792⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 460062720 482344960 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 471203840) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 465633280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 476774400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 471203840) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 465633280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 196608000) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 476774400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
