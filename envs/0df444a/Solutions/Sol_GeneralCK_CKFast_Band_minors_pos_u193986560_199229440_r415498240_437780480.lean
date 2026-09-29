-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:37.367113+00:00
-- url     : https://prove2.me/submissions/d419c61c-dd6c-4300-b676-dd6d47c74c3c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 415498240 421068800 ⟨⟨167117217424, 167117217433⟩, ⟨162357823865, 171940013389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 415498240 421068800 ⟨⟨165867585089, 165867585098⟩, ⟨161133382001, 170664808067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 421068800 426639360 ⟨⟨169135139737, 169135139744⟩, ⟨164360494657, 173973095736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 421068800 426639360 ⟨⟨167873265517, 167873265526⟩, ⟨163123816232, 172685648701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 415498240 421068800 ⟨⟨164623934824, 164623934831⟩, ⟨159914720890, 169395789300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 415498240 421068800 ⟨⟨163386189739, 163386189748⟩, ⟨158701766212, 168132877603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 197918720 421068800 426639360 ⟨⟨166617373983, 166617373992⟩, ⟨161892920885, 171404387010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 199229440 421068800 426639360 ⟨⟨165367388571, 165367388580⟩, ⟨160667734581, 170129231549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 195297280 426639360 432209920 ⟨⟨171149159850, 171149159858⟩, ⟨166359309240, 176002228417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 196608000 426639360 432209920 ⟨⟨169875118062, 169875118070⟩, ⟨165110467325, 174702615235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 195297280 432209920 437780480 ⟨⟨173159326220, 173159326227⟩, ⟨168354315401, 178027460559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195297280 196608000 432209920 437780480 ⟨⟨171873190025, 171873190034⟩, ⟨167093381936, 176715755624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 426639360 432209920 ⟨⟨168607058526, 168607058535⟩, ⟨163867409778, 173409185128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 426639360 432209920 ⟨⟨167344905017, 167344905026⟩, ⟨162630062861, 172121859359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 197918720 432209920 437780480 ⟨⟨170593034627, 170593034636⟩, ⟨165838233120, 175410230455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 432209920 437780480 ⟨⟨169318784146, 169318784154⟩, ⟨164588795517, 174110806707⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 415498240 437780480 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 421068800) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 197918720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 196608000) (by decide) (join_sr (m := 432209920) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 195297280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 432209920) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 197918720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
