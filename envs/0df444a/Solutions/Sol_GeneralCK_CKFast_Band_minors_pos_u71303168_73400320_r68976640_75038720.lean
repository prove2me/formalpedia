-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_73400320_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:04.96539+00:00
-- url     : https://prove2.me/submissions/96833baa-466c-48f7-bfae-9cc336b855cc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 7/80]`, `ρ ∈ [421/5120, 229/2560]` by 10 cells of the computing
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
theorem cell0 : cellOK 71303168 71827456 68976640 72007680 ⟨⟨80315104820, 80315104833⟩, ⟨76413810565, 84281887087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71827456 72351744 68976640 72007680 ⟨⟨79879932024, 79879932028⟩, ⟨76001277293, 83823374395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 71827456 72007680 75038720 ⟨⟨83367239082, 83367239092⟩, ⟨79457277663, 87342112032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71827456 72351744 72007680 75038720 ⟨⟨82918807293, 82918807295⟩, ⟨79031463223, 86870374541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 72351744 72876032 68976640 70492160 ⟨⟨78688434514, 78688434524⟩, ⟨75855061219, 81556684389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 72351744 72876032 70492160 72007680 ⟨⟨80208052521, 80208052533⟩, ⟨77370934950, 83079913872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 72876032 73400320 68976640 70492160 ⟨⟨78265182657, 78265182667⟩, ⟨75447401382, 81117484798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 72876032 73400320 70492160 72007680 ⟨⟨79778179333, 79778179343⟩, ⟨76956650461, 82634099118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 72351744 72876032 72007680 75038720 ⟨⟨82474801856, 82474801866⟩, ⟨78609802958, 86403346922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 72876032 73400320 72007680 75038720 ⟨⟨82035151287, 82035151297⟩, ⟨78192230372, 85940952426⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 73400320 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 72351744) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 71827456) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 71827456) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 72007680) (by decide) (join_su (m := 72876032) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 70492160) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 72876032) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (7/80 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
