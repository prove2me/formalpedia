-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:12.060043+00:00
-- url     : https://prove2.me/submissions/0f7ed6ec-41df-4018-8980-b3ca02a84f15

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [201/320, 419/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 526909440 532480000 ⟨⟨224267404902, 224267404912⟩, ⟨215266288845, 233449937543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 532480000 538050560 ⟨⟨226340671172, 226340671182⟩, ⟨217312637564, 235549711355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 526909440 532480000 ⟨⟨221166492042, 221166492052⟩, ⟨212244366620, 230268793162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 532480000 538050560 ⟨⟨223218269051, 223218269061⟩, ⟨214269114779, 232347224669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 538050560 549191680 ⟨⟨229443681547, 229443681557⟩, ⟨218722709221, 240420611563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180879360 183500800 538050560 543621120 ⟨⟨225266486110, 225266486119⟩, ⟨216290369355, 234422024553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 543621120 549191680 ⟨⟨227311192851, 227311192861⟩, ⟨218308178920, 236493243506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 183500800 186122240 526909440 532480000 ⟨⟨218092000131, 218092000140⟩, ⟨209247750440, 227115192435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 532480000 538050560 ⟨⟨220122200848, 220122200857⟩, ⟨211250825267, 229172179183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 188743680 526909440 532480000 ⟨⟨215043294874, 215043294884⟩, ⟨206275831767, 223988475557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 532480000 538050560 ⟨⟨217051836833, 217051836842⟩, ⟨208257164536, 226023920218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 183500800 186122240 538050560 543621120 ⟨⟨222148961730, 222148961739⟩, ⟨213250523516, 231225657556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 543621120 549191680 ⟨⟨224172330353, 224172330363⟩, ⟨215246891753, 233275676130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 538050560 543621120 ⟨⟨219057056370, 219057056379⟩, ⟨210235235043, 228055977040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 543621120 549191680 ⟨⟨221058999071, 221058999081⟩, ⟨212210087924, 230084692556⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 526909440 549191680 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 538050560) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 532480000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (leaf_ok cell4) (join_sr (m := 543621120) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 538050560) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 532480000) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 186122240) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 543621120) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
