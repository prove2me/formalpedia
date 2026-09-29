-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r450887680_499384320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:33:29.694497+00:00
-- url     : https://prove2.me/submissions/9b194dea-cf8d-436f-9161-d250ef7e3eed

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [43/80, 381/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 450887680 463011840 ⟨⟨482783872926, 482783872944⟩, ⟨448888270013, 517430627706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 20971520 463011840 475136000 ⟨⟨488972186817, 488972186836⟩, ⟨455370419692, 523262494299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 20971520 25165824 450887680 463011840 ⟨⟨468833595495, 468833595515⟩, ⟨436151361188, 502329472218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 463011840 475136000 ⟨⟨475114424526, 475114424545⟩, ⟨442686783351, 508296929563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 20971520 475136000 487260160 ⟨⟨495090868517, 495090868536⟩, ⟨461772840894, 529038026081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 20971520 487260160 499384320 ⟨⟨501144126952, 501144126970⟩, ⟨468100230094, 534760691669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 25165824 475136000 487260160 ⟨⟨481323016840, 481323016859⟩, ⟨449141735040, 514203225548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 20971520 25165824 487260160 499384320 ⟨⟨487463644076, 487463644095⟩, ⟨455520848067, 520052056123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 29360128 450887680 463011840 ⟨⟨455739956115, 455739956133⟩, ⟨424145790578, 488184574177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 25165824 29360128 463011840 475136000 ⟨⟨462092547387, 462092547405⟩, ⟨430718236032, 494262215732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 29360128 33554432 450887680 463011840 ⟨⟨443378843016, 443378843033⟩, ⟨412777032733, 474852580514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 29360128 33554432 463011840 475136000 ⟨⟨449785556452, 449785556469⟩, ⟨419372599607, 481018847288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 475136000 487260160 ⟨⟨468371238512, 468371238529⟩, ⟨437210114620, 500275142753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 25165824 29360128 487260160 499384320 ⟨⟨474580303001, 474580303019⟩, ⟨443625958288, 506227186766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 29360128 33554432 475136000 487260160 ⟨⟨456117462413, 456117462429⟩, ⟨425888017491, 487117877658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 487260160 499384320 ⟨⟨462378790695, 462378790712⟩, ⟨432327693224, 493153568262⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 450887680 499384320 t = true :=
  ⟨_, (join_su (m := 25165824) (by decide) (join_sr (m := 475136000) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 463011840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 20971520) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 487260160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 475136000) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 463011840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 29360128) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 487260160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  have e3 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
