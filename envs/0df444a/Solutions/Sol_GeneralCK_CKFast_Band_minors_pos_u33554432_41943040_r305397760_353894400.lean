-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:52:25.554132+00:00
-- url     : https://prove2.me/submissions/74938716-3eb7-45d8-826c-83a02f9ac11b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [233/640, 27/64]` by 15 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 305397760 317521920 ⟨⟨349417570333, 349417570352⟩, ⟨327540553935, 372045998189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 35651584 37748736 305397760 317521920 ⟨⟨343540017980, 343540017998⟩, ⟨322112993085, 365703270198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 35651584 317521920 329646080 ⟨⟨357220879475, 357220879491⟩, ⟨335536669076, 379614753879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 317521920 329646080 ⟨⟨351351874734, 351351874752⟩, ⟨330101192510, 373299127164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 39845888 305397760 317521920 ⟨⟨337849533435, 337849533452⟩, ⟨316854163266, 359566156844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 39845888 41943040 305397760 317521920 ⟨⟨332334932679, 332334932695⟩, ⟨311754152620, 353622239144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 39845888 317521920 329646080 ⟨⟨345664790603, 345664790621⟩, ⟨324830412720, 367182739491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 39845888 41943040 317521920 329646080 ⟨⟨340148891659, 340148891673⟩, ⟨319714777884, 361253716211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 35651584 329646080 341770240 ⟨⟨364865830201, 364865830215⟩, ⟨343369307446, 387032783359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 35651584 37748736 329646080 341770240 ⟨⟨359006937193, 359006937211⟩, ⟨337928307566, 380744793845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 33554432 37748736 341770240 353894400 ⟨⟨369416928547, 369416928564⟩, ⟨338074070833, 402195185770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 37748736 39845888 329646080 341770240 ⟨⟨353325022606, 353325022623⟩, ⟨332648088274, 374649975925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 41943040 329646080 341770240 ⟨⟨347809768499, 347809768516⟩, ⟨327519435710, 368736957752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 37748736 39845888 341770240 353894400 ⟨⟨360840134773, 360840134790⟩, ⟨340317071779, 381977625887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 39845888 41943040 341770240 353894400 ⟨⟨355327195726, 355327195744⟩, ⟨335177696890, 376081506752⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 35651584) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 35651584) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 39845888) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 39845888) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 37748736) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 35651584) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 341770240) (by decide) (join_su (m := 39845888) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 39845888) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
