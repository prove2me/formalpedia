-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:45:06.166249+00:00
-- url     : https://prove2.me/submissions/95a658ee-96c7-4fc2-965f-cb3e0591de84

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [11/20, 97/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 461373440 473169920 ⟨⟨279596418451, 279596418463⟩, ⟨265724969534, 293828836545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 117964800 120586240 461373440 473169920 ⟨⟨275813369223, 275813369232⟩, ⟨262113438205, 289870311925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 117964800 473169920 484966400 ⟨⟨285173634167, 285173634179⟩, ⟨271262474065, 299439229150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 473169920 484966400 ⟨⟨281349334596, 281349334607⟩, ⟨267607747064, 295441707778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 123207680 461373440 473169920 ⟨⟨272083479088, 272083479099⟩, ⟨258551667464, 285968375487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 125829120 461373440 473169920 ⟨⟨268405117320, 268405117327⟩, ⟨255038133894, 282121291000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 120586240 123207680 473169920 484966400 ⟨⟨277577612981, 277577612993⟩, ⟨264002316714, 291500064677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123207680 125829120 473169920 484966400 ⟨⟨273856873516, 273856873524⟩, ⟨260444688988, 287612604497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 117964800 484966400 496762880 ⟨⟨290711112622, 290711112634⟩, ⟨276761094288, 305009081965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 120586240 484966400 496762880 ⟨⟨286846612831, 286846612843⟩, ⟨273064220081, 300973607846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 117964800 496762880 508559360 ⟨⟨296210294883, 296210294894⟩, ⟨282222222455, 310539883154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 120586240 496762880 508559360 ⟨⟨292306591380, 292306591392⟩, ⟨278484197473, 306467445357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 484966400 496762880 ⟨⟨283034095875, 283034095886⟩, ⟨269416162137, 296993291186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 484966400 496762880 ⟨⟨279272000271, 279272000279⟩, ⟨265815455465, 293066476650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 123207680 496762880 508559360 ⟨⟨288454263229, 288454263240⟩, ⟨274794493550, 302449434898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 496762880 508559360 ⟨⟨284651782657, 284651782664⟩, ⟨271151674350, 298484235559⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 117964800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 123207680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 120586240) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 117964800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 496762880) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 123207680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
