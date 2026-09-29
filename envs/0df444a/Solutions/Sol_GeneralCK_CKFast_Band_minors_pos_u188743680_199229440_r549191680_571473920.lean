-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r549191680_571473920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:40.63577+00:00
-- url     : https://prove2.me/submissions/534a9576-9aa5-48e3-b144-3a0bc1edc49e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [419/640, 109/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 549191680 554762240 ⟨⟨219947908352, 219947908359⟩, ⟨211147389572, 228923799774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 554762240 560332800 ⟨⟨221922143144, 221922143150⟩, ⟨213094568126, 230924795702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 549191680 554762240 ⟨⟨216862366054, 216862366063⟩, ⟨208136282365, 225762739252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 554762240 560332800 ⟨⟨218815227235, 218815227244⟩, ⟨210062018125, 227742462166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 560332800 565903360 ⟨⟨223893342657, 223893342663⟩, ⟨215038764962, 232922697555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 565903360 571473920 ⟨⟨225861549080, 225861549086⟩, ⟨216980021410, 234917548377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 560332800 565903360 ⟨⟨220765157927, 220765157935⟩, ⟨211984874118, 229719198681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 565903360 571473920 ⟨⟨222712198559, 222712198569⟩, ⟨213904889960, 231692990035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 549191680 554762240 ⟨⟨213800516434, 213800516444⟩, ⟨205147900640, 222626343184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 554762240 560332800 ⟨⟨215731923810, 215731923820⟩, ⟨207052125816, 224584699494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 549191680 554762240 ⟨⟨210761807788, 210761807796⟩, ⟨202181713694, 219514039133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 554762240 560332800 ⟨⟨212671685022, 212671685031⟩, ⟨204064363916, 221450939571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 560332800 565903360 ⟨⟨217660503094, 217660503103⟩, ⟨208953570805, 226540174674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 565903360 571473920 ⟨⟨219586293015, 219586293024⟩, ⟨210852273572, 228492808212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 560332800 565903360 ⟨⟨214578834184, 214578834193⟩, ⟨205944331188, 223385061745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 565903360 571473920 ⟨⟨216483292361, 216483292370⟩, ⟨207821651875, 225316443461⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 549191680 571473920 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 560332800) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 554762240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 565903360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 560332800) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 554762240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 196608000) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 565903360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (419/640 : ℝ) (109/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  have e3 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
