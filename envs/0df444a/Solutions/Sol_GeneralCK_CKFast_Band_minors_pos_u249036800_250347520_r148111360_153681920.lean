-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:54.237475+00:00
-- url     : https://prove2.me/submissions/28c66c16-85ab-41cd-a5ba-70dc0739047a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 148111360 149504000 ⟨⟨44032320593, 44032320600⟩, ⟨43235349135, 44832168977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 148111360 149504000 ⟨⟨43928075565, 43928075571⟩, ⟨43132069279, 44726953218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 149504000 150896640 ⟨⟨44435115639, 44435115645⟩, ⟨43637239803, 45235869901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 149504000 150896640 ⟨⟨44329958412, 44329958418⟩, ⟨43533049151, 45129740546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 148111360 149504000 ⟨⟨43823964304, 43823964306⟩, ⟨43028921120, 44621873310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 148111360 149504000 ⟨⟨43719986309, 43719986314⟩, ⟨42925904162, 44516928754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250019840 149504000 150896640 ⟨⟨44224935851, 44224935853⟩, ⟨43428991090, 45023747940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250019840 250347520 149504000 150896640 ⟨⟨44120047447, 44120047452⟩, ⟨43325065125, 44917891582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249364480 150896640 152289280 ⟨⟨44837752027, 44837752032⟩, ⟨44038972021, 45639411958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249364480 249692160 150896640 152289280 ⟨⟨44731683663, 44731683669⟩, ⟨43933871629, 45532370072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249364480 152289280 153681920 ⟨⟨45240230113, 45240230118⟩, ⟨44440546143, 46042795502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249364480 249692160 152289280 153681920 ⟨⟨45133251670, 45133251675⟩, ⟨44334537065, 45934842148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 150896640 152289280 ⟨⟨44625750854, 44625750857⟩, ⟨43828904719, 45425465828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250019840 250347520 150896640 152289280 ⟨⟨44519953092, 44519953099⟩, ⟨43724070789, 45318698721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249692160 250019840 152289280 153681920 ⟨⟨45026409667, 45026409668⟩, ⟨44228662352, 45827027322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 152289280 153681920 ⟨⟨44919703593, 44919703598⟩, ⟨44122921502, 45719350517⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250019840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249692160) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249364480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250019840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
