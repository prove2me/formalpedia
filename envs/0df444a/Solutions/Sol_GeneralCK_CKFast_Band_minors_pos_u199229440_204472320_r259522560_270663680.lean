-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:36.132514+00:00
-- url     : https://prove2.me/submissions/01240410-d3e9-4bd9-a783-a4941adc2735

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 259522560 262307840 ⟨⟨104841372489, 104841372491⟩, ⟨101308398652, 108417830011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 200540160 262307840 265093120 ⟨⟨105887535385, 105887535389⟩, ⟨102346889705, 109471674965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 200540160 201850880 259522560 262307840 ⟨⟨103994858327, 103994858333⟩, ⟨100478900292, 107554000169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 262307840 265093120 ⟨⟨105033643994, 105033644001⟩, ⟨101510037851, 108600445550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 200540160 265093120 267878400 ⟨⟨106932428328, 106932428332⟩, ⟨103384122253, 110524238189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 200540160 267878400 270663680 ⟨⟨107976058692, 107976058695⟩, ⟨104420103595, 111575527132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201850880 265093120 267878400 ⟨⟨106071186750, 106071186758⟩, ⟨102539943555, 109645636639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 200540160 201850880 267878400 270663680 ⟨⟨107107493765, 107107493771⟩, ⟨103568624505, 110689580678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 203161600 259522560 262307840 ⟨⟨103153445967, 103153445975⟩, ⟨99654331930, 106695447740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 203161600 262307840 265093120 ⟨⟨104184875583, 104184875590⟩, ⟨100678137492, 107734514367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 204472320 259522560 262307840 ⟨⟨102317061282, 102317061290⟩, ⟨98834622067, 105842095904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203161600 204472320 262307840 265093120 ⟨⟨103341155900, 103341155908⟩, ⟨99851116992, 106873804489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 265093120 267878400 ⟨⟨105215088853, 105215088859⟩, ⟨101700737381, 108772353657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201850880 203161600 267878400 270663680 ⟨⟨106244092749, 106244092756⟩, ⟨102722138503, 109808972649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 204472320 265093120 267878400 ⟨⟨104364060269, 104364060276⟩, ⟨100866431965, 107904312214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 267878400 270663680 ⟨⟨105385781168, 105385781174⟩, ⟨101880573701, 108933625926⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 259522560 270663680 t = true :=
  ⟨_, (join_su (m := 201850880) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262307840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 200540160) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 267878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 265093120) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262307840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203161600) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 267878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
