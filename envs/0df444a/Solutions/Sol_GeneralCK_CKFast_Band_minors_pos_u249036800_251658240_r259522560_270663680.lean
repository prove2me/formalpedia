-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:52:09.188274+00:00
-- url     : https://prove2.me/submissions/beca42c4-b7aa-4eeb-8473-7c793174f9ad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 259522560 262307840 ⟨⟨75891057126, 75891057131⟩, ⟨74156787952, 77637271891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249692160 250347520 259522560 262307840 ⟨⟨75542403686, 75542403693⟩, ⟨73812378963, 77284333085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249692160 262307840 265093120 ⟨⟨76672303803, 76672303809⟩, ⟨74934481863, 78422081572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 262307840 265093120 ⟨⟨76320311777, 76320311784⟩, ⟨74586743128, 78065795437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 251002880 259522560 262307840 ⟨⟨75194503954, 75194503955⟩, ⟨73468706910, 76932164969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251002880 251658240 259522560 262307840 ⟨⟨74847352720, 74847352727⟩, ⟨73125766705, 76580762232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 262307840 265093120 ⟨⟨75969077438, 75969077441⟩, ⟨74239745318, 77710283963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251658240 262307840 265093120 ⟨⟨75618595560, 75618595566⟩, ⟨73893483323, 77355541821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249692160 265093120 267878400 ⟨⟨77453025296, 77453025301⟩, ⟨75711651868, 79206364741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250347520 265093120 267878400 ⟨⟨77097701414, 77097701421⟩, ⟨75360590067, 78846738062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249692160 267878400 270663680 ⟨⟨78233224051, 78233224058⟩, ⟨76488300411, 79990123858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249692160 250347520 267878400 270663680 ⟨⟨77874575008, 77874575015⟩, ⟨76133922182, 79627163380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 265093120 267878400 ⟨⟨76743139132, 76743139135⟩, ⟨75010273110, 78487889947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 265093120 267878400 ⟨⟨76389333208, 76389333214⟩, ⟨74660695873, 78129815052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251002880 267878400 270663680 ⟨⟨77516691411, 77516691414⟩, ⟨75780292656, 79264985304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 267878400 270663680 ⟨⟨77159568001, 77159568008⟩, ⟨75427406684, 78903584270⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249692160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251002880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 250347520) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249692160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251002880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
