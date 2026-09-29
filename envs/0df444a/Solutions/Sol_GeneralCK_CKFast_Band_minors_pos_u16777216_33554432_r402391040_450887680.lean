-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r402391040_450887680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:32:46.768642+00:00
-- url     : https://prove2.me/submissions/85075ca3-52cc-42d1-a076-70b992ce3f10

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [307/640, 43/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 402391040 414515200 ⟨⟨457238304299, 457238304319⟩, ⟨422055480455, 493460811875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 20971520 414515200 426639360 ⟨⟨463754096321, 463754096340⟩, ⟨428911041537, 499558296788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 20971520 25165824 402391040 414515200 ⟨⟨442890777416, 442890777434⟩, ⟨409099909832, 477763951741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 414515200 426639360 ⟨⟨449510062619, 449510062637⟩, ⟨416010739296, 484018912691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 20971520 426639360 438763520 ⟨⟨470179897104, 470179897123⟩, ⟨435664222251, 505582699120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 20971520 438763520 450887680 ⟨⟨476521401483, 476521401499⟩, ⟨442321347167, 511538699908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 25165824 426639360 438763520 ⟨⟨456036538220, 456036538239⟩, ⟨422818874943, 490194899623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 20971520 25165824 438763520 450887680 ⟨⟨462475944101, 462475944117⟩, ⟨429530502790, 496296885289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 29360128 402391040 414515200 ⟨⟨429493719635, 429493719654⟩, ⟨396947911767, 463139886563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 25165824 29360128 414515200 426639360 ⟨⟨436191261126, 436191261141⟩, ⟨403894781453, 469520706560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 29360128 33554432 402391040 414515200 ⟨⟨416908348612, 416908348630⟩, ⟨385494022762, 449426927073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 29360128 33554432 414515200 426639360 ⟨⟨423662952319, 423662952336⟩, ⟨392460697829, 455907075991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 426639360 438763520 ⟨⟨442794416120, 442794416138⟩, ⟨410739452757, 475818404323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 25165824 29360128 438763520 450887680 ⟨⟨449308884753, 449308884772⟩, ⟨417487928790, 482038108868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 29360128 33554432 426639360 438763520 ⟨⟨430322568710, 430322568727⟩, ⟨399326296822, 462301340295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 438763520 450887680 ⟨⟨436892796916, 436892796934⟩, ⟨406096610139, 468614904061⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 402391040 450887680 t = true :=
  ⟨_, (join_su (m := 25165824) (by decide) (join_sr (m := 426639360) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 414515200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 20971520) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 438763520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 426639360) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 414515200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 29360128) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 438763520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  have e3 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
