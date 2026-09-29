-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r402391040_450887680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:20:58.530116+00:00
-- url     : https://prove2.me/submissions/2dc4a4aa-653a-4ee1-ba8f-cbaf3b0c2da2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [307/640, 43/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 402391040 414515200 ⟨⟨363135835242, 363135835252⟩, ⟨336245699926, 391066036557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 54525952 414515200 426639360 ⟨⟨369950134565, 369950134575⟩, ⟨343138288107, 397759725692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 58720256 402391040 414515200 ⟨⟨353807221746, 353807221761⟩, ⟨327659389821, 380975897247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 414515200 426639360 ⟨⟨360600990579, 360600990594⟩, ⟨334512335998, 387671337870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 54525952 426639360 438763520 ⟨⟨376675268464, 376675268472⟩, ⟨349940787965, 404366671680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 54525952 438763520 450887680 ⟨⟨383315891546, 383315891550⟩, ⟨356657770638, 410891524061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 58720256 426639360 438763520 ⟨⟨367307774031, 367307774044⟩, ⟨341277949056, 394281437637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 54525952 58720256 438763520 450887680 ⟨⟨373932005889, 373932005904⟩, ⟨347960557934, 400810662146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 62914560 402391040 414515200 ⟨⟨344858346110, 344858346122⟩, ⟨319411941939, 371305756114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 62914560 414515200 426639360 ⟨⟨351623750329, 351623750344⟩, ⟨326219302460, 377992991051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 67108864 402391040 414515200 ⟨⟨336259008818, 336259008833⟩, ⟨311476986301, 362021882897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 62914560 67108864 414515200 426639360 ⟨⟨342989143132, 342989143146⟩, ⟨318233543919, 368692104199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 426639360 438763520 ⟨⟨358304524537, 358304524552⟩, ⟨332942159532, 384596588126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 58720256 62914560 438763520 450887680 ⟨⟨364904881772, 364904881787⟩, ⟨339584606307, 391120820177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 67108864 426639360 438763520 ⟨⟨349637132352, 349637132366⟩, ⟨324908471587, 375280627483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 62914560 67108864 438763520 450887680 ⟨⟨356206971328, 356206971339⟩, ⟨331505634295, 381791528210⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 402391040 450887680 t = true :=
  ⟨_, (join_su (m := 58720256) (by decide) (join_sr (m := 426639360) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 414515200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 54525952) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 438763520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 426639360) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 414515200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 62914560) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 438763520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  have e3 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
