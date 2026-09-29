-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r259522560_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:28:24.694848+00:00
-- url     : https://prove2.me/submissions/de0ed9a5-8b3c-47d5-a238-514afc31f383

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [99/320, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 259522560 265093120 ⟨⟨127522015615, 127522015623⟩, ⟨122665625580, 132456026323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 259522560 265093120 ⟨⟨126522909931, 126522909940⟩, ⟨121696690039, 131426053409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 169082880 265093120 270663680 ⟨⟨129977531330, 129977531337⟩, ⟨125103556482, 134928939673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 265093120 270663680 ⟨⟨128962678805, 128962678812⟩, ⟨124118894174, 133883208764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171704320 259522560 265093120 ⟨⟨125531175991, 125531175998⟩, ⟨120734790983, 130403797273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 171704320 173015040 259522560 265093120 ⟨⟨124546697246, 124546697255⟩, ⟨119779817654, 129389135397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 171704320 265093120 270663680 ⟨⟨127955242819, 127955242826⟩, ⟨123141315312, 132845237020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 173015040 265093120 270663680 ⟨⟨126955106807, 126955106814⟩, ⟨122170709043, 131814901990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 169082880 270663680 276234240 ⟨⟨132424797851, 132424797858⟩, ⟨127533357170, 137393483063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 169082880 170393600 270663680 276234240 ⟨⟨131394360502, 131394360509⟩, ⟨126533127181, 136332159099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 169082880 276234240 281804800 ⟨⟨134863927393, 134863927401⟩, ⟨129955137784, 139849770812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 169082880 170393600 276234240 281804800 ⟨⟨133818064260, 133818064269⟩, ⟨128939496297, 138773015678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 270663680 276234240 ⟨⟨130371381749, 130371381757⟩, ⟨125540024909, 135278633904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 173015040 270663680 276234240 ⟨⟨129355745057, 129355745066⟩, ⟨124553939452, 134232785142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 170393600 171704320 276234240 281804800 ⟨⟨132779699123, 132779699132⟩, ⟨127931024184, 137704096218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 276234240 281804800 ⟨⟨131748715514, 131748715523⟩, ⟨126929610528, 136642890248⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 259522560 281804800 t = true :=
  ⟨_, (join_sr (m := 270663680) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 169082880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 265093120) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 171704320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 170393600) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 169082880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 276234240) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 171704320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
