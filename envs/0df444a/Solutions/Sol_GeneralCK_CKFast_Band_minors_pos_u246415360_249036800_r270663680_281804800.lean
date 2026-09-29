-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:24:15.530772+00:00
-- url     : https://prove2.me/submissions/90710a96-578e-4ea9-922f-f27e3dfacfe0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 270663680 273448960 ⟨⟨80468571646, 80468571653⟩, ⟨78702811506, 82246482291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247070720 247726080 270663680 273448960 ⟨⟨80103473766, 80103473770⟩, ⟨78342061167, 81876995478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247070720 273448960 276234240 ⟨⟨81261017302, 81261017307⟩, ⟨79491675048, 83042519692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 273448960 276234240 ⟨⟨80892592500, 80892592502⟩, ⟨79127606376, 82669697477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248381440 270663680 273448960 ⟨⟨79739166553, 79739166560⟩, ⟨77982084321, 81508316734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248381440 249036800 270663680 273448960 ⟨⟨79375644596, 79375644602⟩, ⟨77622875662, 81140440528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 248381440 273448960 276234240 ⟨⟨80524962148, 80524962154⟩, ⟨78764314990, 82297687100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248381440 249036800 273448960 276234240 ⟨⟨80158120818, 80158120824⟩, ⟨78401795568, 81926483015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247070720 276234240 279019520 ⟨⟨82052920541, 82052920548⟩, ⟨80279997636, 83838013167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247070720 247726080 276234240 279019520 ⟨⟨81681175661, 81681175665⟩, ⟨79912617420, 83461862448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247070720 279019520 281804800 ⟨⟨82844283937, 82844283944⟩, ⟨81067781834, 84632965294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247070720 247726080 279019520 281804800 ⟨⟨82469225781, 82469225786⟩, ⟨80697096823, 84253492929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 276234240 279019520 ⟨⟨81310228947, 81310228954⟩, ⟨79546018217, 83086527270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 249036800 276234240 279019520 ⟨⟨80940074955, 80940074961⟩, ⟨79180194691, 82712002072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247726080 248381440 279019520 281804800 ⟨⟨82094969444, 82094969450⟩, ⟨80327196488, 83874839744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 279019520 281804800 ⟨⟨81721509464, 81721509470⟩, ⟨79958075476, 83497000160⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247070720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248381440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247726080) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247070720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248381440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
