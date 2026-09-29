-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:39:59.518793+00:00
-- url     : https://prove2.me/submissions/0d736bbe-27cc-4381-835a-0e80a9c3091a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 1/20]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 37748736 38797312 99287040 102318080 ⟨⟨160356903823, 160356903838⟩, ⟨151369142566, 169623304275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 38797312 102318080 105349120 ⟨⟨163911437867, 163911437882⟩, ⟨154933046610, 173163909378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 38797312 39845888 99287040 102318080 ⟨⟨158071972162, 158071972169⟩, ⟨149239721051, 167174741603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38797312 39845888 102318080 105349120 ⟨⟨161601005942, 161601005946⟩, ⟨152776588133, 170691627248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 38797312 105349120 108380160 ⟨⟨167418569101, 167418569120⟩, ⟨158450163355, 176656592859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 37748736 38797312 108380160 111411200 ⟨⟨170879695051, 170879695066⟩, ⟨161921845241, 180102794982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 38797312 39845888 105349120 108380160 ⟨⟨165083808269, 165083808277⟩, ⟨156267842037, 174161751879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 38797312 39845888 108380160 111411200 ⟨⟨168521719682, 168521719689⟩, ⟨159714779851, 177586497421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 39845888 40894464 99287040 102318080 ⟨⟨155852142693, 155852142711⟩, ⟨147169814238, 164797237095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 39845888 40894464 102318080 105349120 ⟨⟨159355631776, 159355631791⟩, ⟨150679710400, 168290232286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 40894464 41943040 99287040 102318080 ⟨⟨153694447533, 153694447551⟩, ⟨145156750783, 162487504060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 40894464 41943040 102318080 105349120 ⟨⟨157172379553, 157172379567⟩, ⟨148639765481, 165956479800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 40894464 105349120 108380160 ⟨⟨162814028745, 162814028760⟩, ⟨154145133462, 171737597794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 40894464 108380160 111411200 ⟨⟨166228619813, 166228619828⟩, ⟨157567327802, 175140659866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 40894464 41943040 105349120 108380160 ⟨⟨160606327415, 160606327429⟩, ⟨152079414029, 169380928203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 40894464 41943040 108380160 111411200 ⟨⟨163997525540, 163997525555⟩, ⟨155476890588, 172762122372⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 41943040 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 39845888) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 38797312) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 38797312) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 40894464) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 40894464) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
