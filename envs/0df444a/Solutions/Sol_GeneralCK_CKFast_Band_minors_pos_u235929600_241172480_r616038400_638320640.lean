-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r616038400_638320640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:48:25.440686+00:00
-- url     : https://prove2.me/submissions/01cf0efc-57e7-431c-8c3b-14ef78325b11

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [47/64, 487/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 616038400 621608960 ⟨⟨187238850484, 187238850492⟩, ⟨182685393414, 191845552653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237240320 238551040 616038400 621608960 ⟨⟨185736408548, 185736408556⟩, ⟨181203921859, 190321953260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 237240320 621608960 627179520 ⟨⟨188807391634, 188807391643⟩, ⟨184239888446, 193428138527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 621608960 627179520 ⟨⟨187294152352, 187294152361⟩, ⟨182747639901, 191893724770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239861760 616038400 621608960 ⟨⟨184237803209, 184237803215⟩, ⟨179726185112, 188802292338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239861760 241172480 616038400 621608960 ⟨⟨182742991487, 182742991496⟩, ⟨178252141045, 187286526073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 238551040 239861760 621608960 627179520 ⟨⟨185784736120, 185784736126⟩, ⟨181259113753, 190363234743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 241172480 621608960 627179520 ⟨⟨184279100218, 184279100226⟩, ⟨179774268114, 188836624910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 627179520 632750080 ⟨⟨190374635584, 190374635591⟩, ⟨185793093054, 195009419312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 238551040 627179520 632750080 ⟨⟨188850626694, 188850626701⟩, ⟨184290094743, 193464219462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 237240320 632750080 638320640 ⟨⟨191940599892, 191940599901⟩, ⟨187345024627, 196589412735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 238551040 632750080 638320640 ⟨⟨190405848712, 190405848720⟩, ⟨185831303354, 195033454637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 627179520 632750080 ⟨⟨187330426915, 187330426918⟩, ⟨182790806027, 191922928201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 627179520 632750080 ⟨⟨185813993787, 185813993794⟩, ⟨181295185268, 190385502277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 239861760 632750080 638320640 ⟨⟨188874892317, 188874892323⟩, ⟨184321278503, 193481389596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 632750080 638320640 ⟨⟨187347688515, 187347688524⟩, ⟨182814908677, 191933174644⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 616038400 638320640 t = true :=
  ⟨_, (join_sr (m := 627179520) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 621608960) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237240320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 621608960) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239861760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 238551040) (by decide) (join_sr (m := 632750080) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237240320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 632750080) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239861760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (487/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
