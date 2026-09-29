-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:25:36.453181+00:00
-- url     : https://prove2.me/submissions/71130bc7-6b09-4caa-ae09-912d8d2a83a5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 270663680 273448960 ⟨⟨79012902513, 79012902520⟩, ⟨77264429921, 80773361369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249692160 250347520 270663680 273448960 ⟨⟨78650934963, 78650934969⟩, ⟨76906741870, 80407073801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249692160 273448960 276234240 ⟨⟨79792063112, 79792063118⟩, ⟨78040042826, 81556079715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 273448960 276234240 ⟨⟨79426783673, 79426783679⟩, ⟨77679051516, 81186471729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 251002880 270663680 273448960 ⟨⟨78289736640, 78289736643⟩, ⟨76549806309, 80041572408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251002880 251658240 270663680 273448960 ⟨⟨77929302272, 77929302278⟩, ⟨76193618079, 79676851811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 273448960 276234240 ⟨⟨79062277180, 79062277181⟩, ⟨77318816425, 80817653625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251658240 273448960 276234240 ⟨⟨78698538341, 78698538346⟩, ⟨76959332375, 80449620007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249692160 276234240 279019520 ⟨⟨80570708273, 80570708279⟩, ⟨78815141540, 82338281330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250347520 276234240 279019520 ⟨⟨80202123526, 80202123532⟩, ⟨78450853500, 81965359560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249692160 279019520 281804800 ⟨⟨81348840413, 81348840419⟩, ⟨79589728472, 83119968638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249692160 250347520 279019520 281804800 ⟨⟨80976956902, 80976956909⟩, ⟨79222150196, 82743739681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 276234240 279019520 ⟨⟨79834315378, 79834315381⟩, ⟨78087325344, 81593231314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 276234240 279019520 ⟨⟨79467278521, 79467278528⟩, ⟨77724551875, 81221891178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251002880 279019520 281804800 ⟨⟨80605853579, 80605853582⟩, ⟨78855335403, 82368307823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 279019520 281804800 ⟨⟨80235525124, 80235525131⟩, ⟨78489278882, 81993667640⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249692160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251002880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 250347520) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249692160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251002880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
