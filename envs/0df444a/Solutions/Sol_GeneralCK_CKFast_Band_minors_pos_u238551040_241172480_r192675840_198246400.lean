-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r192675840_198246400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:52:03.209146+00:00
-- url     : https://prove2.me/submissions/ad50daf5-74ab-4fd8-b69b-b8f96bf395ad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [147/640, 121/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 192675840 194068480 ⟨⟨61117067060, 61117067066⟩, ⟨59650893060, 62591983323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 194068480 195461120 ⟨⟨61543050578, 61543050584⟩, ⟨60075138916, 63019709908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 192675840 194068480 ⟨⟨60840719553, 60840719560⟩, ⟨59377585082, 62312568326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 194068480 195461120 ⟨⟨61264896692, 61264896698⟩, ⟨59800028869, 62738484252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 195461120 196853760 ⟨⟨61968853192, 61968853199⟩, ⟨60499204259, 63447255188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238551040 239206400 196853760 198246400 ⟨⟨62394475334, 62394475341⟩, ⟨60923089516, 63874619598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239861760 195461120 196853760 ⟨⟨61688895204, 61688895209⟩, ⟨60222294403, 63164221167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239206400 239861760 196853760 198246400 ⟨⟨62112715512, 62112715519⟩, ⟨60644382108, 63589779494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240517120 192675840 194068480 ⟨⟨60565085750, 60565085755⟩, ⟨59104976585, 62033881427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239861760 240517120 194068480 195461120 ⟨⟨60987459669, 60987459675⟩, ⟨59525621459, 62457989859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 240517120 241172480 192675840 194068480 ⟨⟨60290160471, 60290160474⟩, ⟨58833062490, 61755917348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 241172480 194068480 195461120 ⟨⟨60710734315, 60710734316⟩, ⟨59251911592, 62178221430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 195461120 196853760 ⟨⟨61409657215, 61409657221⟩, ⟨59946090320, 62881921547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 240517120 196853760 198246400 ⟨⟨61831678805, 61831678812⟩, ⟨60366383584, 63305676911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 241172480 195461120 196853760 ⟨⟨61131134016, 61131134018⟩, ⟨59670586897, 62600351015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 196853760 198246400 ⟨⟨61551359986, 61551359989⟩, ⟨60089088815, 63022306514⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 192675840 198246400 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 194068480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 196853760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195461120) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 194068480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 240517120) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 196853760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (121/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
