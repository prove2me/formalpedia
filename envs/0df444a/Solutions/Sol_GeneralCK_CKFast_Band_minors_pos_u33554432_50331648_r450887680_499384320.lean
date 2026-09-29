-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r450887680_499384320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:54:31.649101+00:00
-- url     : https://prove2.me/submissions/6827c963-fef6-4239-803a-f5448d9a767e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [43/80, 381/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 450887680 463011840 ⟨⟨431656624755, 431656624772⟩, ⟨401970209944, 462226557469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 37748736 463011840 475136000 ⟨⟨438102269752, 438102269769⟩, ⟨408576888604, 468462889345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 41943040 450887680 463011840 ⟨⟨420499804957, 420499804973⟩, ⟨391664691590, 450223311130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 463011840 475136000 ⟨⟨426971174751, 426971174768⟩, ⟨398272027743, 456513561737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 37748736 475136000 487260160 ⟨⟨444472811994, 444472812013⟩, ⟨415104246925, 474630306373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 37748736 487260160 499384320 ⟨⟨450772403495, 450772403512⟩, ⟨421556548887, 480732716019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 41943040 475136000 487260160 ⟨⟨433367643862, 433367643878⟩, ⟨404801200135, 462733912948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 37748736 41943040 487260160 499384320 ⟨⟨439693261296, 439693261312⟩, ⟨411256317888, 468888241252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 46137344 450887680 463011840 ⟨⟨409848963019, 409848963035⟩, ⟨381810405002, 438776052883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 41943040 46137344 463011840 475136000 ⟨⟨416334491481, 416334491497⟩, ⟨388409242861, 445106064151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 46137344 50331648 450887680 463011840 ⟨⟨399654950876, 399654950892⟩, ⟨372365295535, 427829849242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 46137344 50331648 463011840 475136000 ⟨⟨406144450281, 406144450296⟩, ⟨378947577054, 434187129592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 46137344 475136000 487260160 ⟨⟨422745725919, 422745725935⟩, ⟨394931334369, 451365764214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 41943040 46137344 487260160 499384320 ⟨⟨429086593969, 429086593985⟩, ⟨401380626202, 457558966580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 50331648 475136000 487260160 ⟨⟨412560590988, 412560591004⟩, ⟨385454735642, 440474160232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 46137344 50331648 487260160 499384320 ⟨⟨418907166299, 418907166314⟩, ⟨391890551334, 446694667433⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 450887680 499384320 t = true :=
  ⟨_, (join_su (m := 41943040) (by decide) (join_sr (m := 475136000) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 463011840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 37748736) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 487260160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 475136000) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 463011840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 46137344) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 487260160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  have e3 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
