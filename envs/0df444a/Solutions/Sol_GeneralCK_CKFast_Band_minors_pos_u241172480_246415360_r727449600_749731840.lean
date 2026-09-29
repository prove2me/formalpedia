-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r727449600_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:07:13.468809+00:00
-- url     : https://prove2.me/submissions/50a74b77-cc32-413a-9a68-91f49194291d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [111/128, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 727449600 733020160 ⟨⟨211549349099, 211549349108⟩, ⟨206800741983, 216350482313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242483200 243793920 727449600 733020160 ⟨⟨209849540478, 209849540487⟩, ⟨205121910484, 214629575393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 242483200 733020160 738590720 ⟨⟨213053797046, 213053797055⟩, ⟨208291299073, 217868810967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 733020160 738590720 ⟨⟨211343590970, 211343590979⟩, ⟨206602086121, 216137494054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 727449600 733020160 ⟨⟨208153083461, 208153083470⟩, ⟨203446354544, 212912095150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 727449600 733020160 ⟨⟨206459941926, 206459941930⟩, ⟨201774038502, 211198005015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243793920 245104640 733020160 738590720 ⟨⟨209636717585, 209636717594⟩, ⟨204916130991, 214409583670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 246415360 733020160 738590720 ⟨⟨207933141042, 207933141046⟩, ⟨203233398283, 212685043539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 242483200 738590720 744161280 ⟨⟨214557362294, 214557362303⟩, ⟨209780975289, 219386253960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243793920 738590720 744161280 ⟨⟨212836777633, 212836777642⟩, ⟨208081399362, 217644546327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 744161280 749731840 ⟨⟨216060059507, 216060059515⟩, ⟨211269785144, 220902826091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243793920 744161280 749731840 ⟨⟨214329114785, 214329114794⟩, ⟨209559864388, 219150746665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 738590720 744161280 ⟨⟨211119506493, 211119506502⟩, ⟨206385063274, 215906224817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 738590720 744161280 ⟨⟨209405513303, 209405513306⟩, ⟨204691931882, 214171253446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243793920 245104640 744161280 749731840 ⟨⟨212601464170, 212601464179⟩, ⟨207853165242, 217402032706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 744161280 749731840 ⟨⟨210877072362, 210877072367⟩, ⟨206149652823, 215656648518⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 727449600 749731840 t = true :=
  ⟨_, (join_sr (m := 738590720) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 733020160) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242483200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 733020160) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245104640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243793920) (by decide) (join_sr (m := 744161280) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242483200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 744161280) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245104640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (111/128 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
