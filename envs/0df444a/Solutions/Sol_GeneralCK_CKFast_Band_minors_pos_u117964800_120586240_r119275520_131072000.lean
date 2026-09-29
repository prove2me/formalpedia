-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u117964800_120586240_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:40.306005+00:00
-- url     : https://prove2.me/submissions/e817ca14-8241-40b7-ae4b-79f36888cfd0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/64, 23/160]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 117964800 118620160 119275520 122224640 ⟨⟨87417061615, 87417061625⟩, ⟨84416124098, 90453536638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 118620160 119275520 119275520 122224640 ⟨⟨87001131711, 87001131718⟩, ⟨84013523039, 90024003167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 118620160 122224640 125173760 ⟨⟨89354040052, 89354040060⟩, ⟨86346237135, 92397259006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 118620160 119275520 122224640 125173760 ⟨⟨88930441969, 88930441976⟩, ⟨85935975457, 91960052319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 119275520 119930880 119275520 122224640 ⟨⟨86588081111, 86588081114⟩, ⟨83613681167, 89597472471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119930880 120586240 119275520 122224640 ⟨⟨86177874545, 86177874552⟩, ⟨83216564879, 89173907562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 119275520 119930880 122224640 125173760 ⟨⟨88509758255, 88509758257⟩, ⟨85528508404, 91525883042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119930880 120586240 122224640 125173760 ⟨⟨88091953384, 88091953391⟩, ⟨85123802111, 91094713949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 118620160 125173760 128122880 ⟨⟨91283086273, 91283086283⟩, ⟨88268501153, 94332965970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 118620160 119275520 125173760 128122880 ⟨⟨90851911263, 90851911270⟩, ⟨87850668955, 93888178452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 117964800 118620160 128122880 131072000 ⟨⟨93204288581, 93204288590⟩, ⟨90183003018, 96260747272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 118620160 119275520 128122880 131072000 ⟨⟨92765626390, 92765626398⟩, ⟨89757688932, 95808469779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 119275520 119930880 125173760 128122880 ⟨⟨90423684554, 90423684558⟩, ⟨87435665711, 93446461838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119930880 120586240 125173760 128122880 ⟨⟨89998370391, 89998370400⟩, ⟨87023457308, 93007778680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 119930880 128122880 131072000 ⟨⟨92329945341, 92329945346⟩, ⟨89335237044, 95359295572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119930880 120586240 128122880 131072000 ⟨⟨91897209456, 91897209464⟩, ⟨88915613010, 94913186997⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 117964800 120586240 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 118620160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119930880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 119275520) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 118620160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 119930880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/64 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
