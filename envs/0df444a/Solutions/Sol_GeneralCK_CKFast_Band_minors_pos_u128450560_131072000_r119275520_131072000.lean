-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u128450560_131072000_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:07:17.52025+00:00
-- url     : https://prove2.me/submissions/7225cd46-4206-40a3-a7fa-e343d88b8a8f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [49/320, 5/32]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 128450560 129105920 119275520 122224640 ⟨⟨81088954963, 81088954970⟩, ⟨78287745120, 83921680089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 129105920 129761280 119275520 122224640 ⟨⟨80715165808, 80715165812⟩, ⟨77925546921, 83536072841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 129105920 122224640 125173760 ⟨⟨82907311269, 82907311276⟩, ⟨80099395930, 85746655276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 129105920 129761280 122224640 125173760 ⟨⟨82526385436, 82526385438⟩, ⟨79730073351, 85353900884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 129761280 130416640 119275520 122224640 ⟨⟨80343754990, 80343754997⟩, ⟨77565630291, 83152943294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 130416640 131072000 119275520 122224640 ⟨⟨79974695225, 79974695232⟩, ⟨77207969190, 82772262867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 129761280 130416640 122224640 125173760 ⟨⟨82147869132, 82147869139⟩, ⟨79363063754, 84963655133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 130416640 131072000 122224640 125173760 ⟨⟨81771734845, 81771734852⟩, ⟨78998340860, 84575889224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 128450560 129105920 125173760 128122880 ⟨⟨84719068879, 84719068888⟩, ⟨81904514568, 87564965112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 129105920 129761280 125173760 128122880 ⟨⟨84331081409, 84331081413⟩, ⟨81528141722, 87165139543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 128450560 129105920 128122880 131072000 ⟨⟨86524295141, 86524295148⟩, ⟨83703167361, 89376677966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 129105920 129761280 128122880 131072000 ⟨⟨86129319957, 86129319960⟩, ⟨83319817268, 88969856046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 129761280 130416640 125173760 128122880 ⟨⟨83945533765, 83945533772⟩, ⟨81154112386, 86767852646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 130416640 131072000 125173760 128122880 ⟨⟨83562398218, 83562398227⟩, ⟨80782400056, 86373075414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 129761280 130416640 128122880 131072000 ⟨⟨85736814021, 85736814030⟩, ⟨82938840345, 88565601943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 130416640 131072000 128122880 131072000 ⟨⟨85346749400, 85346749407⟩, ⟨82560209880, 88163886452⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 128450560 131072000 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 129761280) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 129105920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 130416640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 129761280) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 129105920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 130416640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (49/320 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
