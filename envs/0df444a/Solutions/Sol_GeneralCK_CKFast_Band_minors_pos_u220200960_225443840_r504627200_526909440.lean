-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:42:52.404985+00:00
-- url     : https://prove2.me/submissions/197fbaa9-00d6-40f3-b281-5373f250ff4c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 504627200 510197760 ⟨⟨171258715468, 171258715475⟩, ⟨166732480458, 175841101101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221511680 222822400 504627200 510197760 ⟨⟨169926661862, 169926661870⟩, ⟨165422448048, 174486760176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 510197760 515768320 ⟨⟨172993995036, 172993995044⟩, ⟨168453240119, 177590879581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 510197760 515768320 ⟨⟨171650559581, 171650559589⟩, ⟨167131844622, 176225141851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 504627200 510197760 ⟨⟨168599235629, 168599235637⟩, ⟨164116904048, 173137186941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224133120 225443840 504627200 510197760 ⟨⟨167276382137, 167276382144⟩, ⟨162815795276, 171792325307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 224133120 510197760 515768320 ⟨⟨170311744866, 170311744874⟩, ⟨165814932142, 174864163866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 225443840 510197760 515768320 ⟨⟨168977496516, 168977496525⟩, ⟨164502449724, 173507889826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 221511680 515768320 521338880 ⟨⟨174727117644, 174727117652⟩, ⟨170171861727, 179338480953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222822400 515768320 521338880 ⟨⟨173372344454, 173372344461⟩, ⟨168839146489, 177961391317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 221511680 521338880 526909440 ⟨⟨176458109604, 176458109611⟩, ⟨171888371307, 181083931814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221511680 222822400 521338880 526909440 ⟨⟨175092042159, 175092042168⟩, ⟨170544379050, 179695534531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 515768320 521338880 ⟨⟨172022184740, 172022184747⟩, ⟨167510908250, 176589052843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 225443840 515768320 521338880 ⟨⟨170676584394, 170676584402⟩, ⟨166187094298, 175221410022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222822400 224133120 521338880 526909440 ⟨⟨173730580312, 173730580320⟩, ⟨169204857167, 178311879199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 521338880 526909440 ⟨⟨172373670224, 172373670233⟩, ⟨167869753190, 176932910609⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 504627200 526909440 t = true :=
  ⟨_, (join_sr (m := 515768320) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 510197760) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221511680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 510197760) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224133120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222822400) (by decide) (join_sr (m := 521338880) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221511680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 521338880) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224133120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
