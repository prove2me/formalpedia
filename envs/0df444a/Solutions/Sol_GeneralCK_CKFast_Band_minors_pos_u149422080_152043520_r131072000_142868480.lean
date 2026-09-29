-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:31:05.834691+00:00
-- url     : https://prove2.me/submissions/80b07164-56cb-4032-9f4d-cef9bef3b22f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 131072000 134021120 ⟨⟨76575683223, 76575683230⟩, ⟨74078210981, 79098342735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 150077440 150732800 131072000 134021120 ⟨⟨76241609522, 76241609530⟩, ⟨73753221791, 78755027695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 150077440 134021120 136970240 ⟨⟨78161944539, 78161944546⟩, ⟨75658402881, 80690630579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 134021120 136970240 ⟨⟨77821828929, 77821828936⟩, ⟨75327385787, 80341260633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 150732800 151388160 131072000 134021120 ⟨⟨75909308849, 75909308857⟩, ⟨73429940422, 78413552430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 151388160 152043520 131072000 134021120 ⟨⟨75578763364, 75578763370⟩, ⟨73108349770, 78073898353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150732800 151388160 134021120 136970240 ⟨⟨77483508688, 77483508696⟩, ⟨74998098947, 79993752703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 151388160 152043520 134021120 136970240 ⟨⟨77146965827, 77146965833⟩, ⟨74670525096, 79648088049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150077440 136970240 139919360 ⟨⟨79743775524, 79743775530⟩, ⟨77234204572, 82278447772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150077440 150732800 136970240 139919360 ⟨⟨79397667134, 79397667140⟩, ⟨76897208141, 81923072616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 149422080 150077440 139919360 142868480 ⟨⟨81321214289, 81321214297⟩, ⟨78805653683, 83861832912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150077440 150732800 139919360 142868480 ⟨⟨80969161648, 80969161656⟩, ⟨78462725888, 83500501630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 151388160 136970240 139919360 ⟨⟨79053375915, 79053375922⟩, ⟨76561963857, 81569581166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 151388160 152043520 136970240 139919360 ⟨⟨78710883730, 78710883736⟩, ⟨76228454307, 81217954541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 151388160 139919360 142868480 ⟨⟨80618947447, 80618947455⟩, ⟨78121571608, 83141075206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 151388160 152043520 139919360 142868480 ⟨⟨80270553409, 80270553417⟩, ⟨77782173289, 82783534620⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 150077440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 151388160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 150732800) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 150077440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 151388160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
