-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:20:49.42973+00:00
-- url     : https://prove2.me/submissions/ac4cabe7-e1ee-42fa-bd8f-3e432a665989

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 131072000 134021120 ⟨⟨104475155071, 104475155082⟩, ⟨99310384196, 109740139202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 106168320 134021120 136970240 ⟨⟨106529927496, 106529927506⟩, ⟨101353416404, 111806280205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 106168320 107479040 131072000 134021120 ⟨⟨103453033702, 103453033712⟩, ⟨98334666746, 108670063280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 134021120 136970240 ⟨⟨105491942462, 105491942470⟩, ⟨100361825599, 110720366385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 106168320 136970240 139919360 ⟨⟨108575221655, 108575221663⟩, ⟨103387123180, 113862790172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 106168320 139919360 142868480 ⟨⟨110611153614, 110611153623⟩, ⟨105411617708, 115909788097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 107479040 136970240 139919360 ⟨⟨107521588535, 107521588543⟩, ⟨102379870623, 112761257924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106168320 107479040 139919360 142868480 ⟨⟨109542084049, 109542084059⟩, ⟨104388911181, 114792852829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108789760 131072000 134021120 ⟨⟨102446130614, 102446130620⟩, ⟨97373252439, 107616160562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 108789760 134021120 136970240 ⟨⟨104469312522, 104469312528⟩, ⟨99384678861, 109650757805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 108789760 110100480 131072000 134021120 ⟨⟨101454052841, 101454052851⟩, ⟨96425775324, 106578009697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 110100480 134021120 136970240 ⟨⟨103461643259, 103461643267⟩, ⟨98421608536, 108597031941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 136970240 139919360 ⟨⟨106483442028, 106483442030⟩, ⟨101387197848, 111676157571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 107479040 108789760 139919360 142868480 ⟨⟨108488627461, 108488627468⟩, ⟨103380915087, 113692470878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 110100480 136970240 139919360 ⟨⟨105460386402, 105460386410⟩, ⟨100408735649, 110607065557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 139919360 142868480 ⟨⟨107450386958, 107450386968⟩, ⟨102387258807, 112608217808⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 107479040) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 106168320) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 134021120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 108789760) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
