-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_136314880_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:23.419926+00:00
-- url     : https://prove2.me/submissions/fcbd9fe7-081b-433a-babe-d3fd4f3d704d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 13/80]`, `ρ ∈ [77/320, 43/160]` by 17 cells of the computing
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
theorem cell0 : cellOK 131072000 132382720 201850880 207749120 ⟨⟨128083952647, 128083952656⟩, ⟨122276676923, 134004154076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 132382720 133693440 201850880 207749120 ⟨⟨127010623634, 127010623643⟩, ⟨121247876939, 132884943586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 132382720 207749120 213647360 ⟨⟨131338850374, 131338850381⟩, ⟨125510777143, 137279202358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 132382720 133693440 207749120 213647360 ⟨⟨130244358793, 130244358802⟩, ⟨124460776829, 136138891194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 133693440 135004160 201850880 207749120 ⟨⟨125948555879, 125948555881⟩, ⟨120229690304, 131777667567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135004160 136314880 201850880 204800000 ⟨⟨124096790620, 124096790628⟩, ⟨119558161164, 128704805542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 135004160 136314880 204800000 207749120 ⟨⟨125697133352, 125697133360⟩, ⟨121148944520, 130314566046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 135004160 207749120 213647360 ⟨⟨129161223110, 129161223114⟩, ⟨123421490409, 135010602455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 135004160 136314880 207749120 213647360 ⟨⟨128089221037, 128089221047⟩, ⟨122392709781, 133894099073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131072000 132382720 213647360 219545600 ⟨⟨134574885213, 134574885223⟩, ⟨128726341724, 140535060327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 132382720 133693440 213647360 219545600 ⟨⟨133459605581, 133459605591⟩, ⟨127655508339, 139374030057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 131072000 132382720 219545600 225443840 ⟨⟨137792404451, 137792404461⟩, ⟨131923709073, 143772084239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133693440 219545600 225443840 ⟨⟨136656701384, 136656701392⟩, ⟨130832400294, 142590706213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 135004160 213647360 219545600 ⟨⟨132355769393, 132355769399⟩, ⟨126595482412, 138225102976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 135004160 136314880 213647360 219545600 ⟨⟨131263154443, 131263154452⟩, ⟨125546055665, 137088042380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 135004160 219545600 225443840 ⟨⟨135532522506, 135532522512⟩, ⟨129751985834, 141421505259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 135004160 136314880 219545600 225443840 ⟨⟨134419645819, 134419645829⟩, ⟨128682257369, 140264245155⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 136314880 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 132382720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell4) (join_sr (m := 204800000) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 135004160) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 133693440) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 132382720) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 219545600) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 135004160) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
