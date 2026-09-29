-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r367001600_390594560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:58.803356+00:00
-- url     : https://prove2.me/submissions/22224fa8-e540-429b-8831-b6d0dfbef40f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [7/16, 149/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 367001600 372899840 ⟨⟨218616719449, 218616719459⟩, ⟨208275065113, 229213229095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 128450560 372899840 378798080 ⟨⟨221500723630, 221500723641⟩, ⟨211131931201, 232122810000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 131072000 367001600 372899840 ⟨⟨215439554648, 215439554658⟩, ⟨205223464251, 225906869173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 372899840 378798080 ⟨⟨218296517392, 218296517403⟩, ⟨208052794817, 228789998122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 128450560 378798080 384696320 ⟨⟨224372610293, 224372610304⟩, ⟨213976944006, 235020008819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125829120 128450560 384696320 390594560 ⟨⟨227232591755, 227232591766⟩, ⟨216810309415, 237905044343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 131072000 378798080 384696320 ⟨⟨221141743813, 221141743822⟩, ⟨210870646527, 231661132067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 128450560 131072000 384696320 390594560 ⟨⟨223975436828, 223975436837⟩, ⟨213677216191, 234520480085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 133693440 367001600 372899840 ⟨⟨212312303684, 212312303694⟩, ⟨202218850191, 222653432348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131072000 133693440 372899840 378798080 ⟨⟨215142106879, 215142106888⟩, ⟨205020567996, 225509945950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 136314880 367001600 372899840 ⟨⟨209233354104, 209233354112⟩, ⟨199259714078, 219451200455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 136314880 372899840 378798080 ⟨⟨212035893664, 212035893674⟩, ⟨202033753612, 222280951869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 378798080 384696320 ⟨⟨217960546012, 217960546021⟩, ⟨207811172253, 228354842979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 131072000 133693440 384696320 390594560 ⟨⟨220767814987, 220767814998⟩, ⟨210590851069, 231188323194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 136314880 378798080 384696320 ⟨⟨214827432566, 214827432576⟩, ⟨204797035899, 225099456516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 384696320 390594560 ⟨⟨217608156073, 217608156084⟩, ⟨207549740704, 227906905220⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 367001600 390594560 t = true :=
  ⟨_, (join_su (m := 131072000) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 372899840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 128450560) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 384696320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378798080) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 372899840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133693440) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 384696320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (149/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
