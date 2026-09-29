-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_107479040_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:03:14.038267+00:00
-- url     : https://prove2.me/submissions/72a7f53c-8c9f-47cc-b082-f31776aa490a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 41/320]`, `ρ ∈ [137/1280, 73/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 104857600 105512960 89784320 91258880 ⟨⟨74285806962, 74285806970⟩, ⟨71777347303, 76820753330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 105512960 91258880 92733440 ⟨⟨75391527018, 75391527026⟩, ⟨72879504246, 77929990010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 105512960 106168320 89784320 91258880 ⟨⟨73897558077, 73897558085⟩, ⟨71400840101, 76420535935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 105512960 106168320 91258880 92733440 ⟨⟨74998375313, 74998375320⟩, ⟨72498101584, 77524863539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 105512960 92733440 95682560 ⟨⟨77044717215, 77044717224⟩, ⟨73816663473, 80316279835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 105512960 106168320 92733440 95682560 ⟨⟨76644279065, 76644279075⟩, ⟨73432314291, 79899361521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 106823680 89784320 91258880 ⟨⟨73512525661, 73512525663⟩, ⟨71027424860, 76023662743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106168320 106823680 91258880 92733440 ⟨⟨74608469660, 74608469664⟩, ⟨72119820612, 77123110679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 106823680 107479040 89784320 91258880 ⟨⟨73130664053, 73130664061⟩, ⟨70657057920, 75630086039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 106823680 107479040 91258880 92733440 ⟨⟨74221764113, 74221764123⟩, ⟨71744617382, 76724683439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 106168320 106823680 92733440 95682560 ⟨⟨76247130377, 76247130379⟩, ⟨73051087974, 79485904806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 106823680 107479040 92733440 95682560 ⟨⟨75853224784, 75853224794⟩, ⟨72672940822, 79075860576⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 107479040 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 106168320) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 105512960) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 105512960) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 92733440) (by decide) (join_su (m := 106823680) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 106823680) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (41/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
