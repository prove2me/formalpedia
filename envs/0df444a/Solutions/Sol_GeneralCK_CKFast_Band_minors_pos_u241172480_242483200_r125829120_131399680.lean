-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_242483200_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:16:49.851703+00:00
-- url     : https://prove2.me/submissions/dca13e8b-48e5-46c8-ace8-2585d77fad6d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 37/128]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241500160 125829120 127221760 ⟨⟨39750593753, 39750593758⟩, ⟨38944876167, 40559304618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241500160 241827840 125829120 127221760 ⟨⟨39658104093, 39658104096⟩, ⟨38853380005, 40465815371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241500160 127221760 128614400 ⟨⟨40178591909, 40178591914⟩, ⟨39371930693, 40988247836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241500160 241827840 127221760 128614400 ⟨⟨40085147877, 40085147880⟩, ⟨39279481678, 40893802703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242155520 125829120 127221760 ⟨⟨39565744389, 39565744395⟩, ⟨38762011568, 40372458336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242155520 242483200 125829120 127221760 ⟨⟨39473514152, 39473514157⟩, ⟨38670770376, 40279233005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242155520 127221760 128614400 ⟨⟨39991834876, 39991834882⟩, ⟨39187161460, 40799490858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242155520 242483200 127221760 128614400 ⟨⟨39898652410, 39898652415⟩, ⟨39094969555, 40705311789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241500160 128614400 130007040 ⟨⟨40606397132, 40606397139⟩, ⟨39798792614, 41416997791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241500160 241827840 128614400 130007040 ⟨⟨40511999994, 40511999996⟩, ⟨39705392005, 41321598041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241500160 130007040 131399680 ⟨⟨41034009870, 41034009877⟩, ⟨40225462375, 41845554931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241500160 241827840 130007040 131399680 ⟨⟨40938660883, 40938660886⟩, ⟨40131111426, 41749201828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 241827840 242155520 128614400 130007040 ⟨⟨40417734951, 40417734956⟩, ⟨39612121257, 41226332649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242155520 242483200 128614400 130007040 ⟨⟨40323601506, 40323601512⟩, ⟨39518979884, 41131201096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 241827840 242155520 130007040 131399680 ⟨⟨40843445052, 40843445057⟩, ⟨40036891397, 41652984145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 242155520 242483200 130007040 131399680 ⟨⟨40748361875, 40748361881⟩, ⟨39942801796, 41556901362⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 242483200 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241500160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 242155520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 241827840) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241500160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 242155520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (37/128 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
