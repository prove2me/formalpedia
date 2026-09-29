-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u117964800_120586240_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:14:39.83634+00:00
-- url     : https://prove2.me/submissions/b74c1ea3-0bbc-46fb-aa3b-3c7ed5bc5947

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/64, 23/160]`, `ρ ∈ [31/256, 41/320]` by 8 cells of the computing
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
theorem cell0 : cellOK 117964800 118620160 101580800 104529920 ⟨⟨75623500604, 75623500613⟩, ⟨72665586625, 78617680368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 118620160 119275520 101580800 104529920 ⟨⟨75255583876, 75255583883⟩, ⟨72310927466, 78236216001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 118620160 104529920 107479040 ⟨⟨77610002167, 77610002175⟩, ⟨74644691816, 80611457039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 118620160 119275520 104529920 107479040 ⟨⟨77233836521, 77233836530⟩, ⟨74281798878, 80221731204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 119275520 119930880 101580800 104529920 ⟨⟨74890310793, 74890310798⟩, ⟨71958789927, 77857520973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119930880 120586240 101580800 104529920 ⟨⟨74527647974, 74527647983⟩, ⟨71609142365, 77481560105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 119275520 119930880 104529920 107479040 ⟨⟨76860356965, 76860356968⟩, ⟨73921470273, 79834816823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119930880 120586240 104529920 107479040 ⟨⟨76489529749, 76489529758⟩, ⟨73563673985, 79450678369⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 117964800 120586240 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 119275520) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 118620160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 104529920) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119930880) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/64 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
