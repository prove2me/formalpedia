-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:02.932374+00:00
-- url     : https://prove2.me/submissions/1f21e8ba-89ef-40f9-8ed2-6fc6da6c3e80

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [167/320, 351/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 437780480 443351040 ⟨⟨170008621577, 170008621582⟩, ⟨165288155924, 174790689019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 200540160 201850880 437780480 443351040 ⟨⟨168733927571, 168733927579⟩, ⟨164037902967, 173491204169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 200540160 443351040 448921600 ⟨⟨171963398923, 171963398927⟩, ⟨167227874033, 176760449642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 443351040 448921600 ⟨⟨170676741840, 170676741847⟩, ⟨165965665273, 175448999519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 203161600 437780480 443351040 ⟨⟨167464916298, 167464916307⟩, ⟨162793147716, 172197589693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203161600 204472320 437780480 443351040 ⟨⟨166201516487, 166201516496⟩, ⟨161553821155, 170909772043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 203161600 443351040 448921600 ⟨⟨169395765436, 169395765445⟩, ⟨164708953770, 174143416011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 204472320 443351040 448921600 ⟨⟨168120398764, 168120398772⟩, ⟨163457670790, 172843625929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 200540160 448921600 454492160 ⟨⟨173914738650, 173914738654⟩, ⟨169164193317, 178726732416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 200540160 201850880 448921600 454492160 ⟨⟨172616184519, 172616184528⟩, ⟨167890093676, 177403384173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 201850880 454492160 460062720 ⟨⟨175206776441, 175206776450⟩, ⟨167168872388, 183417970448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 201850880 203161600 448921600 454492160 ⟨⟨171323308097, 171323308105⟩, ⟨166621489932, 176085897851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 204472320 448921600 454492160 ⟨⟨170036038756, 170036038764⟩, ⟨165358313636, 174774200630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201850880 203161600 454492160 460062720 ⟨⟨173247584713, 173247584720⟩, ⟨168530796110, 178025076168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 204472320 454492160 460062720 ⟨⟨171948475934, 171948475942⟩, ⟨167255788663, 176701536117⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 200540160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203161600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 201850880) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 454492160) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 203161600) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
