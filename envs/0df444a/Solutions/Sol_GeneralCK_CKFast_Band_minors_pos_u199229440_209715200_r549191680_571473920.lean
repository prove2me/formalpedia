-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r549191680_571473920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:55.03944+00:00
-- url     : https://prove2.me/submissions/c6c4dd5c-12f5-4fbf-97d9-da8c8ee93383

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [419/640, 109/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 549191680 554762240 ⟨⟨207745702899, 207745702908⟩, ⟨199237204712, 216425269734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 554762240 560332800 ⟨⟨209633977346, 209633977355⟩, ⟨201098218887, 218340629162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 549191680 554762240 ⟨⟨204751678486, 204751678491⟩, ⟨196313870234, 213359492101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 554762240 560332800 ⟨⟨206618281023, 206618281027⟩, ⟨198153190395, 215253229331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 560332800 565903360 ⟨⟨211519621377, 211519621386⟩, ⟨202956645022, 220253310806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 565903360 571473920 ⟨⟨213402670499, 213402670508⟩, ⟨204812517939, 222163350843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 560332800 565903360 ⟨⟨208482348463, 208482348467⟩, ⟨199990015120, 217144386889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 565903360 571473920 ⟨⟨210343914782, 210343914786⟩, ⟨201824377744, 219032999378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 549191680 554762240 ⟨⟨201779224639, 201779224648⟩, ⟨193411219621, 210316177277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 554762240 560332800 ⟨⟨203624089517, 203624089526⟩, ⟨195228790787, 212188214906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 549191680 554762240 ⟨⟨198827844337, 198827844346⟩, ⟨190528774578, 207294809691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 554762240 560332800 ⟨⟨200650909034, 200650909042⟩, ⟨192324544625, 209145073936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 560332800 565903360 ⟨⟨205466512297, 205466512306⟩, ⟨197043956843, 214057768618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 565903360 571473920 ⟨⟨207306525478, 207306525485⟩, ⟨198856749686, 215924871502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 560332800 565903360 ⟨⟨202471622329, 202471622339⟩, ⟨194117997630, 210992947683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 565903360 571473920 ⟨⟨204290015302, 204290015311⟩, ⟨195909164103, 212838462559⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 549191680 571473920 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 560332800) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 554762240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 565903360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 560332800) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 554762240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 565903360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (419/640 : ℝ) (109/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  have e3 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
