-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r791674880_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:16:53.715426+00:00
-- url     : https://prove2.me/submissions/73a4225e-360a-4f5b-9d5d-dcf1720178d4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [151/160, 1]` by 15 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 791674880 803471360 ⟨⟨370682666930, 370682666942⟩, ⟨357277991812, 384300168608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 152043520 791674880 803471360 ⟨⟨366376440882, 366376440888⟩, ⟨353081054155, 379885796977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 149422080 803471360 815267840 ⟨⟨375221422456, 375221422468⟩, ⟨361771863590, 388879880490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 803471360 815267840 ⟨⟨370882835223, 370882835228⟩, ⟨357541521236, 384434334112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 154664960 791674880 803471360 ⟨⟨362096386452, 362096386465⟩, ⟨348909525749, 375498272937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 157286400 791674880 803471360 ⟨⟨357841919014, 357841919025⟩, ⟨344762832555, 371137004171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152043520 154664960 803471360 815267840 ⟨⟨366569959800, 366569959811⟩, ⟨353336175555, 380015125941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154664960 157286400 803471360 815267840 ⟨⟨362282223764, 362282223775⟩, ⟨349155263640, 375621676927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 149422080 815267840 827064320 ⟨⟨379750515338, 379750515351⟩, ⟨366256245130, 393449732575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 152043520 815267840 827064320 ⟨⟨375379785375, 375379785382⟩, ⟨361992716845, 388973228533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 152043520 827064320 838860800 ⟨⟨382065964810, 382065964822⟩, ⟨359540261026, 405162675646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 152043520 154664960 815267840 827064320 ⟨⟨371034306976, 371034306987⟩, ⟨357753771558, 384522553632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 157286400 815267840 827064320 ⟨⟨366713519698, 366713519710⟩, ⟨353538857321, 380097141818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 827064320 838860800 ⟨⟨375489887630, 375489887642⟩, ⟨362162761814, 389021026375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 827064320 838860800 ⟨⟨371136253056, 371136253067⟩, ⟨357914048514, 384563855570⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 791674880 838860800 t = true :=
  ⟨_, (join_sr (m := 815267840) (by decide) (join_su (m := 152043520) (by decide) (join_sr (m := 803471360) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 149422080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 803471360) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154664960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 152043520) (by decide) (join_sr (m := 827064320) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 827064320) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 154664960) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (151/160 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
