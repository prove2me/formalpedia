-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:53:22.702304+00:00
-- url     : https://prove2.me/submissions/ff8277f8-fc77-4f99-9586-93021165f852

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 602931200 614727680 ⟨⟨327585753897, 327585753909⟩, ⟨313865211759, 341588502946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 131072000 602931200 614727680 ⟨⟨323541362451, 323541362465⟩, ⟨309960891487, 337403057787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 128450560 614727680 626524160 ⟨⟨332640876670, 332640876682⟩, ⟨318881110277, 346677691351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 614727680 626524160 ⟨⟨328562317243, 328562317257⟩, ⟨314941073245, 342459834988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 602931200 614727680 ⟨⟨319537800657, 319537800668⟩, ⟨306095458667, 333260328922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 602931200 614727680 ⟨⟨315573995315, 315573995327⟩, ⟨302267886734, 329159200266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 614727680 626524160 ⟨⟨324524022219, 324524022231⟩, ⟨311039436053, 338284046613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 136314880 614727680 626524160 ⟨⟨320524940977, 320524940991⟩, ⟨307175192013, 334149235527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 626524160 638320640 ⟨⟨337672965134, 337672965145⟩, ⟨323874410199, 351743420074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 128450560 131072000 626524160 638320640 ⟨⟨333560784111, 333560784123⟩, ⟨319899205212, 347493692663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 128450560 638320640 650117120 ⟨⟨342682884859, 342682884870⟩, ⟨328845952784, 356786577766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 638320640 650117120 ⟨⟨338537601176, 338537601188⟩, ⟨324836101771, 352505491568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 626524160 638320640 ⟨⟨329488298589, 329488298600⟩, ⟨315961907302, 343285383059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 626524160 638320640 ⟨⟨325454480060, 325454480071⟩, ⟨312061529305, 339117425344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131072000 133693440 638320640 650117120 ⟨⟨334431441027, 334431441039⟩, ⟨320863660530, 348265171672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 638320640 650117120 ⟨⟨330363397555, 330363397566⟩, ⟨316927661077, 344064576356⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 128450560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 614727680) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133693440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 131072000) (by decide) (join_sr (m := 638320640) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 128450560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 638320640) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133693440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
