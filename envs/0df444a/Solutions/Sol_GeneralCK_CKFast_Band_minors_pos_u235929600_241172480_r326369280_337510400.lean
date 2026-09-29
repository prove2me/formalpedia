-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r326369280_337510400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:37:59.903871+00:00
-- url     : https://prove2.me/submissions/5146625e-19fa-4a17-8e0b-2d03e84d1ce6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [249/640, 103/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 326369280 329154560 ⟨⟨103001789274, 103001789281⟩, ⟨99722670442, 106318106862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 329154560 331939840 ⟨⟨103833753927, 103833753935⟩, ⟨100547783140, 107156956875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 326369280 329154560 ⟨⟨102113990882, 102113990890⟩, ⟨98848560704, 105416422951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 329154560 331939840 ⟨⟨102939482870, 102939482876⟩, ⟨99667224937, 106248776856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 331939840 334725120 ⟨⟨104665123888, 104665123895⟩, ⟨101372303771, 107995209379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 334725120 337510400 ⟨⟨105495902170, 105495902178⟩, ⟨102196235334, 108832867403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 331939840 334725120 ⟨⟨103764394160, 103764394167⟩, ⟨100485310909, 107080547441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 334725120 337510400 ⟨⟨104588727683, 104588727689⟩, ⟨101302821535, 107911737652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 326369280 329154560 ⟨⟨101229954934, 101229954939⟩, ⟨97978102230, 104518614644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 329154560 331939840 ⟨⟨102048984848, 102048984850⟩, ⟨98790328791, 105344482813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 326369280 329154560 ⟨⟨100349631794, 100349631801⟩, ⟨97111246803, 103624630872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 329154560 331939840 ⟨⟨101162210175, 101162210181⟩, ⟨97917046426, 104444023636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 331939840 334725120 ⟨⟨102867447808, 102867447812⟩, ⟨99601990650, 106169781599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 334725120 337510400 ⟨⟨103685346663, 103685346668⟩, ⟨100413090638, 106994513862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 331939840 334725120 ⟨⟨101974235101, 101974235108⟩, ⟨98722294663, 105262860702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 334725120 337510400 ⟨⟨102785709340, 102785709346⟩, ⟨99526994265, 106081144848⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 326369280 337510400 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 329154560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 334725120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331939840) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 329154560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 334725120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (103/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
