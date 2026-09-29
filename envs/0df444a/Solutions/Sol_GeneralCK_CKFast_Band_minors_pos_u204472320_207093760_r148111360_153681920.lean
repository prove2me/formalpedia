-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:54:06.099368+00:00
-- url     : https://prove2.me/submissions/29d1e8ff-a66f-4534-a4d0-80c9e8143055

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 148111360 149504000 ⟨⟨59639628014, 59639628017⟩, ⟨58056558303, 61233073732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205127680 149504000 150896640 ⟨⟨60175661072, 60175661075⟩, ⟨58590578648, 61771123017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205127680 205783040 148111360 149504000 ⟨⟨59383851179, 59383851184⟩, ⟨57804574403, 60973462360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 149504000 150896640 ⟨⟨59917757497, 59917757502⟩, ⟨58336473257, 61509379721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205127680 150896640 152289280 ⟨⟨60711325370, 60711325373⟩, ⟨59124231855, 62308801902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205127680 152289280 153681920 ⟨⟨61246621953, 61246621955⟩, ⟨59657518962, 62846111438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205127680 205783040 150896640 152289280 ⟨⟨60451299348, 60451299353⟩, ⟨58868009233, 62044931008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205127680 205783040 152289280 153681920 ⟨⟨60984477760, 60984477765⟩, ⟨59399183351, 62580117252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 205783040 206438400 148111360 149504000 ⟨⟨59128972009, 59128972016⟩, ⟨57553467090, 60714770042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 206438400 149504000 150896640 ⟨⟨59660757068, 59660757075⟩, ⟨58083249926, 61248560965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 206438400 207093760 148111360 149504000 ⟨⟨58874983315, 58874983322⟩, ⟨57303229349, 60456989404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 206438400 207093760 149504000 150896640 ⟨⟨59404652557, 59404652564⟩, ⟨57830901601, 60988659341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 150896640 152289280 ⟨⟨60192181907, 60192181913⟩, ⟨58612674097, 61781990092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 205783040 206438400 152289280 153681920 ⟨⟨60723247540, 60723247546⟩, ⟨59141740615, 62315058442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 206438400 207093760 150896640 152289280 ⟨⟨59933965786, 59933965792⟩, ⟨58358219366, 61519971717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 152289280 153681920 ⟨⟨60462923997, 60462924003⟩, ⟨58885183635, 62050927534⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 205783040) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 205127680) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205127680) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 152289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 150896640) (by decide) (join_su (m := 206438400) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 149504000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 206438400) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 152289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
