-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r237240320_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:33.146905+00:00
-- url     : https://prove2.me/submissions/87ed442a-52df-47fb-bd4f-15b014a4be7d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [181/640, 99/320]` by 19 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 237240320 242810880 ⟨⟨117615157911, 117615157917⟩, ⟨112830339855, 122478326966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 237240320 240025600 ⟨⟨116061062777, 116061062784⟩, ⟨112147944619, 120026046246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 169082880 170393600 240025600 242810880 ⟨⟨117299839146, 117299839153⟩, ⟨113378439245, 121273073198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 167772160 169082880 242810880 248381440 ⟨⟨120104826145, 120104826153⟩, ⟨115301925783, 124985897737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 169082880 170393600 242810880 248381440 ⟨⟨119153963801, 119153963809⟩, ⟨114381155011, 124004219924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 170393600 171704320 237240320 240025600 ⟨⟨115137909497, 115137909505⟩, ⟨111246512257, 119080742458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 171704320 240025600 242810880 ⟨⟨116368457742, 116368457750⟩, ⟨112468795420, 120319527185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 173015040 237240320 240025600 ⟨⟨114221789237, 114221789245⟩, ⟨110351856653, 118142734284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 171704320 173015040 240025600 242810880 ⟨⟨115444138295, 115444138302⟩, ⟨111565957973, 119373304970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 242810880 248381440 ⟨⟨118210321602, 118210321608⟩, ⟨113467262924, 123030114232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 242810880 248381440 ⟨⟨117273783325, 117273783333⟩, ⟨112560139324, 122063458216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167772160 169082880 248381440 253952000 ⟨⟨122585779440, 122585779448⟩, ⟨117764924469, 127484623978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 169082880 170393600 248381440 253952000 ⟨⟨121618665712, 121618665720⟩, ⟨116827931639, 126486674397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167772160 169082880 253952000 259522560 ⟨⟨125058136837, 125058136846⟩, ⟨120219452708, 129974627005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 169082880 170393600 253952000 259522560 ⟨⟨124074943052, 124074943059⟩, ⟨119266405985, 128960580139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 170393600 171704320 248381440 253952000 ⟨⟨120658825610, 120658825619⟩, ⟨115897872993, 125496348156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 171704320 173015040 248381440 253952000 ⟨⟨119706142761, 119706142768⟩, ⟨114974638099, 124513522740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 170393600 171704320 253952000 259522560 ⟨⟨123099073399, 123099073407⟩, ⟨118320346018, 127954204806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 171704320 173015040 253952000 259522560 ⟨⟨122130411395, 122130411402⟩, ⟨117381162190, 126955378462⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 237240320 259522560 t = true :=
  ⟨_, (join_sr (m := 248381440) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (join_sr (m := 240025600) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 169082880) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 242810880) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 240025600) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 171704320) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 170393600) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 169082880) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 253952000) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 171704320) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
