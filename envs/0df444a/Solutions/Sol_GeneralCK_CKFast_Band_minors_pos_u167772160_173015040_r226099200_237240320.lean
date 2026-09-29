-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:50.825978+00:00
-- url     : https://prove2.me/submissions/6ef69a11-5ad3-486d-a885-8931107f63d5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 226099200 228884480 ⟨⟨111980911499, 111980911507⟩, ⟨108079255875, 115934999191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 169082880 228884480 231669760 ⟨⟨113236903680, 113236903689⟩, ⟨109326848501, 117199358932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 169082880 170393600 226099200 228884480 ⟨⟨111084088976, 111084088984⟩, ⟨107204344623, 115015818827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 228884480 231669760 ⟨⟨112331642725, 112331642732⟩, ⟨108443517484, 116271724091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 169082880 231669760 234455040 ⟨⟨114490632969, 114490632975⟩, ⟨110572204020, 118461429537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 169082880 234455040 237240320 ⟨⟨115742114932, 115742114939⟩, ⟨111815337786, 119721226796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 170393600 231669760 234455040 ⟨⟨113576979535, 113576979542⟩, ⟨109680498504, 117525386868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169082880 170393600 234455040 237240320 ⟨⟨114820114543, 114820114552⟩, ⟨110915302608, 118776822511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171704320 226099200 228884480 ⟨⟨110194291138, 110194291145⟩, ⟨106336194421, 114103933541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 228884480 231669760 ⟨⟨111433438755, 111433438762⟩, ⟨107566980483, 115351415891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 226099200 228884480 ⟨⟨109311402651, 109311402659⟩, ⟨105474694698, 113199223102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171704320 173015040 228884480 231669760 ⟨⟨110542176263, 110542176272⟩, ⟨106697126721, 114438313960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 231669760 234455040 ⟨⟨112670414560, 112670414567⟩, ⟨108795619148, 116596701565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 170393600 171704320 234455040 237240320 ⟨⟨113905233270, 113905233278⟩, ⟨110022124935, 117839805485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 173015040 231669760 234455040 ⟨⟨111770822376, 111770822383⟩, ⟨107917454992, 115675253124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 234455040 237240320 ⟨⟨112997355298, 112997355305⟩, ⟨109135693630, 116910055099⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 226099200 237240320 t = true :=
  ⟨_, (join_su (m := 170393600) (by decide) (join_sr (m := 231669760) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228884480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 169082880) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234455040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231669760) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 228884480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 171704320) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 234455040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
