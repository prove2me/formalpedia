-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:36:26.839768+00:00
-- url     : https://prove2.me/submissions/784c2967-0cee-4c8c-9ca8-fcbd010b75e2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 192675840 195461120 ⟨⟨73071754179, 73071754184⟩, ⟨71167485901, 74990603482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212992000 213647360 192675840 195461120 ⟨⟨72761109661, 72761109668⟩, ⟨70862016290, 74674722618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212992000 195461120 198246400 ⟨⟨74073253561, 74073253568⟩, ⟨72164817812, 75996274018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 195461120 198246400 ⟨⟨73758719424, 73758719429⟩, ⟨71855468978, 75676493339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 213647360 214302720 192675840 195461120 ⟨⟨72451427191, 72451427197⟩, ⟨70557483415, 74359829528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214302720 214958080 192675840 195461120 ⟨⟨72142699510, 72142699514⟩, ⟨70253880215, 74045916748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 195461120 198246400 ⟨⟨73445155130, 73445155136⟩, ⟨71547064683, 75357708223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214302720 214958080 195461120 198246400 ⟨⟨73132553382, 73132553386⟩, ⟨71239597826, 75039911163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 212992000 198246400 201031680 ⟨⟨75073583887, 75073583894⟩, ⟨73160987085, 77000768990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212992000 213647360 198246400 201031680 ⟨⟨74755173615, 74755173622⟩, ⟨72847772392, 76677102106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 212992000 201031680 203816960 ⟨⟨76072751483, 76072751490⟩, ⟨74156000007, 78004094766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212992000 213647360 201031680 203816960 ⟨⟨75750478470, 75750478476⟩, ⟨73838932727, 77676555190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 198246400 201031680 ⟨⟨74437740853, 74437740861⟩, ⟨72535509913, 76354438439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214302720 214958080 198246400 201031680 ⟨⟨74121278265, 74121278270⟩, ⟨72224192509, 76032770444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214302720 201031680 203816960 ⟨⟨75429190504, 75429190511⟩, ⟨73522825208, 77350026353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 201031680 203816960 ⟨⟨75108880209, 75108880213⟩, ⟨73207670272, 77024500676⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212992000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214302720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 213647360) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 212992000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 214302720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
