-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:33:45.504365+00:00
-- url     : https://prove2.me/submissions/a060ef16-e8f3-47dc-9ede-9c3fcb2b0cba

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 437780480 443351040 ⟨⟨145517812573, 145517812577⟩, ⟨141253416688, 149837286245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 437780480 443351040 ⟨⟨144344292477, 144344292485⟩, ⟨140101027326, 148642333798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 443351040 448921600 ⟨⟨147233256345, 147233256349⟩, ⟨142954212284, 151567385926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 443351040 448921600 ⟨⟨146047782253, 146047782262⟩, ⟨141789902015, 150360449705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 437780480 443351040 ⟨⟨143175200653, 143175200661⟩, ⟨138952920180, 147451957863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229376000 230686720 437780480 443351040 ⟨⟨142010482655, 142010482663⟩, ⟨137809042466, 146266102321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228065280 229376000 443351040 448921600 ⟨⟨144866739090, 144866739098⟩, ⟨140629877615, 149158091587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 443351040 448921600 ⟨⟨143690072569, 143690072575⟩, ⟨139474086430, 147960255633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226754560 448921600 454492160 ⟨⟨148946416924, 148946416928⟩, ⟨144652743687, 153295182263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 228065280 448921600 454492160 ⟨⟨147749037930, 147749037938⟩, ⟨143476560756, 152076312230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226754560 454492160 460062720 ⟨⟨150657320157, 150657320161⟩, ⟨146349036477, 155020701370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226754560 228065280 454492160 460062720 ⟨⟨149448084697, 149448084706⟩, ⟨145161028481, 153789946819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 448921600 454492160 ⟨⟨146556091757, 146556091765⟩, ⟨142304666594, 150862021111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 448921600 454492160 ⟨⟨145367524285, 145367524292⟩, ⟨141137008691, 149652253162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 229376000 454492160 460062720 ⟨⟨148243283201, 148243283209⟩, ⟨143977311415, 152563771231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 454492160 460062720 ⟨⟨147042861722, 147042861729⟩, ⟨142797832926, 151342119060⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229376000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228065280) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226754560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 454492160) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229376000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
