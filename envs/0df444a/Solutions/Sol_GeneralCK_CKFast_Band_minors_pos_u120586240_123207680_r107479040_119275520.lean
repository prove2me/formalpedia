-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_123207680_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:53.378177+00:00
-- url     : https://prove2.me/submissions/b1f3c6be-0ea2-4a02-ab33-7b2a292a5531

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 47/320]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121241600 107479040 110428160 ⟨⟨78066986108, 78066986116⟩, ⟨75146795854, 81022081050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121241600 121896960 107479040 110428160 ⟨⟨77693379111, 77693379119⟩, ⟨74785999655, 80635392233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121241600 110428160 113377280 ⟨⟨80004645818, 80004645827⟩, ⟨77077294166, 82966790731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121241600 121896960 110428160 113377280 ⟨⟨79623147537, 79623147546⟩, ⟨76708620327, 82572199343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 121896960 122552320 107479040 110428160 ⟨⟨77322366382, 77322366390⟩, ⟨74427682924, 80251415806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 122552320 123207680 107479040 110428160 ⟨⟨76953916052, 76953916054⟩, ⟨74071815381, 79870118256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 121896960 122552320 110428160 113377280 ⟨⟨79244282102, 79244282109⟩, ⟨76342464802, 82180358614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 122552320 123207680 110428160 113377280 ⟨⟨78868017332, 78868017336⟩, ⟨75978796988, 81791234723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 121241600 113377280 116326400 ⟨⟨81934389537, 81934389546⟩, ⟨78999960704, 84903500120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 121241600 121896960 113377280 116326400 ⟨⟨81545092663, 81545092671⟩, ⟨78623500709, 84501100054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 121241600 116326400 119275520 ⟨⟨83856304665, 83856304675⟩, ⟨80914881448, 86832298053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 121241600 121896960 116326400 119275520 ⟨⟨83459300384, 83459300393⟩, ⟨80530725305, 86422181665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 121896960 122552320 113377280 116326400 ⟨⟨81158466043, 81158466051⟩, ⟨78249596719, 84101487725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 122552320 123207680 113377280 116326400 ⟨⟨80774477201, 80774477205⟩, ⟨77878217828, 83704629028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 121896960 122552320 116326400 119275520 ⟨⟨83065002622, 83065002631⟩, ⟨80149161731, 86014888931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 122552320 123207680 116326400 119275520 ⟨⟨82673378625, 82673378629⟩, ⟨79770159532, 85610385481⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 123207680 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 121896960) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 121241600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121241600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 122552320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 122552320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 121896960) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 121241600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 121241600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 122552320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 122552320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (47/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
