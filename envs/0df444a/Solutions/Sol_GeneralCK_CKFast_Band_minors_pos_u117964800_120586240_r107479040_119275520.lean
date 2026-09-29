-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u117964800_120586240_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:22.638504+00:00
-- url     : https://prove2.me/submissions/d7b2baee-5787-45de-bb1a-fc14d068e35b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/64, 23/160]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 117964800 118620160 107479040 110428160 ⟨⟨79588013145, 79588013152⟩, ⟨76615398867, 82596650620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 118620160 119275520 107479040 110428160 ⟨⟨79203699497, 79203699504⟩, ⟨76244371713, 82198765569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 118620160 110428160 113377280 ⟨⟨81557630140, 81557630149⟩, ⟨78577802755, 84573359347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 118620160 119275520 110428160 113377280 ⟨⟨81165267708, 81165267717⟩, ⟨78198739290, 84167415603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 119275520 119930880 107479040 110428160 ⟨⟨78822113071, 78822113073⟩, ⟨75875950316, 81803732763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119930880 120586240 107479040 110428160 ⟨⟨78443219776, 78443219783⟩, ⟨75510102307, 81411516340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 119275520 119930880 110428160 113377280 ⟨⟨80775672354, 80775672358⟩, ⟨77822321750, 83764363596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119930880 120586240 110428160 113377280 ⟨⟨80388809667, 80388809675⟩, ⟨77448517428, 83364167160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 118620160 113377280 116326400 ⟨⟨83518948302, 83518948310⟩, ⟨80531997041, 86541679969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 118620160 119275520 113377280 116326400 ⟨⟨83118634645, 83118634652⟩, ⟨80144993544, 86127776360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 117964800 118620160 116326400 119275520 ⟨⟨85472061352, 85472061361⟩, ⟨82478073887, 88501707781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 118620160 119275520 116326400 119275520 ⟨⟨85063892400, 85063892410⟩, ⟨82083225046, 88079941470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 119275520 119930880 113377280 116326400 ⟨⟨82721126676, 82721126682⟩, ⟨79760674911, 85716802719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119930880 120586240 113377280 116326400 ⟨⟨82326389684, 82326389693⟩, ⟨79379008125, 85308722590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119275520 119930880 116326400 119275520 ⟨⟨84658566539, 84658566545⟩, ⟨81691098815, 87661142132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119930880 120586240 116326400 119275520 ⟨⟨84256048765, 84256048775⟩, ⟨81301661871, 87245273033⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 117964800 120586240 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 118620160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119930880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 119275520) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 118620160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 119930880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/64 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
