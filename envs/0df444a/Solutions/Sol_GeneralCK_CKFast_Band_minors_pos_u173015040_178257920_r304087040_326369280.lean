-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.188983+00:00
-- url     : https://prove2.me/submissions/47fecb04-caad-461b-95ff-f4a6e579f888

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 304087040 309657600 ⟨⟨142503996296, 142503996301⟩, ⟨137629276382, 147452333528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 174325760 175636480 304087040 309657600 ⟨⟨141413235527, 141413235534⟩, ⟨136567531741, 146331961407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 174325760 309657600 315228160 ⟨⟨144838599802, 144838599808⟩, ⟨139947199878, 149803450200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 309657600 315228160 ⟨⟨143733409547, 143733409556⟩, ⟨138871033774, 148668648531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176947200 304087040 309657600 ⟨⟨140329683012, 140329683019⟩, ⟨135512698566, 145219101712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 178257920 304087040 309657600 ⟨⟨139253231626, 139253231634⟩, ⟨134464674469, 144113642458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 175636480 176947200 309657600 315228160 ⟨⟨142635453466, 142635453474⟩, ⟨137801807231, 147541382830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 176947200 178257920 309657600 315228160 ⟨⟨141544624638, 141544624646⟩, ⟨136739417990, 146421541397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 174325760 315228160 320798720 ⟨⟨147166354657, 147166354662⟩, ⟨142258368781, 152147622503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 174325760 175636480 315228160 320798720 ⟨⟨146046866173, 146046866182⟩, ⟨141167910199, 150998524808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 174325760 320798720 326369280 ⟨⟨149487351259, 149487351261⟩, ⟨144562871936, 154484942405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 174325760 175636480 320798720 326369280 ⟨⟨148353693502, 148353693511⟩, ⟨143458247613, 153321679854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 315228160 320798720 ⟨⟨144934635715, 144934635723⟩, ⟨140084417232, 149856984530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 178257920 315228160 320798720 ⟨⟨143829556594, 143829556601⟩, ⟨139007787788, 148722890273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 176947200 320798720 326369280 ⟨⟨147227315612, 147227315621⟩, ⟨142360612978, 152165994129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 320798720 326369280 ⟨⟨146108111156, 146108111165⟩, ⟨141269866127, 151017774165⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 174325760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 176947200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 175636480) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 174325760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 176947200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
