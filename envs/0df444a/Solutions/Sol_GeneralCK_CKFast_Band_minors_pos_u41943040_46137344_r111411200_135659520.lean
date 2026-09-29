-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:44:52.124828+00:00
-- url     : https://prove2.me/submissions/34df8e3f-3214-4575-9020-52d784422581

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 11/200]`, `ρ ∈ [17/128, 207/1280]` by 18 cells of the computing
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
theorem cell0 : cellOK 41943040 42991616 111411200 117473280 ⟨⟨166801636248, 166801636262⟩, ⟨155362782579, 178670243077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 42991616 44040192 111411200 117473280 ⟨⟨164653222754, 164653222768⟩, ⟨153394859497, 176330044942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 42991616 117473280 123535360 ⟨⟨173300419463, 173300419482⟩, ⟨161887307952, 185130081434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 42991616 44040192 117473280 123535360 ⟨⟨171110576152, 171110576170⟩, ⟨159874670447, 182752363616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 44040192 45088768 111411200 114442240 ⟨⟨160932264876, 160932264893⟩, ⟨152809463258, 169277185059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 44040192 45088768 114442240 117473280 ⟨⟨164176751778, 164176751792⟩, ⟨156057815734, 172514721379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 45088768 46137344 111411200 114442240 ⟨⟨158901254395, 158901254412⟩, ⟨150900511727, 167118534164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 45088768 46137344 114442240 117473280 ⟨⟨162124098289, 162124098303⟩, ⟨154126216411, 170335579223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 44040192 45088768 117473280 123535360 ⟨⟨168974955908, 168974955925⟩, ⟨157910750888, 180434791520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 45088768 46137344 117473280 123535360 ⟨⟨166891384383, 166891384400⟩, ⟨155993629138, 178174914844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 42991616 123535360 129597440 ⟨⟨179651489522, 179651489537⟩, ⟨168266448794, 191440394685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 42991616 44040192 123535360 129597440 ⟨⟨177423485952, 177423485970⟩, ⟨166212385073, 189028370788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 42991616 129597440 135659520 ⟨⟨185862402823, 185862402837⟩, ⟨174507456725, 197609020043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 42991616 44040192 129597440 135659520 ⟨⟨183599234205, 183599234223⟩, ⟨172414990022, 195165622426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 44040192 45088768 123535360 129597440 ⟨⟨175249504596, 175249504610⟩, ⟨164207040347, 186676056492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 45088768 46137344 123535360 129597440 ⟨⟨173127417249, 173127417263⟩, ⟨162248526963, 184381063576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 44040192 45088768 129597440 135659520 ⟨⟨181389821638, 181389821652⟩, ⟨170371170798, 192781442940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 45088768 46137344 129597440 135659520 ⟨⟨179232083650, 179232083667⟩, ⟨168374145280, 190454154997⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 46137344 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 44040192) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 42991616) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 42991616) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 45088768) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 114442240) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 45088768) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 44040192) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 42991616) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 42991616) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 129597440) (by decide) (join_su (m := 45088768) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 45088768) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
