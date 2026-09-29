-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:47:46.402022+00:00
-- url     : https://prove2.me/submissions/0092d68d-76cd-42f9-b044-69375a63a659

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 19/200]`, `ρ ∈ [207/1280, 61/320]` by 20 cells of the computing
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
theorem cell0 : cellOK 75497472 76546048 135659520 138690560 ⟨⟨136428147914, 136428147927⟩, ⟨130744273089, 142223323637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 76546048 138690560 141721600 ⟨⟨138920403880, 138920403892⟩, ⟨133229037671, 144722264367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 76546048 77594624 135659520 138690560 ⟨⟨135194368154, 135194368165⟩, ⟨129565072672, 140933172223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76546048 77594624 138690560 141721600 ⟨⟨137671330237, 137671330247⟩, ⟨132034369984, 143417021195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 76546048 141721600 147783680 ⟨⟨142627735090, 142627735100⟩, ⟨134959288672, 150492391324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 76546048 77594624 141721600 147783680 ⟨⟨141356309969, 141356309982⟩, ⟨133763998404, 149141602289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 77594624 78643200 135659520 138690560 ⟨⟨133979799537, 133979799549⟩, ⟨128403981380, 139663380196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77594624 78643200 138690560 141721600 ⟨⟨136441554604, 136441554617⟩, ⟨130857908488, 142132212935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 78643200 79691776 135659520 138690560 ⟨⟨132783941138, 132783941148⟩, ⟨127260531490, 138413411814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 78643200 79691776 138690560 141721600 ⟨⟨135230577077, 135230577087⟩, ⟨129699185976, 140867305423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 77594624 78643200 141721600 147783680 ⟨⟨140104300790, 140104300802⟩, ⟨132586635567, 147811799235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78643200 79691776 141721600 147783680 ⟨⟨138871209454, 138871209463⟩, ⟨131426745873, 146502437495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 76546048 147783680 153845760 ⟨⟨147514303027, 147514303039⟩, ⟨139832402953, 155389246039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 76546048 77594624 147783680 153845760 ⟨⟨146214134198, 146214134208⟩, ⟨138607821964, 154010367575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 75497472 76546048 153845760 159907840 ⟨⟨152338172306, 152338172317⟩, ⟨144643965542, 160222309197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 76546048 77594624 153845760 159907840 ⟨⟨151010413596, 151010413606⟩, ⟨143391230485, 158816509091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 77594624 78643200 147783680 153845760 ⟨⟨144933516813, 144933516826⟩, ⟨137401333108, 152652577266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 78643200 79691776 147783680 153845760 ⟨⟨143671955684, 143671955697⟩, ⟨136212483596, 151315334935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 77594624 78643200 153845760 159907840 ⟨⟨149702318806, 149702318816⟩, ⟨142156729150, 157431876544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 78643200 79691776 153845760 159907840 ⟨⟨148413396133, 148413396143⟩, ⟨140940010761, 156067876326⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 79691776 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 76546048) (by decide) (join_sr (m := 138690560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138690560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 76546048) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 141721600) (by decide) (join_su (m := 78643200) (by decide) (join_sr (m := 138690560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 138690560) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 78643200) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 77594624) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 76546048) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 76546048) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 153845760) (by decide) (join_su (m := 78643200) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 78643200) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
