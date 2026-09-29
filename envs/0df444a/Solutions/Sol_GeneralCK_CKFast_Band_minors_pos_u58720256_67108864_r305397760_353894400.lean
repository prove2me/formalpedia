-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:19:18.642803+00:00
-- url     : https://prove2.me/submissions/369c4760-5c32-4a90-904b-6760500be753

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [233/640, 27/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 305397760 317521920 ⟨⟨289195417717, 289195417732⟩, ⟨271733331944, 307245035768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 60817408 62914560 305397760 317521920 ⟨⟨284999568345, 284999568360⟩, ⟨267829004534, 302746000864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 60817408 317521920 329646080 ⟨⟨296841795640, 296841795653⟩, ⟨279432579505, 314815623134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 317521920 329646080 ⟨⟨292614664675, 292614664687⟩, ⟨275489529697, 310293833870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 65011712 305397760 317521920 ⟨⟨280903515073, 280903515088⟩, ⟨264015492174, 298356043008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 65011712 67108864 305397760 317521920 ⟨⟨276902938767, 276902938781⟩, ⟨260288907993, 294070404675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 62914560 65011712 317521920 329646080 ⟨⟨288485504563, 288485504575⟩, ⟨271635924853, 305878786212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 65011712 67108864 317521920 329646080 ⟨⟨284450142823, 284450142838⟩, ⟨267867995206, 301565901995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 60817408 329646080 341770240 ⟨⟨304356854855, 304356854870⟩, ⟨287001154217, 322255178541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 60817408 62914560 329646080 341770240 ⟨⟨300101065508, 300101065520⟩, ⟨283022211663, 317712977236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 58720256 60817408 341770240 353894400 ⟨⟨311747818497, 311747818512⟩, ⟨294446071974, 329571077331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 60817408 62914560 341770240 353894400 ⟨⟨307465747832, 307465747847⟩, ⟨290433817166, 325010569141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62914560 65011712 329646080 341770240 ⟨⟨295941426390, 295941426404⟩, ⟨279131323672, 313275217409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 65011712 67108864 329646080 341770240 ⟨⟨291873905170, 291873905184⟩, ⟨275324833434, 308937490909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 65011712 341770240 353894400 ⟨⟨303278017403, 303278017417⟩, ⟨286508213630, 320552241559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 65011712 67108864 341770240 353894400 ⟨⟨299180728688, 299180728703⟩, ⟨282665713381, 316191847536⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 60817408) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 65011712) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 65011712) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 62914560) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 60817408) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 341770240) (by decide) (join_su (m := 65011712) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 65011712) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
