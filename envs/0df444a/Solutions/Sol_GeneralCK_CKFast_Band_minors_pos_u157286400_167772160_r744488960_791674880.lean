-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r744488960_791674880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:16:03.417678+00:00
-- url     : https://prove2.me/submissions/c9134b34-3e62-464e-b5a9-8b4f8b07bb38

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [71/80, 151/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 744488960 756285440 ⟨⟨335889257524, 335889257534⟩, ⟨323114246431, 348894369183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 162529280 744488960 756285440 ⟨⟨331823219508, 331823219519⟩, ⟨319157926242, 344718885950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 159907840 756285440 768081920 ⟨⟨340335489025, 340335489037⟩, ⟨327510904515, 353386910732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 756285440 768081920 ⟨⟨336234324391, 336234324402⟩, ⟨323518608178, 349177287033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 165150720 744488960 756285440 ⟨⟨327782752189, 327782752193⟩, ⟨315226277177, 340569807969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 167772160 744488960 756285440 ⟨⟨323767291540, 323767291551⟩, ⟨311318748718, 336446560179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 162529280 165150720 756285440 768081920 ⟨⟨332158324804, 332158324810⟩, ⟨319550622425, 344993615084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165150720 167772160 756285440 768081920 ⟨⟨328106937754, 328106937765⟩, ⟨315606407111, 340835332483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 159907840 768081920 779878400 ⟨⟨344771129601, 344771129612⟩, ⟨331897188153, 357868619294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 162529280 768081920 779878400 ⟨⟨340635108974, 340635108985⟩, ⟨327869182941, 353625128269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 159907840 779878400 791674880 ⟨⟨349196639456, 349196639468⟩, ⟨336273545508, 362339966457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 162529280 779878400 791674880 ⟨⟨345026019128, 345026019141⟩, ⟨332210084707, 358062866600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 768081920 779878400 ⟨⟨336523845461, 336523845466⟩, ⟨323865124975, 349407133812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 167772160 768081920 779878400 ⟨⟨332436797879, 332436797892⟩, ⟨319884484349, 345214085959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 162529280 165150720 779878400 791674880 ⟨⟨340879745976, 340879745981⟩, ⟨328170205301, 353810806728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 779878400 791674880 ⟨⟨336757289967, 336757289978⟩, ⟨324153387489, 349583249089⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 744488960 791674880 t = true :=
  ⟨_, (join_sr (m := 768081920) (by decide) (join_su (m := 162529280) (by decide) (join_sr (m := 756285440) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 159907840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 756285440) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 165150720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 162529280) (by decide) (join_sr (m := 779878400) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 159907840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 779878400) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 165150720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (71/80 : ℝ) (151/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  have e3 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
