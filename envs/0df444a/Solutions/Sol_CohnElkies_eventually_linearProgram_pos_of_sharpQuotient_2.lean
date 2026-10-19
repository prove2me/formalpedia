-- Prove2me | solution 2 for CohnElkies.eventually_linearProgram_pos_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:37.817001+00:00
-- url     : https://prove2.me/submissions/0ad59c3f-ab9e-4dce-80aa-1f05730a3230

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
theorem h47_normProg (d : ℕ) : CohnElkies.normalizedProgram d = CohnElkies.quotientRootMap d (sInf (CohnElkies.quotientSet d)) := by
  rcases (quotientSet d).eq_empty_or_nonempty with hE | hN
  · have hR : Set.range (normalizedCost (d := d)) = ∅ := by
      rw [Set.range_eq_empty_iff]
      constructor
      intro f
      exact (Set.eq_empty_iff_forall_notMem.1 hE) _ ⟨f, rfl⟩
    unfold normalizedProgram
    rw [hR, hE, Real.sInf_empty]
    unfold quotientRootMap
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [Real.zero_rpow (by positivity)]; simp
  · have hpos : ∀ q ∈ quotientSet d, 0 < q := by
      rintro q ⟨f, rfl⟩; exact div_pos (admissible_zero_pos f) f.fourier_zero_pos
    have hbdd : BddBelow (quotientSet d) := ⟨0, fun q hq => (hpos q hq).le⟩
    have hrange : Set.range (normalizedCost (d := d)) = quotientRootMap d '' quotientSet d := by
      ext y; constructor
      · rintro ⟨f, rfl⟩; exact ⟨quotient f, ⟨f, rfl⟩, rfl⟩
      · rintro ⟨q, ⟨f, rfl⟩, rfl⟩; exact ⟨f, rfl⟩
    have Mf : MonotoneOn (quotientRootMap d) (quotientSet d) := by
      intro a ha b hb hab
      unfold quotientRootMap
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (hpos a ha).le hab (by positivity))
        (Real.sqrt_nonneg _)
    have Cf : ContinuousWithinAt (quotientRootMap d) (quotientSet d) (sInf (quotientSet d)) := by
      unfold quotientRootMap
      exact ((Real.continuous_rpow_const (by positivity)).div_const _).continuousAt.continuousWithinAt
    unfold normalizedProgram
    rw [hrange]
    exact (MonotoneOn.map_csInf_of_continuousWithinAt Cf Mf hN hbdd).symm

theorem solution
    (hquotient : SharpQuotientAsymptotic) :
    ∀ᶠ d : ℕ in atTop, 0 < linearProgram d := by
  have hcr : (0:ℝ) < criticalRadius := by unfold criticalRadius; exact inv_pos.2 Real.pi_pos
  filter_upwards [hquotient.eventually (lt_mem_nhds hcr), eventually_gt_atTop 0] with d h hd
  rw [h47_normProg] at h
  unfold quotientRootMap at h
  have hS : 0 ≤ sInf (quotientSet d) := Real.sInf_nonneg (by
    rintro q ⟨f, rfl⟩; exact (div_pos (admissible_zero_pos f) f.fourier_zero_pos).le)
  have hS' : sInf (quotientSet d) ≠ 0 := by
    intro h0
    rw [h0, Real.zero_rpow (inv_ne_zero (by exact_mod_cast hd.ne'))] at h
    simp at h
  unfold linearProgram
  exact mul_pos (div_pos (unitBallVolume_pos d) (by positivity)) (lt_of_le_of_ne hS (Ne.symm hS'))

