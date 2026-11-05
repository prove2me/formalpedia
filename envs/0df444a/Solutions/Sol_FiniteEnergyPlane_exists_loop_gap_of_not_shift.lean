-- Prove2me | solution 1 for FiniteEnergyPlane.exists_loop_gap_of_not_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T16:17:17.608009+00:00
-- url     : https://prove2.me/submissions/c6c3699b-f657-454c-9efb-5759df6b4a04

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_reeb_spec

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-! Uniform `C⁰` gap between normalized loops of different periodic Reeb orbits. -/


namespace FiniteEnergyPlane

theorem exists_loop_gap_of_not_shift_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P Q : ReebOrbit H)
    (hPQ : ¬ (P.T = Q.T ∧ ∃ c : ℝ, ∀ τ : ℝ, P.x τ = Q.x (τ + c))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c c' : ℝ, ∃ t : ℝ,
      δ ≤ ‖P.x (P.T * t + c) - Q.x (Q.T * t + c')‖ := by
  have hPc : Continuous P.x := continuous_iff_continuousAt.2 fun t => (P.hasDerivAt t).continuousAt
  have hQc : Continuous Q.x := continuous_iff_continuousAt.2 fun t => (Q.hasDerivAt t).continuousAt
  -- at every pair of phases the two loops differ somewhere
  have hne : ∀ c c' : ℝ, ∃ t : ℝ, P.x (P.T * t + c) ≠ Q.x (Q.T * t + c') := by
    intro c c'
    by_contra hcon
    push Not at hcon
    -- derivatives of the two loops at `t = 0`
    have h1 : HasDerivAt (fun t : ℝ => P.x (P.T * t + c)) (P.T • reeb H (P.x (P.T * 0 + c))) 0 := by
      have hi : HasDerivAt (fun t : ℝ => P.T * t + c) P.T 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul P.T).add_const c
      exact (P.hasDerivAt _).scomp 0 hi
    have h2 : HasDerivAt (fun t : ℝ => Q.x (Q.T * t + c')) (Q.T • reeb H (Q.x (Q.T * 0 + c'))) 0 := by
      have hi : HasDerivAt (fun t : ℝ => Q.T * t + c') Q.T 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Q.T).add_const c'
      exact (Q.hasDerivAt _).scomp 0 hi
    have hfun : (fun t : ℝ => P.x (P.T * t + c)) = fun t : ℝ => Q.x (Q.T * t + c') := funext hcon
    rw [hfun] at h1
    have heq := h1.unique h2
    have hpt := hcon 0
    rw [← hpt] at heq
    have hspec := (reeb_spec H hH _ (P.mem (P.T * 0 + c))).2.1
    have hT : P.T = Q.T := by
      have := congrArg (liouville (P.x (P.T * 0 + c))) heq
      have hl : ∀ a : ℝ, liouville (P.x (P.T * 0 + c)) (a • reeb H (P.x (P.T * 0 + c))) = a := by
        intro a
        have h3 : liouville (P.x (P.T * 0 + c)) (a • reeb H (P.x (P.T * 0 + c))) =
            a * liouville (P.x (P.T * 0 + c)) (reeb H (P.x (P.T * 0 + c))) := by
          simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            Finset.sum_div, mul_div_assoc]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [h3, hspec, mul_one]
      rwa [hl, hl] at this
    apply hPQ
    refine ⟨hT, c' - c, fun τ => ?_⟩
    have := hcon ((τ - c) / P.T)
    have hTne := P.T_pos.ne'
    rw [show P.T * ((τ - c) / P.T) + c = τ by field_simp; ring,
      ← hT, show P.T * ((τ - c) / P.T) + c' = τ + (c' - c) by field_simp; ring] at this
    exact this
  -- compactness in the phases
  have hcpt : IsCompact (Icc 0 P.T ×ˢ Icc 0 Q.T : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hmain : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ (Icc 0 P.T ×ˢ Icc 0 Q.T : Set (ℝ × ℝ)), ∃ t : ℝ,
      δ ≤ ‖P.x (P.T * t + a.1) - Q.x (Q.T * t + a.2)‖ := by
    refine hcpt.induction_on (p := fun s => ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, ∃ t : ℝ,
      δ ≤ ‖P.x (P.T * t + a.1) - Q.x (Q.T * t + a.2)‖) ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
    · rintro s u hsu ⟨δ, hδ, h⟩
      exact ⟨δ, hδ, fun a ha => h a (hsu ha)⟩
    · rintro s u ⟨δ, hδ, h⟩ ⟨δ', hδ', h'⟩
      refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
      rintro a (ha | ha)
      · obtain ⟨t, ht⟩ := h a ha
        exact ⟨t, (min_le_left _ _).trans ht⟩
      · obtain ⟨t, ht⟩ := h' a ha
        exact ⟨t, (min_le_right _ _).trans ht⟩
    · rintro a _
      obtain ⟨t, ht⟩ := hne a.1 a.2
      have hpos : 0 < ‖P.x (P.T * t + a.1) - Q.x (Q.T * t + a.2)‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 ht)
      set ε := ‖P.x (P.T * t + a.1) - Q.x (Q.T * t + a.2)‖ with hε
      have hcont : Continuous (fun b : ℝ × ℝ => ‖P.x (P.T * t + b.1) - Q.x (Q.T * t + b.2)‖) := by
        fun_prop
      have hev : ∀ᶠ b in 𝓝 a, ε / 2 < ‖P.x (P.T * t + b.1) - Q.x (Q.T * t + b.2)‖ :=
        hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
      refine ⟨_, mem_nhdsWithin_of_mem_nhds hev, ε / 2, by positivity, ?_⟩
      intro b hb
      exact ⟨t, le_of_lt hb⟩
  obtain ⟨δ, hδ, h⟩ := hmain
  refine ⟨δ, hδ, fun c c' => ?_⟩
  have hPper : Function.Periodic P.x P.T := P.periodic
  have hQper : Function.Periodic Q.x Q.T := Q.periodic
  set d := toIcoMod P.T_pos 0 c with hdd
  set d' := toIcoMod Q.T_pos 0 c' with hdd'
  have hd : d ∈ Ico 0 P.T := by simpa using toIcoMod_mem_Ico P.T_pos 0 c
  have hd' : d' ∈ Ico 0 Q.T := by simpa using toIcoMod_mem_Ico Q.T_pos 0 c'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, c = d + m • P.T :=
    ⟨toIcoDiv P.T_pos 0 c, by have := self_sub_toIcoMod P.T_pos 0 c; rw [← this, hdd]; abel⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, c' = d' + m' • Q.T :=
    ⟨toIcoDiv Q.T_pos 0 c', by have := self_sub_toIcoMod Q.T_pos 0 c'; rw [← this, hdd']; abel⟩
  obtain ⟨t, ht⟩ := h (d, d') ⟨Ico_subset_Icc_self hd, Ico_subset_Icc_self hd'⟩
  refine ⟨t, ?_⟩
  have e1 : P.x (P.T * t + c) = P.x (P.T * t + d) := by
    rw [show P.T * t + c = P.T * t + d + m • P.T by rw [add_assoc, ← hm]]
    exact hPper.zsmul m (P.T * t + d)
  have e2 : Q.x (Q.T * t + c') = Q.x (Q.T * t + d') := by
    rw [show Q.T * t + c' = Q.T * t + d' + m' • Q.T by rw [add_assoc, ← hm']]
    exact hQper.zsmul m' (Q.T * t + d')
  rw [e1, e2]
  exact ht

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P Q : ReebOrbit H)
    (hPQ : ¬ (P.T = Q.T ∧ ∃ c : ℝ, ∀ τ : ℝ, P.x τ = Q.x (τ + c))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c c' : ℝ, ∃ t : ℝ,
      δ ≤ ‖P.x (P.T * t + c) - Q.x (Q.T * t + c')‖ :=
  exists_loop_gap_of_not_shift_aux H hH P Q hPQ
