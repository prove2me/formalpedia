-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eq_mul_add_of_norm_le_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:00:37.878341+00:00
-- url     : https://prove2.me/submissions/5feb2584-bbf3-4a83-97a7-40191bcfe21f

import Mathlib



/-! Hryniewicz Lemma 6.25 helper: entire functions of at most linear growth are affine. -/

namespace FiniteEnergyPlane

open Metric

theorem exists_eq_mul_add_of_norm_le_mul_add_aux (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C K : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ C * ‖z‖ + K) : ∃ A B : ℂ, ∀ z, f z = A * z + B := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb' : ∀ z, ‖f z‖ ≤ C' * ‖z‖ + K := fun z =>
    (hb z).trans (by gcongr; exact le_max_left _ _)
  -- the derivative is bounded
  have hd : ∀ c : ℂ, ‖deriv f c‖ ≤ 2 * C' + |K| := by
    intro c
    have hR : (0 : ℝ) < ‖c‖ + 1 := by positivity
    have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := c) (f := f)
      (C := C' * (2 * ‖c‖ + 1) + K) hR hf.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ ≤ ‖c‖ + (‖c‖ + 1) := by
          have := norm_le_norm_add_norm_sub' z c
          rw [mem_sphere_iff_norm] at hz
          linarith
        refine (hb' z).trans ?_
        have : C' * ‖z‖ ≤ C' * (2 * ‖c‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC'0; linarith
        linarith)
    refine h1.trans ?_
    rw [div_le_iff₀ hR]
    have hK : K ≤ |K| * (‖c‖ + 1) := by
      have := le_abs_self K
      have : |K| ≤ |K| * (‖c‖ + 1) := by
        have h0 : 0 ≤ |K| * ‖c‖ := by positivity
        nlinarith
      linarith
    have hc : C' * (2 * ‖c‖ + 1) ≤ 2 * C' * (‖c‖ + 1) := by nlinarith
    nlinarith
  have hdd : Differentiable ℂ (deriv f) := fun z =>
    ((hf.differentiableOn.deriv isOpen_univ) z trivial).differentiableAt
      (isOpen_univ.mem_nhds trivial)
  have hbd : Bornology.IsBounded (Set.range (deriv f)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨_, by rintro _ ⟨c, rfl⟩; exact hd c⟩
  set A := deriv f 0
  have hconst : ∀ z, deriv f z = A := fun z => hdd.apply_eq_apply_of_bounded hbd z 0
  set g : ℂ → ℂ := fun z => f z - A * z
  have hg : Differentiable ℂ g := hf.sub ((differentiable_id.const_mul A))
  have hg' : ∀ z, deriv g z = 0 := by
    intro z
    have h1 : HasDerivAt g (deriv f z - A * 1) z :=
      (hf z).hasDerivAt.sub ((hasDerivAt_id z).const_mul A)
    rw [h1.deriv, hconst z]; ring
  refine ⟨A, g 0, fun z => ?_⟩
  have := is_const_of_deriv_eq_zero hg hg' z 0
  have e : f z = g z + A * z := by simp [g]
  rw [e, this]; ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric

theorem solution (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C K : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ C * ‖z‖ + K) : ∃ A B : ℂ, ∀ z, f z = A * z + B :=
  exists_eq_mul_add_of_norm_le_mul_add_aux f hf C K hb
