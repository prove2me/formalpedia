-- Prove2me | solution 1 for CondMat0408017.log_transmission_localization_length
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:32:10.591253+00:00
-- url     : https://prove2.me/submissions/65b0a882-c7cc-48aa-9a20-5a4c70aedb05

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (k2 : ℝ) (hk2 : 0 < k2) (t : ℝ → Ω → ℂ) (TL : ℝ → Ω → ℝ)
    (h144 : ∀ L w, TL L w = ‖1 + t L w‖ ^ 2 * Real.exp (-(L / ohmicMeanFreePath k2)))
    (hne : ∀ L, ∀ᵐ w ∂P, 1 + t L w ≠ 0)
    (hint : ∀ L, Integrable (fun w => Real.log (‖1 + t L w‖ ^ 2)) P) :
    (∀ L, ∫ w, Real.log (TL L w) ∂P =
      (∫ w, Real.log (‖1 + t L w‖ ^ 2) ∂P) - L / ohmicMeanFreePath k2) ∧
    ∀ (ℓ C : ℝ) (m : ℕ) (Ls : Fin m → ℝ), ℓ ≠ 0 → (∃ i j, Ls i ≠ Ls j) →
      (∀ i, ∫ w, Real.log (‖1 + t (Ls i) w‖ ^ 2) ∂P = C - Ls i / ℓ) →
      olsSlope Ls (fun i => ∫ w, Real.log (‖1 + t (Ls i) w‖ ^ 2) ∂P) = -(1 / ℓ) := by
  constructor
  · intro L
    have hae : (fun w => Real.log (TL L w)) =ᵐ[P]
        fun w => Real.log (‖1 + t L w‖ ^ 2) - L / ohmicMeanFreePath k2 := by
      filter_upwards [hne L] with w hw
      rw [h144 L w]
      have hpos : 0 < ‖1 + t L w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
      rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    rw [integral_congr_ae hae, integral_sub (hint L) (integrable_const _)]
    simp
  · intro ℓ C m Ls hℓ hne_ij hlin
    simp only [olsSlope]
    have hne0 : m ≠ 0 := by
      rintro rfl
      obtain ⟨i, _⟩ := hne_ij
      exact Fin.elim0 i
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne0)
    set xbar : ℝ := (∑ j : Fin m, Ls j) / (m : ℝ)
    have hybar : (∑ j : Fin m, ∫ w, Real.log (‖1 + t (Ls j) w‖ ^ 2) ∂P) / (m : ℝ) =
        C - xbar / ℓ := by
      have hsum : ∑ j : Fin m, ∫ w, Real.log (‖1 + t (Ls j) w‖ ^ 2) ∂P =
          (m : ℝ) * C - (∑ j : Fin m, Ls j) / ℓ := by
        calc ∑ j : Fin m, ∫ w, Real.log (‖1 + t (Ls j) w‖ ^ 2) ∂P
            = ∑ j : Fin m, (C - Ls j / ℓ) := Finset.sum_congr rfl (fun j _ => hlin j)
          _ = ∑ _j : Fin m, C - ∑ j : Fin m, Ls j / ℓ := Finset.sum_sub_distrib _ _
          _ = (m : ℝ) * C - (∑ j : Fin m, Ls j) / ℓ := by
              simp [Finset.sum_div]
      rw [hsum]
      simp only [xbar]
      field_simp [hm_pos.ne', hℓ]
    have hnum : ∑ i : Fin m,
        (Ls i - xbar) * ((∫ w, Real.log (‖1 + t (Ls i) w‖ ^ 2) ∂P) -
          (∑ j : Fin m, ∫ w, Real.log (‖1 + t (Ls j) w‖ ^ 2) ∂P) / (m : ℝ)) =
        -(1 / ℓ) * ∑ i : Fin m, (Ls i - xbar) ^ 2 := by
      rw [hybar, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hlin i]
      field_simp [hℓ]
      ring
    have hden_pos : 0 < ∑ i : Fin m, (Ls i - xbar) ^ 2 := by
      obtain ⟨i0, j0, hij⟩ := hne_ij
      have hex : ∃ k : Fin m, Ls k - xbar ≠ 0 := by
        by_cases h : Ls i0 - xbar = 0
        · refine ⟨j0, fun h' => hij ?_⟩
          linarith
        · exact ⟨i0, h⟩
      obtain ⟨k0, hk0⟩ := hex
      have hterm : 0 < (Ls k0 - xbar) ^ 2 := sq_pos_of_ne_zero hk0
      have hle : (Ls k0 - xbar) ^ 2 ≤ ∑ i : Fin m, (Ls i - xbar) ^ 2 :=
        Finset.single_le_sum (f := fun i => (Ls i - xbar) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ k0)
      linarith
    rw [hnum, mul_div_cancel_right₀ _ hden_pos.ne']
