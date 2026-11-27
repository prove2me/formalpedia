-- Prove2me | solution 1 for DataDrivenRO.Guarantee.Supplement.theorem_8_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:16.902562+00:00
-- url     : https://prove2.me/submissions/0d7cb8d8-9afd-457f-b041-5b6eb197c79b

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Supplement_LCX

open MeasureTheory
open scoped ENNReal

open DataDrivenRO
open DataDrivenRO.Guarantee
open DataDrivenRO.Guarantee.Supplement

/-- Theorem 8 is false for the set (31) as printed. The confidence region covers the
true law with probability one, but the simultaneous guarantee fails with probability
at least 1/4. The fixed sample zero also contradicts the support/worst-VaR equality. -/
theorem solution :
    let P : Measure (Fin 1 → ℝ) :=
      (1 / 4 : ℝ≥0∞) • Measure.dirac (fun _ => 0) +
      (3 / 4 : ℝ≥0∞) • Measure.dirac (fun _ => (4 / 3 : ℝ))
    let S0 : Fin 1 → (Fin 1 → ℝ) := fun _ _ => 0
    let U := ULCXPrinted S0 1 (1 / 2)
    IsProbabilityMeasure P ∧
    P ∈ regionLCX S0 1 1 ∧
    U = {u | -(1 : ℝ) ≤ u 0 ∧ u 0 ≤ 1} ∧
    U.Nonempty ∧ IsCompact U ∧ Convex ℝ U ∧
    RobustMDP.Shared.supportFunction U (fun _ => 1) = 1 ∧
    DataDrivenRO.Guarantee.VaR P (1 / 2) (fun _ => 1) = 4 / 3 ∧
    ¬ DataDrivenRO.Guarantee.ImpliesGuarantee P U (1 / 2) ∧
    (Measure.pi (fun _ : Fin 1 => P)) {S | P ∈ regionLCX S 1 1} = 1 ∧
    (Measure.pi (fun _ : Fin 1 => P))
      {S | DataDrivenRO.Guarantee.SimultaneouslyImpliesGuarantee P
        (fun ε => ULCXPrinted S 1 ε)} ≤ (3 / 4 : ℝ≥0∞) := by
          intro P S0 U
          have h14 : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
          have h34 : (3 / 4 : ℝ≥0∞) = ENNReal.ofReal (3 / 4) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
          have h1 : ENNReal.ofReal (1 / 4) + ENNReal.ofReal (3 / 4) = 1 := by
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
          have hPA : ∀ A : Set (Fin 1 → ℝ), P A =
              ENNReal.ofReal (1 / 4) * A.indicator 1 (fun _ => (0 : ℝ)) +
              ENNReal.ofReal (3 / 4) * A.indicator 1 (fun _ => (4 / 3 : ℝ)) := by
            intro A
            simp only [P, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, h14, h34]
          have hPint : ∀ g : (Fin 1 → ℝ) → ℝ, (∀ u, 0 ≤ g u) →
              ∫⁻ u, ENNReal.ofReal (g u) ∂P =
                ENNReal.ofReal (1 / 4 * g (fun _ => 0) + 3 / 4 * g (fun _ => 4 / 3)) := by
            intro g hg
            have e1 := hg (fun _ => 0)
            have e2 := hg (fun _ => 4 / 3)
            simp only [P, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
              h14, h34]
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          have hprob : IsProbabilityMeasure P := by
            refine ⟨?_⟩
            rw [hPA]
            simpa using h1
          have htests : ∀ ab ∈ tests 1, |ab.1 0| + |ab.2| ≤ 1 := by
            intro ab hab
            simpa [tests] using hab
          have hregion : ∀ S : Fin 1 → (Fin 1 → ℝ), (S 0 0) ^ 2 - 1 ≤ 4 / 3 →
              P ∈ regionLCX S 1 1 := by
            intro S hS
            refine ⟨hprob, ?_, ?_⟩
            · intro ab hab
              have hb := htests ab hab
              rw [hPint _ (fun u => le_max_right _ _)]
              apply ENNReal.ofReal_le_ofReal
              simp only [gammaLCX, dotProduct, Fin.sum_univ_one, Nat.cast_one, div_one]
              have k0 : 0 ≤ max (S 0 0 * ab.1 0 - ab.2) 0 := le_max_right _ _
              have ha1 := le_abs_self (ab.1 0)
              have hb1 := neg_abs_le ab.2
              have ha0 := abs_nonneg (ab.1 0)
              have hb0 := abs_nonneg ab.2
              have k1 : max (0 * ab.1 0 - ab.2) 0 ≤ |ab.2| :=
                max_le (by linarith) hb0
              have k2 : max (4 / 3 * ab.1 0 - ab.2) 0 ≤ 4 / 3 * |ab.1 0| + |ab.2| :=
                max_le (by linarith) (by linarith)
              linarith
            · rw [hPint _ (fun u => Finset.sum_nonneg (fun i _ => sq_nonneg _))]
              apply ENNReal.ofReal_le_ofReal
              simp only [Fin.sum_univ_one, Nat.cast_one, div_one]
              linarith
          have hU : U = {u | -(1 : ℝ) ≤ u 0 ∧ u 0 ≤ 1} := by
            ext u
            simp only [U, ULCXPrinted, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨r, z, hz1, hz2, h⟩
              have p1 := h (fun _ => 1, 0) (by simp [tests])
              have p2 := h (fun _ => -1, 0) (by simp [tests])
              simp only [S0, dotProduct, Fin.sum_univ_one, Nat.cast_one, div_one, zero_mul, sub_zero,
                max_self, mul_zero, zero_add] at p1 p2
              have q1 := le_max_right (r 0 * 1) 0
              have q2 := le_max_right (r 0 * -1) 0
              have q3 := le_max_left (u 0 * 1) 0
              have q4 := le_max_left (u 0 * -1) 0
              constructor <;> linarith
            · rintro ⟨hl, hr⟩
              refine ⟨fun _ => 0, 1, le_rfl, by norm_num, ?_⟩
              intro ab hab
              have hb := htests ab hab
              simp only [S0, dotProduct, Fin.sum_univ_one, Nat.cast_one, div_one, zero_mul, sub_self,
                max_self, mul_zero, zero_add, one_mul]
              have k0 : 0 ≤ max (0 - ab.2) 0 := le_max_right _ _
              have hb1 := neg_abs_le ab.2
              have k3 : u 0 * ab.1 0 ≤ |ab.1 0| := by
                have hu : |u 0| ≤ 1 := abs_le.2 ⟨hl, hr⟩
                calc u 0 * ab.1 0 ≤ |u 0 * ab.1 0| := le_abs_self _
                  _ = |u 0| * |ab.1 0| := abs_mul _ _
                  _ ≤ 1 * |ab.1 0| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
                  _ = _ := one_mul _
              have k2 : max (u 0 * ab.1 0 - ab.2) 0 ≤ 1 := max_le (by linarith) (by norm_num)
              linarith
          have hUpi : U = Set.univ.pi (fun _ : Fin 1 => Set.Icc (-1 : ℝ) 1) := by
            rw [hU]; ext u; simp [-Set.pi_univ_Icc, Set.mem_pi]
          have hnot : ¬ DataDrivenRO.Guarantee.ImpliesGuarantee P U (1 / 2) := by
            intro h
            have h2 := h 0 (fun u _ => u 0 - 1) (by
              intro x
              refine ⟨convex_univ, ?_⟩
              intro a _ b _ s t _ _ hst
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              apply le_of_eq
              linear_combination -hst) (fun _ => 0) (by
              intro u hu
              rw [hU] at hu
              have := hu.2
              linarith)
            rw [hPA] at h2
            have e1 : ({u : Fin 1 → ℝ | u 0 - 1 ≤ 0}.indicator (1 : (Fin 1 → ℝ) → ℝ≥0∞)
                (fun _ => (0 : ℝ))) = 1 := by
              rw [Set.indicator_of_mem]
              · rfl
              · simp
            have e2 : ({u : Fin 1 → ℝ | u 0 - 1 ≤ 0}.indicator (1 : (Fin 1 → ℝ) → ℝ≥0∞)
                (fun _ => (4 / 3 : ℝ))) = 0 := by
              rw [Set.indicator_of_notMem]
              simp only [Set.mem_ofPred_eq]; norm_num
            rw [e1, e2, mul_one, mul_zero, add_zero, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
            norm_num at h2
          refine ⟨hprob, hregion S0 (by simp [S0]; norm_num), hU, ?_, ?_, ?_, ?_, ?_, hnot, ?_, ?_⟩
          · rw [hU]; exact ⟨fun _ => 0, by simp⟩
          · rw [hUpi]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
          · rw [hUpi]; exact convex_pi (fun _ _ => convex_Icc _ _)
          · have himg : (fun p : Fin 1 → ℝ => ∑ j, p j * (1 : ℝ)) '' U = Set.Icc (-1) 1 := by
              rw [hU]; ext y
              simp only [Fin.sum_univ_one, mul_one, Set.mem_image, Set.mem_ofPred_eq, Set.mem_Icc]
              constructor
              · rintro ⟨u, hu, rfl⟩; exact hu
              · intro hy; exact ⟨fun _ => y, hy, rfl⟩
            have : RobustMDP.Shared.supportFunction U (fun _ => 1) = sSup (Set.Icc (-1 : ℝ) 1) := by
              unfold RobustMDP.Shared.supportFunction
              rw [himg]
            rw [this, csSup_Icc (by norm_num)]
          · have hset : {y : ℝ | ENNReal.ofReal (1 - 1 / 2) ≤
                P {u : Fin 1 → ℝ | u ⬝ᵥ (fun _ => (1 : ℝ)) ≤ y}} = Set.Ici (4 / 3) := by
              ext y
              simp only [Set.mem_ofPred_eq, Set.mem_Ici, dotProduct, Fin.sum_univ_one, mul_one]
              rw [hPA]
              by_cases hy : 4 / 3 ≤ y
              · have e1 : ({u : Fin 1 → ℝ | u 0 ≤ y}.indicator (1 : (Fin 1 → ℝ) → ℝ≥0∞)
                    (fun _ => (0 : ℝ))) = 1 := by
                  rw [Set.indicator_of_mem]
                  · rfl
                  · simp only [Set.mem_ofPred_eq]; linarith
                have e2 : ({u : Fin 1 → ℝ | u 0 ≤ y}.indicator (1 : (Fin 1 → ℝ) → ℝ≥0∞)
                    (fun _ => (4 / 3 : ℝ))) = 1 := by
                  rw [Set.indicator_of_mem]
                  · rfl
                  · simp only [Set.mem_ofPred_eq]; linarith
                rw [e1, e2, mul_one, mul_one, h1]
                simp only [hy, iff_true]
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (by norm_num)
              · have e2 : ({u : Fin 1 → ℝ | u 0 ≤ y}.indicator (1 : (Fin 1 → ℝ) → ℝ≥0∞)
                    (fun _ => (4 / 3 : ℝ))) = 0 := by
                  rw [Set.indicator_of_notMem]
                  exact hy
                rw [e2, mul_zero, add_zero]
                simp only [hy, iff_false, not_le]
                calc _ ≤ ENNReal.ofReal (1 / 4) * 1 := by
                        gcongr
                        exact Set.indicator_le_self' (fun _ _ => zero_le) _
                  _ = ENNReal.ofReal (1 / 4) := mul_one _
                  _ < _ := by
                        rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
            unfold DataDrivenRO.Guarantee.VaR MultistageStochastic.valueAtRisk
            rw [hset, csInf_Ici]
          · apply le_antisymm prob_le_one
            have hA : P {u : Fin 1 → ℝ | (u 0) ^ 2 - 1 ≤ 4 / 3} = 1 := by
              rw [hPA, Set.indicator_of_mem, Set.indicator_of_mem]
              · simpa using h1
              · simp only [Set.mem_ofPred_eq]; norm_num
              · simp only [Set.mem_ofPred_eq]; norm_num
            calc (1 : ℝ≥0∞) = (Measure.pi (fun _ : Fin 1 => P))
                  (Set.univ.pi (fun _ => {u : Fin 1 → ℝ | (u 0) ^ 2 - 1 ≤ 4 / 3})) := by
                    rw [Measure.pi_pi, Fin.prod_univ_one, hA]
              _ ≤ _ := by
                    apply measure_mono
                    intro S hS
                    exact hregion S (hS 0 (Set.mem_univ _))
          · have hA : P ({fun _ => (0 : ℝ)}ᶜ : Set (Fin 1 → ℝ)) ≤ (3 / 4 : ℝ≥0∞) := by
              rw [hPA, Set.indicator_of_notMem (by simp), mul_zero, zero_add, h34]
              calc _ ≤ ENNReal.ofReal (3 / 4) * 1 := by
                        gcongr
                        exact Set.indicator_le_self' (fun _ _ => zero_le) _
                _ = _ := mul_one _
            calc _ ≤ (Measure.pi (fun _ : Fin 1 => P))
                  (Set.univ.pi (fun _ => ({fun _ => (0 : ℝ)}ᶜ : Set (Fin 1 → ℝ)))) := by
                    apply measure_mono
                    intro S hS i _ hi
                    apply hnot
                    have hSS : S = S0 := by
                      funext j
                      have : j = i := Subsingleton.elim _ _
                      rw [this]
                      exact hi
                    have := hS (1 / 2) ⟨by norm_num, by norm_num⟩
                    rw [hSS] at this
                    exact this
              _ = P ({fun _ => (0 : ℝ)}ᶜ : Set (Fin 1 → ℝ)) := by
                    rw [Measure.pi_pi, Fin.prod_univ_one]
              _ ≤ _ := hA
