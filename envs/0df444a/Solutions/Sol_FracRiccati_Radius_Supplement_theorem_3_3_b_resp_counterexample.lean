-- Prove2me | solution 1 for FracRiccati.Radius.Supplement.theorem_3_3_b_resp_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:44.406831+00:00
-- url     : https://prove2.me/submissions/2b066c44-4917-4d79-8e5b-efd389931077

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

open FracRiccati
open FracRiccati.Radius
open FracRiccati.Radius.Supplement

open Filter Topology

/-- Counterexample to the negative-sign blow-up and noncontinuation clauses. -/
theorem solution :
    (∀ k : ℕ, 1 ≤ k → coeff 1 (-1) (-2) (-1) k = (-1 : ℂ) ^ k) ∧
    radius 1 (coeff 1 (-1) (-2) (-1)) = 1 ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, psiReal 1 (-1) (-2) (-1) t = -t / (1 + t)) ∧
    StrictAntiOn (psiReal 1 (-1) (-2) (-1)) (Set.Ico 0 1) ∧
    Tendsto (psiReal 1 (-1) (-2) (-1)) (nhdsWithin 1 (Set.Ico 0 1)) (nhds (-1 / 2)) ∧
    (∃ f : ℝ → ℝ, ContinuousOn f (Set.Ico 0 2) ∧
      Set.EqOn f (psiReal 1 (-1) (-2) (-1)) (Set.Ico 0 1)) := by
        have hc : ∀ k : ℕ, 1 ≤ k → coeff 1 (-1) (-2) (-1) k = (-1 : ℂ) ^ k := by
          intro k
          induction k using Nat.strong_induction_on with
          | _ k ih =>
            intro hk
            match k, ih, hk with
            | 1, _, _ =>
              rw [coeff]
              have h : Real.Gamma ((1 : ℝ) + 1) = 1 := by
                rw [Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one]
              rw [h]; norm_num
            | j + 2, ih, _ =>
              rw [coeff]
              have hsum : (∑ ℓ ∈ (Finset.Ico 1 (j + 1)).attach,
                  coeff 1 (-1) (-2) (-1) ℓ.1 * coeff 1 (-1) (-2) (-1) (j + 1 - ℓ.1))
                  = (j : ℂ) * (-1 : ℂ) ^ (j + 1) := by
                have h1 : ∀ ℓ ∈ (Finset.Ico 1 (j + 1)).attach,
                    coeff 1 (-1) (-2) (-1) ℓ.1 * coeff 1 (-1) (-2) (-1) (j + 1 - ℓ.1)
                    = (-1 : ℂ) ^ (j + 1) := by
                  intro ℓ _
                  have hl := Finset.mem_Ico.mp ℓ.2
                  rw [ih ℓ.1 (by omega) (by omega), ih (j + 1 - ℓ.1) (by omega) (by omega),
                    ← pow_add]
                  congr 1
                  omega
                rw [Finset.sum_congr rfl h1]
                simp
              rw [hsum, ih (j + 1) (by omega) (by omega)]
              have hpos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
              have hg : Real.Gamma ((1 : ℝ) * ((j + 1 : ℕ) : ℝ) + 1) /
                  Real.Gamma ((1 : ℝ) * ((j + 1 : ℕ) : ℝ) + 1 + 1) = 1 / ((j : ℝ) + 2) := by
                have hne : (1 : ℝ) * ((j + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
                have hG : Real.Gamma ((1 : ℝ) * ((j + 1 : ℕ) : ℝ) + 1) ≠ 0 :=
                  (Real.Gamma_pos_of_pos (by positivity)).ne'
                rw [Real.Gamma_add_one hne]
                have e : (1 : ℝ) * ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
                rw [e] at hG ⊢
                field_simp
              rw [hg]
              have hne : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast hpos.ne'
              push_cast
              field_simp
              ring
        have hr : radius 1 (coeff 1 (-1) (-2) (-1)) = 1 := by
          unfold radius
          have h : (fun k : ℕ => ((‖coeff 1 (-1) (-2) (-1) k‖₊ : ENNReal) ^
              (-(1 / ((1 : ℝ) * (k : ℝ))) : ℝ))) =ᶠ[atTop] fun _ => (1 : ENNReal) := by
            filter_upwards [eventually_ge_atTop 1] with k hk
            rw [hc k hk]
            simp
          rw [Filter.liminf_congr h]
          simp
        have hp : ∀ t ∈ Set.Ico (0 : ℝ) 1, psiReal 1 (-1) (-2) (-1) t = -t / (1 + t) := by
          intro t ht
          have ht0 := ht.1
          have ht1 := ht.2
          have hs : HasSum (fun k : ℕ => (-t) ^ k) (1 - (-t))⁻¹ :=
            hasSum_geometric_of_abs_lt_one (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1)
          have hs2 : HasSum (fun k : ℕ => (-t) ^ (k + 1)) (-t / (1 + t)) := by
            have h := hs.mul_left (-t)
            have e1 : (fun k : ℕ => -t * (-t) ^ k) = fun k : ℕ => (-t) ^ (k + 1) := by
              funext k; ring
            have e2 : -t * (1 - (-t))⁻¹ = -t / (1 + t) := by
              rw [sub_neg_eq_add, div_eq_mul_inv]
            rw [e1, e2] at h
            exact h
          have hs3 : HasSum (fun k : ℕ => coeff 1 (-1) (-2) (-1) k * ((t ^ ((1 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (((-t / (1 + t) : ℝ)) : ℂ) := by
            rw [← hasSum_nat_add_iff' 1]
            have h0 : coeff 1 (-1) (-2) (-1) 0 = 0 := by rw [coeff]
            simp only [Finset.sum_range_one, h0, zero_mul, sub_zero]
            have h := Complex.hasSum_ofReal.mpr hs2
            have e : (fun k : ℕ => coeff 1 (-1) (-2) (-1) (k + 1) *
                ((t ^ ((1 : ℝ) * ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) =
                fun k : ℕ => (((-t) ^ (k + 1) : ℝ) : ℂ) := by
              funext k
              rw [hc (k + 1) (by omega), one_mul, Real.rpow_natCast]
              push_cast
              rw [neg_pow (t : ℂ)]
            rw [e]
            exact h
          have n1 : ((-1 : ℝ) : ℂ) = -1 := by push_cast; rfl
          have n2 : ((-2 : ℝ) : ℂ) = -2 := by push_cast; rfl
          unfold psiReal psi
          rw [n1, n2, hs3.tsum_eq, Complex.ofReal_re]
        have hcont : ContinuousOn (fun t : ℝ => -t / (1 + t)) (Set.Ici 0) := by
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          have hx' : (0 : ℝ) ≤ x := hx
          positivity
        refine ⟨hc, hr, hp, ?_, ?_, fun t => -t / (1 + t), hcont.mono fun x hx => hx.1,
          fun t ht => (hp t ht).symm⟩
        · intro x hx y hy hxy
          rw [hp x hx, hp y hy]
          have := hx.1
          have := hy.1
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        · have h1 : Tendsto (fun t : ℝ => -t / (1 + t)) (nhdsWithin 1 (Set.Ico 0 1)) (nhds (-1 / 2)) := by
            have h := (hcont 1 (by simp : (1 : ℝ) ∈ Set.Ici 0)).mono_left
              (nhdsWithin_mono 1 (fun x hx => hx.1 : Set.Ico (0 : ℝ) 1 ⊆ Set.Ici 0))
            have e : (-(1 : ℝ) / (1 + 1)) = -1 / 2 := by norm_num
            simp only [e] at h
            exact h
          refine h1.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (hp t ht).symm
