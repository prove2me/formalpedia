-- Prove2me | solution 1 for FracRiccati.Radius.Supplement.theorem_3_3_c_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:21.943895+00:00
-- url     : https://prove2.me/submissions/8f8a47a9-a911-4721-afa5-4f9612caac44

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

open FracRiccati
open FracRiccati.Radius
open FracRiccati.Radius.Supplement

open Filter Topology

/-- Geometric coefficients decrease strictly, but the boundary terms do not tend to zero. -/
theorem solution :
    (∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) 1 (1/2) k = (1/2 : ℂ) ^ k) ∧
    (∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) (-1) (1/2) k =
      (-1 : ℂ) ^ (k - 1) * (1/2 : ℂ) ^ k) ∧
    StrictAntiOn (fun k : ℕ => (coeff 1 (1/2) 1 (1/2) k).re) (Set.Ici 1) ∧
    radius 1 (coeff 1 (1/2) 1 (1/2)) = 2 ∧
    radius 1 (coeff 1 (1/2) (-1) (1/2)) = 2 ∧
    ¬ ∃ z : ℂ, Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        coeff 1 (1/2) (-1) (1/2) k * (2 : ℂ) ^ k) atTop (nhds z) := by
          have key : ∀ ε : ℂ, ε ^ 2 = 1 → ∀ n : ℕ,
              coeff 1 (1/2) ε (1/2) (n + 1) = ε ^ n * (1/2 : ℂ) ^ (n + 1) := by
            intro ε hε n
            induction n using Nat.strong_induction_on with
            | _ n ih =>
              rcases n with _ | j
              · have hG : Real.Gamma ((1:ℝ) + 1) = 1 := by
                  have h := Real.Gamma_nat_eq_factorial 1
                  simpa using h
                rw [coeff, hG]
                simp
              · have hG : Real.Gamma ((1:ℝ) * ((j + 1 : ℕ) : ℝ) + 1) /
                    Real.Gamma ((1:ℝ) * ((j + 1 : ℕ) : ℝ) + 1 + 1) = 1 / ((j : ℝ) + 2) := by
                  have hpos : (0:ℝ) < (1:ℝ) * ((j + 1 : ℕ) : ℝ) + 1 := by positivity
                  rw [Real.Gamma_add_one hpos.ne']
                  have h2 := Real.Gamma_pos_of_pos hpos
                  have h3 : (1:ℝ) * ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
                  rw [h3] at h2 ⊢
                  have h4 : (j : ℝ) + 2 ≠ 0 := by positivity
                  field_simp
                rw [coeff, hG]
                have hsum : ∑ ℓ ∈ (Finset.Ico 1 (j + 1)).attach,
                    coeff 1 (1/2) ε (1/2) ℓ.1 * coeff 1 (1/2) ε (1/2) (j + 1 - ℓ.1)
                    = (j : ℂ) * (ε ^ (j + 1) * (1/2 : ℂ) ^ (j + 1)) := by
                  have hterm : ∀ ℓ ∈ (Finset.Ico 1 (j + 1)).attach,
                      coeff 1 (1/2) ε (1/2) ℓ.1 * coeff 1 (1/2) ε (1/2) (j + 1 - ℓ.1)
                      = ε ^ (j + 1) * (1/2 : ℂ) ^ (j + 1) := by
                    rintro ⟨l, hl⟩ -
                    rw [Finset.mem_Ico] at hl
                    obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 := ⟨l - 1, by omega⟩
                    obtain ⟨q, rfl⟩ : ∃ q, j = p + q + 1 := ⟨j - p - 1, by omega⟩
                    have e : p + q + 1 + 1 - (p + 1) = q + 1 := by omega
                    simp only [e]
                    rw [ih p (by omega), ih q (by omega)]
                    calc ε ^ p * (1/2 : ℂ) ^ (p + 1) * (ε ^ q * (1/2 : ℂ) ^ (q + 1))
                        = ε ^ (p + q) * 1 * (1/2 : ℂ) ^ (p + q + 1 + 1) := by ring
                      _ = ε ^ (p + q) * ε ^ 2 * (1/2 : ℂ) ^ (p + q + 1 + 1) := by rw [hε]
                      _ = _ := by ring
                  rw [Finset.sum_congr rfl hterm]
                  simp
                rw [hsum, ih j (by omega)]
                have h5 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
                push_cast
                have h6 : ε * (ε ^ j * (1/2 : ℂ) ^ (j + 1)) = ε ^ (j + 1) * (1/2 : ℂ) ^ (j + 1) := by ring
                rw [h6, pow_succ (1/2 : ℂ) (j + 1)]
                generalize ε ^ (j + 1) = x
                generalize (1/2 : ℂ) ^ (j + 1) = y
                field_simp
                try ring
          have h1 : ∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) 1 (1/2) k = (1/2 : ℂ) ^ k := by
            intro k hk
            obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
            rw [key 1 (by norm_num) n]
            simp
          have h2 : ∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) (-1) (1/2) k =
              (-1 : ℂ) ^ (k - 1) * (1/2 : ℂ) ^ k := by
            intro k hk
            obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
            rw [key (-1) (by norm_num) n]
            simp
          have hrad : ∀ a : ℕ → ℂ, (∀ k, 1 ≤ k → ‖a k‖ = (1/2 : ℝ) ^ k) → radius 1 a = 2 := by
            intro a ha
            have hev : (fun k : ℕ => ((‖a k‖₊ : ENNReal) ^ (-(1 / ((1:ℝ) * (k : ℝ))) : ℝ)))
                =ᶠ[atTop] fun _ => (2 : ENNReal) := by
              filter_upwards [eventually_ge_atTop 1] with k hk
              have hn : (‖a k‖₊ : ENNReal) = ((2 : ENNReal)⁻¹) ^ (k : ℝ) := by
                have h : ‖a k‖₊ = ((2 : NNReal)⁻¹) ^ k := by
                  apply NNReal.eq
                  rw [coe_nnnorm, ha k hk]
                  simp
                rw [h, ENNReal.rpow_natCast]
                push_cast
                simp
              have hk0 : (k : ℝ) ≠ 0 := by
                have : k ≠ 0 := by omega
                exact_mod_cast this
              have he : (k : ℝ) * (-(1 / (1 * (k : ℝ)))) = -1 := by field_simp
              rw [hn, ← ENNReal.rpow_mul, he, ENNReal.rpow_neg_one, inv_inv]
            unfold radius
            rw [Filter.liminf_congr hev]
            exact Filter.liminf_const _
          refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
          · intro a ha b hb hab
            have hre : ∀ k : ℕ, 1 ≤ k → (coeff 1 (1/2) 1 (1/2) k).re = (1/2 : ℝ) ^ k := by
              intro k hk
              rw [h1 k hk]
              have : (1/2 : ℂ) ^ k = (((1/2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
              rw [this, Complex.ofReal_re]
            show (coeff 1 (1/2) 1 (1/2) b).re < (coeff 1 (1/2) 1 (1/2) a).re
            rw [hre a ha, hre b hb]
            exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hab
          · apply hrad
            intro k hk
            rw [h1 k hk]
            simp
          · apply hrad
            intro k hk
            rw [h2 k hk]
            simp
          · rintro ⟨z, hz⟩
            have hz' := (tendsto_add_atTop_iff_nat 1).2 hz
            have hd := (hz'.sub hz).norm
            rw [sub_self, norm_zero] at hd
            have hc : ∀ N : ℕ, ‖(∑ k ∈ Finset.Icc 1 (N + 1),
                coeff 1 (1/2) (-1) (1/2) k * (2 : ℂ) ^ k) - ∑ k ∈ Finset.Icc 1 N,
                coeff 1 (1/2) (-1) (1/2) k * (2 : ℂ) ^ k‖ = 1 := by
              intro N
              rw [Finset.sum_Icc_succ_top (by omega), add_sub_cancel_left, h2 (N + 1) (by omega)]
              rw [mul_assoc, ← mul_pow]
              simp
            simp only [hc] at hd
            exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hd)
