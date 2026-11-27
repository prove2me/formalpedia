-- Prove2me | solution 1 for GRH.dirichlet_zero_free_of_prime_lower_bound_in_identity_class
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:47:30.178066+00:00
-- url     : https://prove2.me/submissions/3c475eaf-b812-4a39-91d7-5c196688a2f8

import Theorems.Thm_GRH_nonnegative_mellin_logarithmic_derivative_excludes_zeros
import Theorems.Thm_GRH_identity_progression_mangoldt_series_detects_all_dirichlet_zeros
import Theorems.Thm_GRH_identity_progression_prime_weight_mellin_majorant
import Theorems.Thm_GRH_split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant

open GRH.SplitPrimeLower

theorem solution (q : ℕ) [NeZero q] (θ : ℝ) (hθ : (1/2:ℝ) ≤ θ) (hθ1 : θ<1)
    (h : squareLower q θ) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ<s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by
  obtain ⟨D,hD,h0⟩ := GRH.split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant q θ hθ h
  obtain ⟨hm,hi,hf⟩ := GRH.identity_progression_prime_weight_mellin_majorant q D θ hD hθ1
  obtain ⟨hd,hr,hprod,_⟩ := GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros q
  have hz := GRH.nonnegative_mellin_logarithmic_derivative_excludes_zeros (regularProduct q)
    (primeMajorant q D θ) D θ hd (fun s hs => hr s hs.le) (by linarith) hθ1 hm h0 hi hf
  exact fun χ s hs hp => hprod χ s hp (hz s hs)
