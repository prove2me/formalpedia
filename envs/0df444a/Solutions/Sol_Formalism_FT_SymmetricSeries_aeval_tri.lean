-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.aeval_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:49.772591+00:00
-- url     : https://prove2.me/submissions/0e33ec9b-b9f9-44dc-a953-686674c119ac

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_tri_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution {S : Type*} [CommRing S] [Algebra R S] (e h : ℕ → S) (he0 : e 0 = 1)
    (hh0 : h 0 = 1)
    (rel : ∀ k, 1 ≤ k → k ≤ n → ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∀ k, k ≤ n → MvPolynomial.aeval (fun j : Fin n => e (j + 1)) (tri R n k) = h k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rw [tri, map_one, hh0]
    · rw [tri_succ, map_sum]
      have hrel := rel (k + 1) (by omega) hk
      rw [Finset.sum_range_succ'] at hrel
      simp only [pow_zero, one_mul, he0, Nat.sub_zero] at hrel
      have hterm : ∀ i ∈ range (k + 1),
          MvPolynomial.aeval (fun j : Fin n => e (j + 1)) ((-1) ^ i * yv R n (i + 1) * tri R n (k - i)) =
            -((-1) ^ (i + 1) * e (i + 1) * h (k + 1 - (i + 1))) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [map_mul, map_mul, map_pow, map_neg, map_one, ih (k - i) (by omega) (by omega)]
        have hy : MvPolynomial.aeval (fun j : Fin n => e (j + 1)) (yv R n (i + 1)) = e (i + 1) := by
          simp only [yv]
          rw [dif_pos (by omega)]
          simp
        rw [hy, show k + 1 - (i + 1) = k - i by omega, pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
      linear_combination -hrel
end Formalism.FT.SymmetricSeries
