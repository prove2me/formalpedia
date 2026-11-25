-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.lemma_c_explicit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:19.834062+00:00
-- url     : https://prove2.me/submissions/990b57e8-d36e-44ab-a5e2-902448349553

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ColumnParametrizationOffDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
private theorem g4w9_prod_gt (N : ℕ) (i : Fin (N + 1)) (g : ℕ → ℝ) :
    ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), g ((j : ℕ) - i)
      = ∏ t ∈ range (N - i), g (t + 1) := by
  have hi := i.isLt
  refine Finset.prod_nbij' (fun j => (j : ℕ) - (i : ℕ) - 1)
    (fun t => if h : t + 1 + (i : ℕ) < N + 1 then (⟨t + 1 + (i : ℕ), h⟩ : Fin (N + 1)) else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    simp only [Finset.mem_range]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val,
      Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    have h : (j : ℕ) - (i : ℕ) - 1 + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.ext_iff, Fin.val_mk]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    show g ((j : ℕ) - (i : ℕ)) = g ((j : ℕ) - (i : ℕ) - 1 + 1)
    congr 1
    omega
private theorem g4w9_fact_range (a m : ℕ) :
    ((a + m).factorial : ℝ) = (a.factorial : ℝ) * ∏ t ∈ range m, ((a : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a + (m + 1) = (a + m) + 1 := by omega
    rw [e, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring
private theorem g4w9_sum_count (N : ℕ) :
    ∑ i : Fin (N + 1), (N - (i : ℕ)) = (N + 1) * N / 2 := by
  refine (Fin.sum_univ_eq_sum_range (fun i => N - i) (N + 1)).trans ?_
  have h1 : ∑ i ∈ range (N + 1), (N - i) = ∑ j ∈ range (N + 1), (N + 1 - 1 - j) :=
    Finset.sum_congr rfl (fun i _ => by omega)
  have h2 : ∑ j ∈ range (N + 1), (N + 1 - 1 - j) = ∑ j ∈ range (N + 1), j :=
    Finset.sum_range_reflect (fun i => i) (N + 1)
  show ∑ i ∈ range (N + 1), (N - i) = _
  rw [h1, h2, Finset.sum_range_id]
  simp
end Formalism.HermitianLattices.ExplicitEstimates
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : LemC_bounds := by
  intro N nu hnu
  unfold hookF
  have hd : ∀ i j : Fin (N + 1), i < j →
      (1:ℝ) ≤ ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ (nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
    intro i j hij
    have h1 := hnu (le_of_lt hij)
    have h2 : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp hij
    constructor
    · have h3 : (1:ℤ) ≤ (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
      exact_mod_cast h3
    · have h3 : (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)
          ≤ (nu i : ℤ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) := by omega
      exact_mod_cast h3
  have hper : ∀ i : Fin (N + 1),
      ((nu i).factorial : ℝ) ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
    intro i
    have hi := i.isLt
    have e1 : nu i + (N + 1) - 1 - (i : ℕ) = nu i + (N - (i : ℕ)) := by omega
    have hF : ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ)
        = ((nu i).factorial : ℝ) * ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      rw [e1]
      exact g4w9_fact_range (nu i) (N - (i : ℕ))
    have hAle : ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      calc _ ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
              ((nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)) :=
            Finset.prod_le_prod
              (fun j hj => le_trans zero_le_one (hd i j (Finset.mem_filter.mp hj).2).1)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).2)
        _ = _ := g4w9_prod_gt N i (fun x => (nu i : ℝ) + (x : ℝ))
    have hA1 : (1:ℝ) ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) := by
      calc (1:ℝ) = ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), (1:ℝ) :=
            Finset.prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).1)
    have hPle : ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ))
        ≤ ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
      have h0i : nu i ≤ nu 0 := hnu (by simp [Fin.le_iff_val_le_val])
      calc _ ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu 0 : ℝ) + N + 1) :=
            Finset.prod_le_prod (fun t _ => by positivity)
              (fun t ht => by
                have ht' := Finset.mem_range.mp ht
                have h5 : nu i + (t + 1) ≤ nu 0 + N + 1 := by omega
                exact_mod_cast h5)
        _ = _ := by rw [Finset.prod_const, Finset.card_range]
    have hApos := lt_of_lt_of_le zero_lt_one hA1
    have hfac : (0:ℝ) ≤ ((nu i).factorial : ℝ) := by positivity
    constructor
    · rw [le_div_iff₀ hApos, hF]
      exact mul_le_mul_of_nonneg_left hAle hfac
    · calc _ ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) := div_le_self (by positivity) hA1
        _ = _ := hF
        _ ≤ _ := mul_le_mul_of_nonneg_left hPle hfac
  rw [← Finset.prod_div_distrib]
  constructor
  · exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => (hper i).1)
  · calc _ ≤ ∏ i : Fin (N + 1), (((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ))) :=
          Finset.prod_le_prod (fun i _ => le_trans (by positivity) (hper i).1) (fun i _ => (hper i).2)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, g4w9_sum_count N]
end Formalism.HermitianLattices.ExplicitEstimates
