-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.third_zeta_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:54.714986+00:00
-- url     : https://prove2.me/submissions/66453f1f-33ba-425f-bf2b-fb8e982a89fd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HookRowProductEqFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma weyl_factor_bounds {n : ℕ} (lam : Fin (n + 1) → ℤ) (h : Antitone lam) (i j : Fin (n + 1))
    (hij : i < j) :
    1 ≤ (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ∧
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      ≤ (Wnum lam : ℝ) := by
  have hij' : ((i:ℕ):ℝ) + 1 ≤ ((j:ℕ):ℝ) := by exact_mod_cast hij
  have hd : (0:ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
  have h1 : (lam j : ℝ) ≤ lam i := by exact_mod_cast h hij.le
  have h2 : (lam i : ℝ) ≤ lam 0 := by exact_mod_cast h (Fin.zero_le i)
  have h3 : (lam (Fin.last n) : ℝ) ≤ lam j := by exact_mod_cast h (Fin.le_last j)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  constructor
  · rw [le_div_iff₀ hd]; push_cast; linarith
  · rw [div_le_iff₀ hd]; unfold Wnum; push_cast
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (lam 0 : ℝ) - lam (Fin.last n))
      (by linarith : (0:ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) - 1),
      mul_nonneg hn0 hd.le]
private lemma one_le_weyl_numerator {n : ℕ} (lam : Fin (n + 1) → ℤ) (h : Antitone lam) :
    (1:ℝ) ≤ (Wnum lam : ℝ) := by
  have h2 : (lam (Fin.last n) : ℝ) ≤ lam 0 := by exact_mod_cast h (Fin.zero_le _)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  unfold Wnum; push_cast; linarith
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : WeylDimensionBounds := by
  intro n lam h
  have hW := one_le_weyl_numerator lam h
  have hlow : 1 ≤ weylDim lam := by
    unfold weylDim
    calc (1:ℝ) = ∏ i : Fin (n + 1), ∏ j ∈ univ.filter (fun j => i < j), (1:ℝ) := by simp
      _ ≤ _ := by
        refine Finset.prod_le_prod (fun i _ => by simp) fun i _ => ?_
        refine Finset.prod_le_prod (fun j _ => zero_le_one) fun j hj => ?_
        exact (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
  refine ⟨hlow, ?_⟩
  have hup : weylDim lam ≤ (Wnum lam : ℝ) ^ ((n + 1) * (n + 1)) := by
    unfold weylDim
    calc _ ≤ ∏ _i : Fin (n + 1), (Wnum lam : ℝ) ^ (n + 1) := by
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => ?_) fun i _ => ?_
          · exact le_trans zero_le_one (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
          · calc _ ≤ ∏ j ∈ univ.filter (fun j => i < j), (Wnum lam : ℝ) := by
                  refine Finset.prod_le_prod (fun j hj => ?_) fun j hj => ?_
                  · exact le_trans zero_le_one (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
                  · exact (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).2
              _ = (Wnum lam : ℝ) ^ (univ.filter (fun j => i < j)).card := by simp
              _ ≤ (Wnum lam : ℝ) ^ (n + 1) := by
                  refine pow_le_pow_right₀ hW ?_
                  calc _ ≤ (univ : Finset (Fin (n + 1))).card := Finset.card_filter_le _ _
                    _ = n + 1 := by simp
      _ = _ := by simp [pow_mul]
  calc Real.log (weylDim lam) ≤ Real.log ((Wnum lam : ℝ) ^ ((n + 1) * (n + 1))) :=
        Real.log_le_log (by linarith) hup
    _ = _ := by rw [Real.log_pow]; push_cast; ring
end Formalism.HermitianLattices.TraceIntegrality
