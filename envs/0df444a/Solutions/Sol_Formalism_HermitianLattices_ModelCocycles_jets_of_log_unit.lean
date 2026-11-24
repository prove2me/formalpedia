-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.jets_of_log_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:56.926678+00:00
-- url     : https://prove2.me/submissions/2e0bcf63-387d-4ff4-a7a3-436942a3b08c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : JetsOfLogUnit := by
  intro K _ _ R U f hU hU0 hf n hn
  have hg : ∀ n, PowerSeries.coeff n (PowerSeries.derivative K f) ∈ R := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h1 := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0,
        mul_one] at h1
      have hU' : PowerSeries.coeff n (PowerSeries.derivative K U) =
          PowerSeries.coeff (n + 1) U * ((n : K) + 1) := PowerSeries.coeff_derivative U n
      rw [hU'] at h1
      simp only [] at h1
      have h2 : PowerSeries.coeff n (PowerSeries.derivative K f) =
          PowerSeries.coeff (n + 1) U * ((n : K) + 1) -
            ∑ x ∈ range n, PowerSeries.coeff x (PowerSeries.derivative K f) *
              PowerSeries.coeff (n - x) U := by
        rw [← h1]; ring
      rw [h2]
      refine R.sub_mem (R.mul_mem (hU _) ?_) (R.sum_mem ?_)
      · exact_mod_cast natCast_mem R (n + 1)
      · intro x hx
        exact R.mul_mem (ih x (Finset.mem_range.1 hx)) (hU _)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h3 := hg k
  rw [PowerSeries.coeff_derivative] at h3
  have : ((k + 1).factorial : K) * PowerSeries.coeff (k + 1) f =
      (k.factorial : K) * (PowerSeries.coeff (k + 1) f * ((k : K) + 1)) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [this]
  exact R.mul_mem (natCast_mem R _) h3
end Formalism.HermitianLattices.ModelCocycles
