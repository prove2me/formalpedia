-- Prove2me | solution 1 for Formalism.DivisionValues.spectral_determinant_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:22.097905+00:00
-- url     : https://prove2.me/submissions/f6ec5802-188a-4846-b373-65fa6ef9e111

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Theorems.Thm_Formalism_DivisionValues_detRatio_of_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : SpecDet := by
  unfold SpecDet
  intro K _ _ _ v D XQ XE hXQ hXE ι hι J _ d XT XW hXT hXW θ hθ Ix _ Qp Tq hind htop hindT htopT
    hdim s lam hQ hT
  obtain ⟨h1, hsum⟩ :=
    detRatio_of_scalar v XQ XE (hXQ v) ι Qp hind htop (fun p => s * ∏ j, lam j p) hQ
  have h2 : ∀ j, detRatio (XT j) (XW j) (θ j) v = ∏ p, lam j p ^ finrank K (Qp p) := by
    intro j
    obtain ⟨h, -⟩ := detRatio_of_scalar v (XT j) (XW j) (hXT j v) (θ j) (Tq j) (hindT j)
      (htopT j) (lam j) (hT j)
    rw [h]
    exact Finset.prod_congr rfl (fun p _ => by rw [hdim j p])
  rw [h1, Finset.prod_congr rfl (fun j _ => h2 j)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Finset.prod_pow]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Finset.prod_pow]
end Formalism.DivisionValues
