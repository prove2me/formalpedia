-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:53.134265+00:00
-- url     : https://prove2.me/submissions/8d5cf487-0275-477c-b366-838a46edc42a

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_coeff_subst_congr
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_pderiv_subst_coe
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_degree_le_of_mem_antidiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {R : Type*} [CommRing R] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution (g : PowerSeries R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv R i (g.subst a) =
      (derivative R g).subst a * MvPowerSeries.pderiv R i a := by
  classical
  ext e
  have hP : ∀ k ≤ e.degree + 1,
      coeff k ((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R) = coeff k g := by
    intro k hk
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega)]
  have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i (g.subst a)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i
        (((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R).subst a)) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
      coeff_subst_congr ha _ (fun k hk => (hP k (by omega)).symm)]
  rw [h1, pderiv_subst_coe _ ha i, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxd := degree_le_of_mem_antidiagonal hx
  rw [coeff_subst_congr ha x.1 (fun k hk => ?_)]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hP (k + 1) (by omega)]
end Formalism.ELL.SubstitutionCoefficientCongruence
