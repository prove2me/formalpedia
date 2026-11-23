-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.coeff_subst_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:23.757808+00:00
-- url     : https://prove2.me/submissions/d67d0bb4-d1d1-44cd-abca-416e2847c10d

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_prod_X_pow
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_hasSubst_X_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0)
    (F : MvPowerSeries (Fin r) k) (m : ℕ) :
    PowerSeries.coeff m
        (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) F : PowerSeries k) =
      finsum (fun d => if weight n d = m then MvPowerSeries.coeff d F else 0) := by
  change MvPowerSeries.coeff (Finsupp.single () m) _ = _
  rw [MvPowerSeries.coeff_subst (hasSubst_X_pow n hn)]
  congr 1
  ext d
  rw [prod_X_pow, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases h : weight n d = m
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
end Formalism.CyclotomicNorms.SubstitutionExponents
