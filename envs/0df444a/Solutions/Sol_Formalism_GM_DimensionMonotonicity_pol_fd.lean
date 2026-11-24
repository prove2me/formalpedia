-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.pol_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:42.909317+00:00
-- url     : https://prove2.me/submissions/5f5b595b-2e39-4783-99b9-8371e87b12f4

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) : FiniteDimensional ℚ_[p] (Pol p r LL) := by
  haveI := FiniteDimensional.span_of_finite ℚ_[p]
    ((pol_finite (r := r) LL).image (fun m => monomial m (1 : ℚ_[p])))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[p] ((fun m => monomial m (1 : ℚ_[p])) '' {m : Fin N × Fin r →₀ ℕ | MultiDeg LL m})) ?_
  intro x hx
  unfold Pol at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [show monomial m (coeff m x) = coeff m x • monomial m (1 : ℚ_[p]) by rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hx hm, rfl⟩)
end Formalism.GM.DimensionMonotonicity
