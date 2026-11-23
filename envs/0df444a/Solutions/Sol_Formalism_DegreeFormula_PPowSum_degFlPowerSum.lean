-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFlPowerSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:59.428608+00:00
-- url     : https://prove2.me/submissions/a2c01168-81b2-4461-8c3a-a5b64e2c2386

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution : DegFlPowerSum := by
  intro ι _ _ N τ k P hk
  unfold degFl
  rw [Finset.sum_mul]
  have h : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (∑ i, X (τ, i) ^ k * P).coeff (permExp σ) =
        ∑ j : Fin N, sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ) := by
    intro σ
    rw [coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm (fun i => sgnP σ * (X (τ, i) ^ k * P).coeff (permExp σ))).symm
  rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_comm,
    Finset.sum_eq_zero (fun j _ => slice τ k hk P j), mul_zero]
end Formalism.DegreeFormula.PPowSum
