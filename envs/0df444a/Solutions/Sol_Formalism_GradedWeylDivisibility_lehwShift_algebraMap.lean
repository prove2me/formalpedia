-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:22.31231+00:00
-- url     : https://prove2.me/submissions/565721b0-7099-4f60-9339-a50fac2f0f05

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (c : R) (δ : ℤ) :
    LehwShift w (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  have h1 := lehwShift_one (R := R) w δ k
  rw [Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1))
end Formalism.GradedWeylDivisibility
