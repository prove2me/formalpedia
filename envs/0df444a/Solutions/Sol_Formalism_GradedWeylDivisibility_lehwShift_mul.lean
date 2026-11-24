-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.041803+00:00
-- url     : https://prove2.me/submissions/03d24f00-c9f8-4c08-a2bf-78ba36d4b78f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul


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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LehwShift w P μ δ) (hQ : LehwShift w Q μ' δ) : LehwShift w (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (hP x.1).mul (hQ x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring
end Formalism.GradedWeylDivisibility
