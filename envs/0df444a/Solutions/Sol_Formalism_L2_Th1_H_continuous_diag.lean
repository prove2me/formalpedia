-- Prove2me | solution 1 for Formalism.L2.Th1.H.continuous_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:06.940705+00:00
-- url     : https://prove2.me/submissions/bdde5e4c-abfe-4487-8c72-8c76299d557a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) :
    Continuous fun z => H z z := by
  let b := Module.finBasis ℂ V
  have h : (fun z => H z z) = fun z => ∑ j, conj (b.coord j z) * H.flip (b j) z := by
    funext z
    have e : H z z = H z (∑ j, b.repr z j • b j) := by rw [b.sum_repr z]
    rw [e]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul, LinearMap.flip_apply, Module.Basis.coord_apply]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_conj.comp (LinearMap.continuous_of_finiteDimensional (b.coord j))).mul
    (LinearMap.continuous_of_finiteDimensional (H.flip (b j)))
end Formalism.L2.Th1.H
