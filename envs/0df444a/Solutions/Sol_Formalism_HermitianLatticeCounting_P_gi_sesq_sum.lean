-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gi_sesq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:52.639944+00:00
-- url     : https://prove2.me/submissions/68fdbaf3-021d-4bbc-9106-d42b8c77b9e1

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (c : ι → ℂ) (y : ι → V) :
    h (∑ a, c a • y a) (∑ b, c b • y b) = ∑ b, ∑ a, c a * conj (c b) * h (y a) (y b) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smulₛₗ, map_smul, LinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring
end Formalism.HermitianLatticeCounting.P
