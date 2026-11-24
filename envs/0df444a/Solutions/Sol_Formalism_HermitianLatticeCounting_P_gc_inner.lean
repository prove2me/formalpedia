-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gc_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:42.624111+00:00
-- url     : https://prove2.me/submissions/530b8436-93e0-4960-96d8-130ade594cf8

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {l : ℕ} (y : Fin l → V) (a b : Fin l) :
    inner ℂ (y a) (y b) =
      ∑ c, conj (gramSchmidtUnitriangularMatrix y a c) * ((‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * gramSchmidtUnitriangularMatrix y b c := by
  conv_lhs => rw [gc_expand y a, gc_expand y b]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_sum, Finset.sum_eq_single c]
  · have hs : inner ℂ (gramSchmidt ℂ y c) (gramSchmidt ℂ y c) = (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [inner_smul_left, inner_smul_right, hs]
    ring
  · intro d _ hd
    rw [inner_smul_left, inner_smul_right, gramSchmidt_orthogonal ℂ y hd.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ c) h
end Formalism.HermitianLatticeCounting.P
