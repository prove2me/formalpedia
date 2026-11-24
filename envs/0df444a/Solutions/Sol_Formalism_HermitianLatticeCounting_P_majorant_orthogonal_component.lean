-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.majorant_orthogonal_component
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:36.726551+00:00
-- url     : https://prove2.me/submissions/fe675e03-1d7e-4e3d-a208-7f15f7ea877a

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MajorantOrthogonalComponent := by
  intro V _ _ n y a
  set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hPm : K.starProjection (y a) ∈ K := Submodule.starProjection_apply_mem _ _
  have hort : ∀ w ∈ K, inner ℂ (y a - K.starProjection (y a)) w = 0 := by
    intro w hw
    have h := Submodule.sub_starProjection_mem_orthogonal (K := K) (y a)
    rw [Submodule.mem_orthogonal'] at h; exact h _ hw
  refine ⟨y a - K.starProjection (y a), ?_, ?_, ?_, ?_⟩
  · have : y a - K.starProjection (y a) - y a = -(K.starProjection (y a)) := by abel
    rw [this]; exact K.neg_mem hPm
  · intro b hb
    exact hort _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · unfold majorantDistance
    rw [← hK, Metric.infDist_eq_iInf]
    have := (Submodule.norm_eq_iInf_iff_inner_eq_zero K (u := y a) hPm).mpr hort
    rw [this]
    exact iInf_congr fun w => (dist_eq_norm _ _).symm
  · have h1 : inner ℂ (y a - K.starProjection (y a)) (y a) =
        inner ℂ (y a - K.starProjection (y a)) (y a - K.starProjection (y a)) := by
      rw [inner_sub_right (y a - K.starProjection (y a)) (y a), hort _ hPm, sub_zero]
    rw [h1, inner_self_eq_norm_sq_to_K]; push_cast; rfl
end Formalism.HermitianLatticeCounting.P
