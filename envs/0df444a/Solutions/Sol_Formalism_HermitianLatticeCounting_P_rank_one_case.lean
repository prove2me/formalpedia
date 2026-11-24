-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.rank_one_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:43.17055+00:00
-- url     : https://prove2.me/submissions/38933e05-cb78-408a-ade5-f6ad8eb1119d

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RankOne := by
  intro G H _ _ U P m hP hPU v hv hcyc v' hv'
  have h1 : ∀ g, P (U g v) = m g • v := by
    intro g
    have h1 := congrArg (fun T : H →L[ℂ] H => T v) (hPU g)
    simpa [hv] using h1
  have hle : Submodule.span ℂ (Set.range fun g => U g v) ≤ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, h1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hclosed : IsClosed (((Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := by
    have : IsClosed ((Submodule.span ℂ {v} : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
    exact this.preimage P.continuous
  have htop := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [hcyc] at htop
  have : v' ∈ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := htop trivial
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hv'] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨c, hc.symm⟩
end Formalism.HermitianLatticeCounting.P
