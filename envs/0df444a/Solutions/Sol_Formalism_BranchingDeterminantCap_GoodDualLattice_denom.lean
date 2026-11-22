-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.GoodDualLattice.denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:07.741799+00:00
-- url     : https://prove2.me/submissions/3444f37c-cde9-4583-b585-9f32084de434

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.GoodDualLattice
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
omit [IsDedekindDomain R] [StarRing K]
namespace Formalism.BranchingDeterminantCap.GoodDualLattice
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι K V) (v : V) :
    ∃ (d : R) (n : ι → R), d ≠ 0 ∧ d • v = ∑ i, n i • b i := by
  classical
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ
    (fun i => b.repr v i)
  choose a ha using fun i => RingHom.mem_rangeS.mp (hd i (Finset.mem_univ i))
  refine ⟨d, a, nonZeroDivisors.coe_ne_zero d, ?_⟩
  conv_lhs => rw [← b.sum_repr v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_assoc, ← algebraMap_smul K (a i), ha i]
end Formalism.BranchingDeterminantCap.GoodDualLattice
