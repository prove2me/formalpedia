-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.lemmaB_length_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:34.368225+00:00
-- url     : https://prove2.me/submissions/f3f2475c-041f-41b8-b10e-869ddb7abe0c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.OneDimInversion
open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts
section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]
end T1
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
section Orb
end Orb
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
private lemma len_quot_pi {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] (deg : ι → ℕ) :
    Module.length R ((ι → R) ⧸
      (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
      ((∑ i, deg i : ℕ) : ℕ∞) := by
  classical
  rw [(Submodule.quotientPi (fun i => (Ideal.span {ϖ ^ deg i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R (deg i)
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
theorem _root_.solution : LemmaB'_length := by
  intro R _ _ _ ϖ hϖ ι _ deg
  exact len_quot_pi ϖ hϖ ι deg
end Formalism.HermitianLattices.RamifiedLatticeOperators
