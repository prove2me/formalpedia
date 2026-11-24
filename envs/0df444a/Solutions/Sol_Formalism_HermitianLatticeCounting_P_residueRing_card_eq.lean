-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.residueRing_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:09.52079+00:00
-- url     : https://prove2.me/submissions/dd942055-3d9a-499f-93b8-f4522ece5574

import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLattice
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_FlagKernelVanishing
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open MeasureTheory NumberField Matrix
open scoped InnerProductSpace
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.ResidueRingCard := by
  intro E _ _ g
  have h1 : Ideal.absNorm (Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E := by
    rw [Ideal.absNorm_span_singleton]
    have : (g : 𝓞 E) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  rw [← h1]
  rfl
end Formalism.HermitianLatticeCounting.P
