-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lOneNorm_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:32.683082+00:00
-- url     : https://prove2.me/submissions/611d07a0-882d-4147-9d3e-f0ad8ae3b4ab

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {P κ : Type} (s : Finset κ) (x : κ → P →₀ ℂ) :
    lOneNorm (∑ i ∈ s, x i) ≤ ∑ i ∈ s, lOneNorm (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lOneNorm]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (lOneNorm_add_le _ _).trans (add_le_add le_rfl ih)
end Formalism.HermitianLatticeCounting.P
