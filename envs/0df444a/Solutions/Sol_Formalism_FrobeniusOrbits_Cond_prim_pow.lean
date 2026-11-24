-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.prim_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:17.869553+00:00
-- url     : https://prove2.me/submissions/929f41e0-63cb-4d97-afd4-09e73f5ddbe2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {N m : ℕ} [NeZero N] (hm : m ∣ N) : IsPrimitiveRoot (z N ^ (N / m)) m := by
  have hN : N ≠ 0 := NeZero.ne N
  exact (z_spec N).pow (Nat.pos_of_ne_zero hN) (Nat.div_mul_cancel hm).symm
end Formalism.FrobeniusOrbits.Cond
