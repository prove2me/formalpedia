-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:59:09.91238+00:00
-- url     : https://prove2.me/submissions/2b0c95bb-03ba-4655-9ab2-09a5b3bf99a8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow

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
theorem _root_.solution (m N : ℕ) [NeZero m] [NeZero N] (hm : m ∣ N) : Nonempty (Cyc m →ₐ[ℚ] Cyc N) := by
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one m ℚ (Cyc m)
  exact ⟨Polynomial.IsSplittingField.lift (Cyc m) (X ^ m - 1 : ℚ[X]) (splits_pow (prim_pow hm))⟩
end Formalism.FrobeniusOrbits.Cond
