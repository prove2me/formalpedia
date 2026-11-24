-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.cop_of_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:16.554141+00:00
-- url     : https://prove2.me/submissions/caf4b592-337e-40e1-a161-7a481837cdfe

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq

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
theorem _root_.solution {v n : ℕ} (h : v % n = 1 % n) : v.Coprime n := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_one_right]
end Formalism.FrobeniusOrbits.Cond
