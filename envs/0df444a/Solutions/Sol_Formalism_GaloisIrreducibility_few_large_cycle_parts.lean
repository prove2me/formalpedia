-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.few_large_cycle_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:24.997839+00:00
-- url     : https://prove2.me/submissions/bc6927e9-10c9-445d-859f-03aa0b299dd1

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts
import Theorems.Thm_Formalism_GaloisIrreducibility_prod_lpart_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : FewLargeParts := by
  intro n B S hn hB hS hne hlarge
  have hdvd := prod_lpart_dvd n S hS
  have hle : (∏ l ∈ S, l ^ padicValNat l n) ≤ n := Nat.le_of_dvd (by omega) hdvd
  calc B ^ S.card = ∏ _l ∈ S, B := by rw [Finset.prod_const]
    _ < ∏ l ∈ S, ((l ^ padicValNat l n : ℕ) : ℝ) :=
        Finset.prod_lt_prod_of_nonempty (fun _ _ => hB) hlarge hne
    _ = ((∏ l ∈ S, l ^ padicValNat l n : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ n := by exact_mod_cast hle
end Formalism.GaloisIrreducibility
