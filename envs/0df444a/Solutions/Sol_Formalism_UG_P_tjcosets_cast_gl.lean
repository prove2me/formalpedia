-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_cast_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:45.150806+00:00
-- url     : https://prove2.me/submissions/c8280072-bdef-415a-9710-c541b5cf6f8a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (q N m : ℕ) (hq : 1 ≤ q) (hm : m ≤ N) :
    ((∏ i : Fin m, (q ^ N - q ^ (i : ℕ)) : ℕ) : ℤ) =
      (q : ℤ) ^ (∑ i ∈ Finset.range m, i) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (N - i) - 1) := by
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((q ^ N - q ^ i : ℕ) : ℤ)) m,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ N := by have := Finset.mem_range.1 hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi')]
  push_cast
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
end Formalism.UG.P
