-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_K_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:42.023817+00:00
-- url     : https://prove2.me/submissions/23eb5a33-a631-478e-9316-8a6a38ff2ef8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (k : GU σ n) (hk : k ∈ KU σ n) :
    fIwasawaInt (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  intro i j
  have h1 := Subgroup.mem_subgroupOf.1 hk
  obtain ⟨k', hk'⟩ := (Subgroup.mem_inf.1 h1).2
  rw [← hk']
  show Valued.v (((k' : Matrix (Fin n) (Fin n) (intL L)) i j : intL L) : L) ≤ 1
  exact (k' i j).2
end Formalism.UG.P
