-- Prove2me | solution 1 for Formalism.UG.P.satake_exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:46.35263+00:00
-- url     : https://prove2.me/submissions/5e8fc845-cc88-45fb-a05b-9be45b4c3317

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, a ∈ S ↔ ((σ a : Fin n) : ℕ) < S.card := by
  have hk : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  let e : {a // a ∈ S} ≃ {i : Fin n // (i : ℕ) < S.card} := S.equivFin.trans (Fin.castLEquiv hk)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  by_cases ha : a ∈ S
  · exact iff_of_true ha (e.extendSubtype_mem a ha)
  · exact iff_of_false ha (e.extendSubtype_not_mem a ha)
end Formalism.UG.P
