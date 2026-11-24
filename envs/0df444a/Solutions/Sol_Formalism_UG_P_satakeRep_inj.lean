-- Prove2me | solution 1 for Formalism.UG.P.satakeRep_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:19.219919+00:00
-- url     : https://prove2.me/submissions/cdfeadd2-dfb1-474f-b637-165b425965c8

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satake_subset_of_mem
import Theorems.Thm_Formalism_UG_P_satake_entry_of_mem
import Theorems.Thm_Formalism_UG_P_satakeSec_mk

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
theorem _root_.solution (π : O) (hπ : (π : L) ≠ 0) (hπO : (π : L)⁻¹ ∉ O) (j : ℕ)
    (i i' : Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes O π)
    (h : (satakeRep O π hπ j i)⁻¹ * satakeRep O π hπ j i' ∈ GLint (Fin n) O) : i = i' := by
  obtain ⟨⟨S, hS⟩, r⟩ := i
  obtain ⟨⟨S', hS'⟩, r'⟩ := i'
  have hsub : S ⊆ S' := satake_subset_of_mem O hπ hπO S S' (fun p => satakeSec O π (r p))
    (fun p => satakeSec O π (r' p)) h
  have hSS : S = S' := Finset.eq_of_subset_of_card_le hsub (hS'.trans hS.symm).le
  subst hSS
  have hr : r = r' := by
    funext p
    have h2 : (π : L)⁻¹ * (((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L)) ∈ O :=
      satake_entry_of_mem O hπ S (fun p => satakeSec O π (r p)) (fun p => satakeSec O π (r' p)) h p
    have hmem : satakeSec O π (r' p) - satakeSec O π (r p) ∈ Ideal.span {π} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      apply Subtype.ext
      show ((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L) =
        (π : L) * ((π : L)⁻¹ * (((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L)))
      rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact (satakeSec_mk O π (r p)).symm.trans
      ((Ideal.Quotient.eq.2 hmem).symm.trans (satakeSec_mk O π (r' p)))
  subst hr
  rfl
end Formalism.UG.P
