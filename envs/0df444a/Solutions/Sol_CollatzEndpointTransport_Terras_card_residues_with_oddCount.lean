-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:44.64904+00:00
-- url     : https://prove2.me/submissions/29e8eec4-9142-46ae-99c9-1de811b59305

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_wordWeight
import Theorems.Thm_CollatzEndpointTransport_Terras_card_wordWeight_eq_choose

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H k : ℕ) :
    (Finset.univ.filter
      (fun x : Fin (2 ^ H) => oddCount H (x : ℕ) = k)).card = H.choose k := by
  classical
  have hcard :
      (Finset.univ.filter
        (fun x : Fin (2 ^ H) => oddCount H (x : ℕ) = k)).card =
      (Finset.univ.filter
        (fun v : Fin H → Bool => wordWeight v = k)).card := by
    apply Finset.card_bij (fun x _ => terrasMap H x)
    · intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change oddCount H (x : ℕ) = k
      exact (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact terrasMap_injective H hxy
    · intro v hv
      obtain ⟨x, hx⟩ := (terrasMap_bijective H).2 v
      refine ⟨x, ?_, hx⟩
      have hw : wordWeight v = k := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [oddCount_eq_wordWeight, show parityVec H (x : ℕ) = v from hx]
      exact hw
  rw [hcard, card_wordWeight_eq_choose]
end CollatzEndpointTransport.Terras
