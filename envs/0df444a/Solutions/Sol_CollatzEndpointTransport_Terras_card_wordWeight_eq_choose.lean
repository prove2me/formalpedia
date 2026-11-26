-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_wordWeight_eq_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:07.813615+00:00
-- url     : https://prove2.me/submissions/46fa62d2-c704-4dd4-aeba-db4c9369ea83

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H k : ℕ) :
    (Finset.univ.filter (fun v : Fin H → Bool => wordWeight v = k)).card
      = H.choose k := by
  classical
  have hbij :
      (Finset.univ.filter (fun v : Fin H → Bool => wordWeight v = k)).card
        = (Finset.powersetCard k (Finset.univ : Finset (Fin H))).card := by
    apply Finset.card_bij
      (fun v _ => Finset.univ.filter (fun i : Fin H => v i = true))
    · intro v hv
      have hw : wordWeight v = k := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hw
    · intro v _ w _ hvw
      funext i
      have hi := Finset.ext_iff.mp hvw i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hv : v i <;> cases hw : w i <;> simp [hv, hw] at hi ⊢
    · intro s hs
      have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [wordWeight] using hcard
      · ext i
        simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
end CollatzEndpointTransport.Terras
