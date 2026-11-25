-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:03.880951+00:00
-- url     : https://prove2.me/submissions/4c2c68cf-1d10-4b1f-8e89-776217894b4a

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_run
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_invol
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {α : Type} (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (t : Fin N → α)
    (ht : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j) (i : Fin N) :
    t (τ i) = t i := by
  have inv := desc_invol τ h
  have main : ∀ i : Fin N, i < τ i → t (τ i) = t i := by
    intro i hi
    have hi' : (i : ℕ) < τ i := hi
    have hr := desc_run τ h ((τ i : ℕ) - i) i (τ i) (by omega) (by rw [inv]; exact hi)
    have step : ∀ d : ℕ, ∀ m : Fin N, (m : ℕ) = i + d → m ≤ τ i → t m = t i := by
      intro d
      induction d with
      | zero => intro m hm _; rw [show m = i from Fin.ext (by omega)]
      | succ d ih =>
        intro m hm hle
        have hle' : (m : ℕ) ≤ τ i := hle
        have hm1 : (i : ℕ) + d < N := by have := m.2; omega
        set m1 : Fin N := ⟨i + d, hm1⟩ with hm1def
        have hm1v : (m1 : ℕ) = i + d := rfl
        have e1 := hr m1 (by show (i : ℕ) ≤ m1; omega) (by show (m1 : ℕ) ≤ τ i; omega)
        have e2 := hr m (by show (i : ℕ) ≤ m; omega) hle
        rw [← ih m1 hm1v (by show (m1 : ℕ) ≤ τ i; omega)]
        exact (ht m1 m (by omega) (by show (τ m : ℕ) < τ m1; omega)).symm
    exact step ((τ i : ℕ) - i) (τ i) (by omega) le_rfl
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have := main (τ i) (by rw [inv]; exact hc)
    rw [inv] at this
    exact this.symm
  · rw [hc]
  · exact main i hc
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
