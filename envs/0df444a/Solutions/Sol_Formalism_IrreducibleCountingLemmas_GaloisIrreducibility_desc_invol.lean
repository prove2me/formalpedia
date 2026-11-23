-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_invol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:53.392894+00:00
-- url     : https://prove2.me/submissions/506a2c5d-6b55-4142-b2c2-dcdb9b714777

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_run

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
theorem _root_.solution (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (i : Fin N) :
    τ (τ i) = i := by
  have run := desc_run τ h
  have run' : ∀ i j : Fin N, i < j → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    exact run (j - i) i j (by omega)
  obtain ⟨j0, hj0⟩ := τ.surjective i
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := run' j0 i h1 (by rw [hj0]; exact hc) i h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]
    · exfalso
      have hp : ∃ p, p < i ∧ i < τ p := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Iio i, τ p ∈ (Finset.Iio i).erase (τ i) := by
          intro p hp
          have hp' : p < i := Finset.mem_Iio.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_lt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Iio.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Iio.mpr hc)] at hcard
        have : 0 < (Finset.Iio i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Iio.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' p j0 (lt_trans hp1 h1) (by rw [hj0]; exact hp2)
      have e1 := hr i hp1.le h1.le
      have e2 := hr j0 (lt_trans hp1 h1).le le_rfl
      rw [hj0] at e2
      have hc' : (τ i : ℕ) < i := hc
      have h1' : (i : ℕ) < j0 := h1
      omega
  · rw [hc, hc]
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exfalso
      have hp : ∃ p, i < p ∧ τ p < i := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Ioi i, τ p ∈ (Finset.Ioi i).erase (τ i) := by
          intro p hp
          have hp' : i < p := Finset.mem_Ioi.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_gt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Ioi.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [← this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Ioi.mpr hc)] at hcard
        have : 0 < (Finset.Ioi i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Ioi.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' j0 p (lt_trans h1 hp1) (by rw [hj0]; exact hp2)
      have e1 := hr i h1.le hp1.le
      rw [hj0] at e1
      have hc' : (i : ℕ) < τ i := hc
      have h1' : (j0 : ℕ) < i := h1
      omega
    · have := run' i j0 h1 (by rw [hj0]; exact hc) j0 h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
