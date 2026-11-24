-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.invariant_multiset_orbit_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.736104+00:00
-- url     : https://prove2.me/submissions/f9eac5e6-2d04-48b0-b9e9-aaae97095d2e

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Theorems.Thm_Formalism_GaloisIrreducibility_orbit_map_eq
import Theorems.Thm_Formalism_GaloisIrreducibility_orbit_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Classical
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro M' hO hle hM
  by_cases h0 : M' = 0
  · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h0
  have hxs : x ∈ ∑ i ∈ I, (O i).val := Multiset.mem_of_le hle hx
  rw [Multiset.mem_sum] at hxs
  obtain ⟨i0, hi0, hxi⟩ := hxs
  have hle0 : (O i0).val ≤ M' := orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx
  obtain ⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M'' :=
    ⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩
  have hM'' : M''.map f = M'' := by
    rw [Multiset.map_add, orbit_map_eq (hO i0 hi0)] at hM
    exact add_left_cancel hM
  have hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val := by
    rw [← Finset.add_sum_erase I _ hi0] at hle
    exact (add_le_add_iff_left _).mp hle
  obtain ⟨J, hJ, hc⟩ := ih (I.erase i0) (Finset.erase_ssubset hi0) M''
    (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''
  refine ⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩
  have hnot : i0 ∉ J := fun h => by simpa using hJ h
  rw [Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]
end Formalism.GaloisIrreducibility
