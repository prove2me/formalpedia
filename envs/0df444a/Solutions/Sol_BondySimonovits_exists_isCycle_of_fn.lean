-- Prove2me | solution 1 for BondySimonovits.exists_isCycle_of_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:38.99984+00:00
-- url     : https://prove2.me/submissions/e7eafef5-d60e-4296-b44f-98de2407d5d3

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Theorems.Thm_BondySimonovits_exists_walk_of_fn

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (K : SimpleGraph V) (c : ℕ → V) (L : ℕ) (hL : 3 ≤ L)
    (hadj : ∀ t < L, K.Adj (c t) (c (t + 1))) (hclose : c L = c 0)
    (hinj : ∀ s < L, ∀ t < L, c s = c t → s = t) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = L := by
  obtain ⟨p, hp, hl⟩ := exists_walk_of_fn K (fun t => c (t + 1)) (L - 1)
    (fun t ht => hadj (t + 1) (by omega)) (c 1) (c 0) rfl
    (by show c (L - 1 + 1) = c 0; rw [show L - 1 + 1 = L by omega, hclose])
  have hpath : p.IsPath := by
    rw [Walk.isPath_def, hp, List.nodup_map_iff_inj_on List.nodup_range]
    intro s hs t ht hst
    simp only [List.mem_range] at hs ht
    by_cases hs' : s + 1 = L
    · by_cases ht' : t + 1 = L
      · omega
      · simp only [hs', hclose] at hst
        have := hinj 0 (by omega) (t + 1) (by omega) hst
        omega
    · by_cases ht' : t + 1 = L
      · simp only [ht', hclose] at hst
        have := hinj (s + 1) (by omega) 0 (by omega) hst
        omega
      · have := hinj (s + 1) (by omega) (t + 1) (by omega) hst
        omega
  refine ⟨c 0, Walk.cons (hadj 0 (by omega)) p, ?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by simp; omega⟩
    simpa using hpath
  · simp; omega
end BondySimonovits
