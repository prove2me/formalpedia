-- Prove2me | solution 1 for BalanceSpecification.hasBoundedSuccessiveGaps_iff_uniform_right_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:42.480808+00:00
-- url     : https://prove2.me/submissions/65d04ffd-2cfb-46d6-9bd7-c49486dec0b1

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_of_uniform_right_completion

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ}
    (hS : S.Nonempty) : HasBoundedSuccessiveGaps S ↔
      ∃ N : ℕ, ∀ t : ℕ, (∃ s ∈ S, t ≤ s) →
        ∃ s ∈ S, t ≤ s ∧ s ≤ t + N := by
  constructor
  · classical
    rintro ⟨K, hK⟩
    obtain ⟨m, hm⟩ := hS
    refine ⟨m + K, ?_⟩
    intro t hcompletion
    by_cases htm : t ≤ m
    · exact ⟨m, hm, htm, by omega⟩
    have hmt : m < t := by omega
    let b := Nat.find hcompletion
    have hb : b ∈ S := (Nat.find_spec hcompletion).1
    have htb : t ≤ b := (Nat.find_spec hcompletion).2
    let F := (Finset.range t).filter (· ∈ S)
    have hF : F.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmt, hm⟩⟩
    let a := F.max' hF
    have haF : a ∈ F := Finset.max'_mem _ _
    obtain ⟨hat, ha⟩ := Finset.mem_filter.mp haF
    have hat' : a < t := Finset.mem_range.mp hat
    have hconsecutive : ∀ s ∈ S, a < s → b ≤ s := by
      intro s hs has
      by_cases hst : s < t
      · have hsF : s ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hst, hs⟩
        have hsa : s ≤ a := Finset.le_max' _ _ hsF
        omega
      · exact Nat.find_min' hcompletion ⟨hs, by omega⟩
    have hgap := hK a ha b hb (lt_of_lt_of_le hat' htb) hconsecutive
    exact ⟨b, hb, htb, by omega⟩
  · exact hasBoundedSuccessiveGaps_of_uniform_right_completion
end BalanceSpecification
