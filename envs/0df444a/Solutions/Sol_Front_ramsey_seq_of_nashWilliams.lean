-- Prove2me | solution 1 for Front.ramsey_seq_of_nashWilliams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:51.976229+00:00
-- url     : https://prove2.me/submissions/6f3277fc-08c8-43f4-abcc-99569f9e458c

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Data.Finset.Sort
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_NashWilliams
public import Theorems.Thm_Front_IsFront_nash_williams_fin
public import Theorems.Thm_Front_isFront_powK
public import Theorems.Thm_Front_shrink_powK


set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution {κ : Type*} [Finite κ] (k : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = k → c t = col := by
  classical
  -- Apply the finite-color theorem to `[ℕ]^k` with the list-coloring `c ∘ toFinset`.
  obtain ⟨e, he, col, hmono⟩ :=
    (isFront_powK (strictMono_id (α := ℕ)) k).nash_williams_fin (fun s => c s.toFinset)
  refine ⟨e, he, col, fun t hts htcard => ?_⟩
  -- The sorted list of `t` is a member of the restricted uniform front.
  have hmem : t.sort (· ≤ ·) ∈ powK (id ∘ e) k := by
    refine ⟨?_, (Finset.sortedLT_sort t).pairwise, fun x hx => ?_⟩
    · rw [Finset.length_sort]; exact htcard
    · rw [Finset.mem_sort] at hx; exact hts hx
  have hshr : t.sort (· ≤ ·) ∈ shrink (powK id k) (id ∘ e) := by
    rw [shrink_powK]; exact hmem
  have hc := hmono _ hshr
  rwa [Finset.sort_toFinset] at hc
end Front
