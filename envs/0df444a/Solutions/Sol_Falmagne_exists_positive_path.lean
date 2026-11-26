-- Prove2me | solution 1 for Falmagne.exists_positive_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:14.628825+00:00
-- url     : https://prove2.me/submissions/788fe7c0-d51f-4561-81cf-02a10c58ac49

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution (h : IsFlow q m) (A : Finset X) (hpos : 0 < outflow q A) :
    ∃ l : List X, l.Nodup ∧ l.toFinset = A ∧
      ∀ x B, pathFlow l x B ≠ 0 → 0 < q x B := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
      obtain ⟨y, hy, hqy⟩ := (Finset.sum_pos_iff_of_nonneg (fun x hx => h.nonneg x A hx)).mp hpos
      by_cases he : A.erase y = ∅
      · have hsing : ({y} : Finset X) = A := by
          have hAi : insert y (A.erase y) = A := Finset.insert_erase hy
          simpa [he] using hAi
        refine ⟨[y], by simp, by simpa using hsing, ?_⟩
        intro x B hp
        simp [pathFlow, unitEdge] at hp
        obtain ⟨hxy, hB⟩ := hp
        rw [hxy, hB, hsing]
        exact hqy
      · have hAe : (A.erase y).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
        have hnotU : A.erase y ≠ Finset.univ := by
          intro heq
          have : y ∈ A.erase y := by rw [heq]; exact Finset.mem_univ y
          simp at this
        have hqin : q y A ≤ inflow q (A.erase y) := by
          have hymem : y ∈ Finset.univ \ A.erase y := by simp
          have hh := Finset.single_le_sum
            (fun z (hz : z ∈ Finset.univ \ A.erase y) =>
              h.nonneg z (insert z (A.erase y)) (Finset.mem_insert_self _ _)) hymem
          simpa [inflow, Finset.insert_erase hy] using hh
        have htailpos : 0 < outflow q (A.erase y) := by
          rw [h.conserve _ hAe hnotU]
          linarith
        obtain ⟨l, hln, hlA, hlpos⟩ :=
          ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem hy) (A.erase y) htailpos rfl
        have hyn : y ∉ l := by
          have : y ∉ l.toFinset := by rw [hlA]; simp
          simpa using this
        refine ⟨y :: l, List.nodup_cons.mpr ⟨hyn, hln⟩, ?_, ?_⟩
        · simp [hlA, Finset.insert_erase hy]
        · intro x B hp
          by_cases hu : unitEdge y (y :: l).toFinset x B = 0
          · apply hlpos x B
            rw [pathFlow_cons, hu, zero_add] at hp
            exact hp
          · have heq : x = y ∧ B = (y :: l).toFinset := by
              simpa [unitEdge] using hu
            obtain ⟨rfl, rfl⟩ := heq
            simpa [hlA, Finset.insert_erase hy] using hqy
end Falmagne
