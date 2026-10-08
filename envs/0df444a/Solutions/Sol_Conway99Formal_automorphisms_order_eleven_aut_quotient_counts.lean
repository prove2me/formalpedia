-- Prove2me | solution 1 for Conway99Formal.automorphisms.order_eleven_aut_quotient_counts
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T19:16:06.337993+00:00
-- url     : https://prove2.me/submissions/669adfd4-495e-4b79-9b92-0e4f33e16c3b

import Definitions.Def_Automorphisms
import Theorems.Thm_Conway99Formal_automorphisms_order_eleven_aut_cell_map_with_cycles
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

namespace Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

















































/-- The actual neighbor counts of a target-graph vertex, sorted by nine cell
labels, sum to its degree fourteen. -/
theorem cell_neighbor_counts_sum
    (h : G.IsSRGWith 99 14 1 2) (c : V → Fin 9) (x : V) :
    ∑ i : Fin 9, ((G.neighborFinset x).filter fun y => c y = i).card = 14 := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := G.neighborFinset x) (t := Finset.univ) (f := c)
    (by intro y hy; simp)
  calc
    ∑ i : Fin 9, ((G.neighborFinset x).filter fun y => c y = i).card =
        (G.neighborFinset x).card := by simpa using hfiber.symm
    _ = G.degree x := rfl
    _ = 14 := h.regular x

/-- An automorphism preserving the cell labels preserves each actual
neighbor count into a cell. -/
theorem cell_neighbor_counts_apply (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (c : V → Fin 9) (hc : ∀ x, c (σ x) = c x) (x : V) (i : Fin 9) :
    ((G.neighborFinset (σ x)).filter fun y => c y = i).card =
      ((G.neighborFinset x).filter fun y => c y = i).card := by
  have himage :
      ((G.neighborFinset x).filter fun y => c y = i).image σ =
        (G.neighborFinset (σ x)).filter (fun y => c y = i) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, ⟨hzadj, hzc⟩, rfl⟩
      exact ⟨(hσ x z).mp hzadj, (hc z).trans hzc⟩
    · rintro ⟨hyadj, hyc⟩
      refine ⟨σ.symm y, ⟨?_, ?_⟩, by simp⟩
      · exact (hσ x (σ.symm y)).mpr (by simpa using hyadj)
      · have hc' : c (σ.symm y) = c y := by
          simpa using (hc (σ.symm y)).symm
        exact hc'.trans hyc
  rw [← himage, Finset.card_image_of_injective _ σ.injective]

/-- Cell-neighbor counts are constant along every natural power of a
label-preserving graph automorphism. -/
theorem cell_neighbor_counts_pow (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (c : V → Fin 9) (hc : ∀ x, c (σ x) = c x)
    (x : V) (i : Fin 9) (n : ℕ) :
    ((G.neighborFinset ((σ ^ n) x)).filter fun y => c y = i).card =
      ((G.neighborFinset x).filter fun y => c y = i).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        ((G.neighborFinset ((σ ^ (n + 1)) x)).filter fun y => c y = i).card =
            ((G.neighborFinset (σ ((σ ^ n) x))).filter fun y => c y = i).card := by
          rw [pow_succ' σ n, Equiv.Perm.mul_apply]
        _ = ((G.neighborFinset ((σ ^ n) x)).filter fun y => c y = i).card :=
          cell_neighbor_counts_apply G σ hσ c hc ((σ ^ n) x) i
        _ = ((G.neighborFinset x).filter fun y => c y = i).card := ih

/-- An actual cell-neighbor count is constant between vertices on one
cycle of a label-preserving graph automorphism. -/
theorem cell_neighbor_counts_sameCycle (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (c : V → Fin 9) (hc : ∀ x, c (σ x) = c x)
    (x y : V) (hxy : σ.SameCycle x y) (i : Fin 9) :
    ((G.neighborFinset y).filter fun z => c z = i).card =
      ((G.neighborFinset x).filter fun z => c z = i).card := by
  obtain ⟨n, _, _, hn⟩ := Equiv.Perm.SameCycle.exists_pow_eq σ hxy
  rw [← hn]
  exact cell_neighbor_counts_pow G σ hσ c hc x i n

end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

open Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.automorphisms in
theorem solution
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    ∃ c : V → Fin 9, ∃ R : Matrix (Fin 9) (Fin 9) ℤ,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      (∀ x i, (((G.neighborFinset x).filter fun y => c y = i).card : ℤ) = R (c x) i) ∧
      (∀ i j, 0 ≤ R i j) ∧
      ∀ i, ∑ j, R i j = 14 := by
  classical
  obtain ⟨c, hc, hsize, hcycle⟩ :=
    order_eleven_aut_cell_map_with_cycles G h σ hσ hord
  have hnonempty (i : Fin 9) : ∃ x : V, c x = i := by
    have hp : 0 < (Finset.univ.filter fun x => c x = i).card := by
      rw [hsize i]
      norm_num
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  let rep (i : Fin 9) : V := Classical.choose (hnonempty i)
  have hrep (i : Fin 9) : c (rep i) = i := Classical.choose_spec (hnonempty i)
  let R : Matrix (Fin 9) (Fin 9) ℤ := fun i j =>
    (((G.neighborFinset (rep i)).filter fun y => c y = j).card : ℤ)
  refine ⟨c, R, hc, hsize, ?_, ?_, ?_⟩
  · intro x i
    have hs : σ.SameCycle (rep (c x)) x :=
      hcycle (rep (c x)) x (hrep (c x))
    change (((G.neighborFinset x).filter fun y => c y = i).card : ℤ) =
      (((G.neighborFinset (rep (c x))).filter fun y => c y = i).card : ℤ)
    exact congrArg (fun n : ℕ => (n : ℤ))
      (cell_neighbor_counts_sameCycle G σ hσ c hc (rep (c x)) x hs i)
  · intro i j
    change 0 ≤ (((G.neighborFinset (rep i)).filter fun y => c y = j).card : ℤ)
    exact_mod_cast Nat.zero_le _
  · intro i
    change ∑ j : Fin 9,
      (((G.neighborFinset (rep i)).filter fun y => c y = j).card : ℤ) = 14
    exact_mod_cast cell_neighbor_counts_sum G h c (rep i)
