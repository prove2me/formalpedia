-- Prove2me | solution 1 for Conway99Formal.automorphisms.order_eleven_aut_quotient_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T20:05:54.848988+00:00
-- url     : https://prove2.me/submissions/45a82caa-64f7-4ffe-bc24-8b19eaa9c54b

import Definitions.Def_Automorphisms
import Theorems.Thm_Conway99Formal_automorphisms_order_eleven_aut_quotient_counts
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

namespace Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



























































private theorem quotient_neighbor_counts_symmetric
    (c : V → Fin 9) (R : Matrix (Fin 9) (Fin 9) ℤ)
    (hsize : ∀ i, (Finset.univ.filter fun x => c x = i).card = 11)
    (hbind : ∀ x i,
      (((G.neighborFinset x).filter fun y => c y = i).card : ℤ) = R (c x) i) :
    R.transpose = R := by
  classical
  let C (i : Fin 9) : Finset V := Finset.univ.filter fun x => c x = i
  have hCcard (i : Fin 9) : (C i).card = 11 := hsize i
  have hfilter (x : V) (i : Fin 9) :
      (C i).filter (fun y => G.Adj x y) =
        (G.neighborFinset x).filter (fun y => c y = i) := by
    ext y
    simp [C, SimpleGraph.mem_neighborFinset, and_comm]
  have hentry (i j : Fin 9) (x : V) (hx : x ∈ C i) :
      (∑ y ∈ C j, if G.Adj x y then (1 : ℤ) else 0) = R i j := by
    rw [Finset.sum_boole, hfilter]
    have hcx : c x = i := (Finset.mem_filter.mp hx).2
    simpa only [hcx] using hbind x j
  have hedges (i j : Fin 9) :
      (∑ x ∈ C i, ∑ y ∈ C j, if G.Adj x y then (1 : ℤ) else 0) =
        11 * R i j := by
    calc
      (∑ x ∈ C i, ∑ y ∈ C j, if G.Adj x y then (1 : ℤ) else 0) =
          ∑ x ∈ C i, R i j := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hentry i j x hx
      _ = (C i).card * R i j := by simp [nsmul_eq_mul]
      _ = 11 * R i j := by rw [hCcard i]; norm_num
  have hswap (i j : Fin 9) :
      (∑ x ∈ C i, ∑ y ∈ C j, if G.Adj x y then (1 : ℤ) else 0) =
        (∑ y ∈ C j, ∑ x ∈ C i, if G.Adj y x then (1 : ℤ) else 0) := by
    calc
      (∑ x ∈ C i, ∑ y ∈ C j, if G.Adj x y then (1 : ℤ) else 0) =
          ∑ y ∈ C j, ∑ x ∈ C i, if G.Adj x y then (1 : ℤ) else 0 :=
        Finset.sum_comm
      _ = ∑ y ∈ C j, ∑ x ∈ C i, if G.Adj y x then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxy : G.Adj x y
        · simp [hxy, hxy.symm]
        · have hyx : ¬ G.Adj y x := fun hyx => hxy hyx.symm
          simp [hxy, hyx]
  ext i j
  change R j i = R i j
  have hij : 11 * R j i = 11 * R i j := by
    calc
      11 * R j i =
          (∑ x ∈ C j, ∑ y ∈ C i, if G.Adj x y then (1 : ℤ) else 0) :=
        (hedges j i).symm
      _ = (∑ y ∈ C i, ∑ x ∈ C j, if G.Adj y x then (1 : ℤ) else 0) :=
        hswap j i
      _ = 11 * R i j := hedges i j
  omega

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
      (∀ i, ∑ j, R i j = 14) ∧ R.transpose = R := by
  obtain ⟨c, R, hc, hsize, hbind, hnn, hrow⟩ :=
    order_eleven_aut_quotient_counts G h σ hσ hord
  exact ⟨c, R, hc, hsize, hbind, hnn, hrow,
    quotient_neighbor_counts_symmetric G c R hsize hbind⟩
