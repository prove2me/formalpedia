-- Prove2me | solution 1 for CerednikDrinfeld.exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b0c50443-d006-53e8-8632-387293e3a5d4

import Mathlib
import Definitions.Def_CerednikDrinfeld_Ribbon
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite

set_option autoImplicit false

open ModularCurve

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "degeneracyMatrix degreeOn_pushforward"
p2m_open "CerednikDrinfeld"

namespace DoubleCoverGraph

variable {E V : Type*}

section Combinatorics

variable (a b : E → V)

theorem sum_closed_eq_empty_or_eq_univ
    (hsymm : ∀ e : E, ∃ e' : E, a e' = b e ∧ b e' = a e)
    (hconn : ∀ P : Set V, (∀ e : E, a e ∈ P ↔ b e ∈ P) → P = ∅ ∨ P = Set.univ)
    (hodd : ∀ P : Set V, P.Nonempty → ∃ e : E, (a e ∈ P ↔ b e ∈ P))
    (Q : Set (V ⊕ V)) (hQ : ∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) :
    Q = ∅ ∨ Q = Set.univ := by
  classical

  have hQ' : ∀ e : E, Sum.inl (b e) ∈ Q ↔ Sum.inr (a e) ∈ Q := by
    intro e
    obtain ⟨e', h1, h2⟩ := hsymm e
    rw [← h1, ← h2]
    exact hQ e'

  let U : Set V := {v | Sum.inl v ∈ Q ∧ Sum.inr v ∈ Q}
  have hUc : ∀ e : E, a e ∈ U ↔ b e ∈ U := by
    intro e
    show (Sum.inl (a e) ∈ Q ∧ Sum.inr (a e) ∈ Q) ↔ (Sum.inl (b e) ∈ Q ∧ Sum.inr (b e) ∈ Q)
    rw [hQ e, ← hQ' e]
    exact and_comm

  let N : Set V := {v | Sum.inl v ∉ Q ∧ Sum.inr v ∉ Q}
  have hNc : ∀ e : E, a e ∈ N ↔ b e ∈ N := by
    intro e
    show (Sum.inl (a e) ∉ Q ∧ Sum.inr (a e) ∉ Q) ↔ (Sum.inl (b e) ∉ Q ∧ Sum.inr (b e) ∉ Q)
    rw [hQ e, ← hQ' e]
    exact and_comm
  rcases hconn U hUc with hU0 | hU1
  · rcases hconn N hNc with hN0 | hN1
    ·
      rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
      · left
        ext z
        simp only [Set.mem_empty_iff_false, iff_false]
        intro _
        rcases z with v | v <;> exact isEmptyElim v
      · exfalso
        let P : Set V := {v | Sum.inl v ∈ Q}
        have hone : ∀ v : V, (Sum.inr v ∈ Q ↔ v ∉ P) := by
          intro v
          have h1 : v ∉ U := by rw [hU0]; exact fun h => h
          have h2 : v ∉ N := by rw [hN0]; exact fun h => h
          change ¬ (Sum.inl v ∈ Q ∧ Sum.inr v ∈ Q) at h1
          change ¬ (Sum.inl v ∉ Q ∧ Sum.inr v ∉ Q) at h2
          change Sum.inr v ∈ Q ↔ ¬ (Sum.inl v ∈ Q)
          tauto
        have hedge : ∀ e : E, (a e ∈ P ↔ b e ∉ P) := by
          intro e
          rw [← hone (b e)]
          exact hQ e
        by_cases hv : v₀ ∈ P
        · obtain ⟨e, he⟩ := hodd P ⟨v₀, hv⟩
          have h := hedge e
          tauto
        · obtain ⟨e, he⟩ := hodd Pᶜ ⟨v₀, hv⟩
          have h := hedge e
          simp only [Set.mem_compl_iff] at he
          tauto
    ·
      left
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rcases z with v | v
      · have hv : v ∈ N := by rw [hN1]; trivial
        exact hv.1
      · have hv : v ∈ N := by rw [hN1]; trivial
        exact hv.2
  ·
    right
    ext z
    simp only [Set.mem_univ, iff_true]
    rcases z with v | v
    · have hv : v ∈ U := by rw [hU1]; trivial
      exact hv.1
    · have hv : v ∈ U := by rw [hU1]; trivial
      exact hv.2

end Combinatorics

section LinearAlgebra

variable [Fintype E] [DecidableEq V] (a b : E → V)

noncomputable def jointMap : (E → ℤ) →ₗ[ℤ] (V → ℤ) × (V → ℤ) :=
  LinearMap.prod (degeneracyMatrix a).mulVecLin (degeneracyMatrix b).mulVecLin

theorem jointMap_apply (D : E → ℤ) :
    jointMap a b D = ((degeneracyMatrix a).mulVec D, (degeneracyMatrix b).mulVec D) := rfl

theorem degeneracyMatrix_mulVec_single [DecidableEq E] (f : E → V) (e : E) :
    (degeneracyMatrix f).mulVec (Pi.single e 1) = Pi.single (f e) 1 := by
  ext v
  simp only [Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : f e = v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem jointMap_single [DecidableEq E] (e : E) :
    jointMap a b (Pi.single e 1) = (Pi.single (a e) 1, Pi.single (b e) 1) := by
  rw [jointMap_apply, degeneracyMatrix_mulVec_single, degeneracyMatrix_mulVec_single]

theorem pair_single_mem_range (e : E) :
    (Pi.single (a e) (1 : ℤ), Pi.single (b e) (1 : ℤ)) ∈ LinearMap.range (jointMap a b) := by
  classical
  exact LinearMap.mem_range.mpr ⟨Pi.single e 1, jointMap_single a b e⟩

noncomputable def potential : V ⊕ V → (V → ℤ) × (V → ℤ) :=
  Sum.elim (fun v => (Pi.single v 1, 0)) (fun w => (0, -Pi.single w 1))

@[scoped simp] theorem potential_inl (v : V) : potential (V := V) (Sum.inl v) = (Pi.single v 1, 0) := rfl

@[scoped simp] theorem potential_inr (w : V) : potential (V := V) (Sum.inr w) = (0, -Pi.single w 1) := rfl

theorem potential_inl_sub_potential_inr_mem (e : E) :
    potential (Sum.inl (a e)) - potential (Sum.inr (b e)) ∈ LinearMap.range (jointMap a b) := by
  have h : potential (Sum.inl (a e)) - potential (Sum.inr (b e))
      = (Pi.single (a e) (1 : ℤ), Pi.single (b e) (1 : ℤ)) := by
    ext <;> simp
  rw [h]
  exact pair_single_mem_range a b e

theorem potential_sub_potential_mem
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (z₀ z : V ⊕ V) :
    potential z₀ - potential z ∈ LinearMap.range (jointMap a b) := by
  let Q : Set (V ⊕ V) := {z | potential z₀ - potential z ∈ LinearMap.range (jointMap a b)}
  have hQc : ∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q := by
    intro e
    show potential z₀ - potential (Sum.inl (a e)) ∈ LinearMap.range (jointMap a b) ↔
      potential z₀ - potential (Sum.inr (b e)) ∈ LinearMap.range (jointMap a b)
    have hd := potential_inl_sub_potential_inr_mem a b e
    constructor
    · intro h
      have := (LinearMap.range (jointMap a b)).add_mem h hd
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := (LinearMap.range (jointMap a b)).sub_mem h hd
      rwa [sub_sub_sub_cancel_right] at this
  have h0 : z₀ ∈ Q := by
    show potential z₀ - potential z₀ ∈ LinearMap.range (jointMap a b)
    rw [sub_self]
    exact Submodule.zero_mem _
  rcases hH Q hQc with hQ0 | hQ1
  · exfalso
    rw [hQ0] at h0
    exact h0
  · have hz : z ∈ Q := by rw [hQ1]; trivial
    exact hz

theorem single_sub_single_fst_mem
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (v w : V) :
    (Pi.single v (1 : ℤ) - Pi.single w 1, (0 : V → ℤ)) ∈ LinearMap.range (jointMap a b) := by
  have h := potential_sub_potential_mem a b hH (Sum.inl v) (Sum.inl w)
  have heq : potential (Sum.inl v) - potential (Sum.inl w)
      = (Pi.single v (1 : ℤ) - Pi.single w 1, (0 : V → ℤ)) := by
    ext <;> simp
  rwa [heq] at h

theorem single_sub_single_snd_mem
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (v w : V) :
    ((0 : V → ℤ), Pi.single v (1 : ℤ) - Pi.single w 1) ∈ LinearMap.range (jointMap a b) := by
  have h := potential_sub_potential_mem a b hH (Sum.inr w) (Sum.inr v)
  have heq : potential (Sum.inr w) - potential (Sum.inr v)
      = ((0 : V → ℤ), Pi.single v (1 : ℤ) - Pi.single w 1) := by
    ext <;> simp [sub_eq_add_neg, add_comm]
  rwa [heq] at h

theorem eq_sum_smul_single_sub_single [Fintype V] (v₀ : V) (x : V → ℤ) (hx : x ∈ characterLattice V) :
    x = ∑ v, x v • (Pi.single v (1 : ℤ) - Pi.single v₀ 1) := by
  rw [mem_characterLattice] at hx
  ext w
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hw : w = v₀
  · simp only [hw, if_true]
    rw [hx, sub_zero]
  · simp only [hw, if_false, Finset.sum_const_zero, sub_zero]

theorem pair_fst_mem_range [Fintype V]
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (v₀ : V) (x : V → ℤ) (hx : x ∈ characterLattice V) :
    (x, (0 : V → ℤ)) ∈ LinearMap.range (jointMap a b) := by
  have heq : (x, (0 : V → ℤ)) = ∑ v, x v • (Pi.single v (1 : ℤ) - Pi.single v₀ 1, (0 : V → ℤ)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst]
      exact eq_sum_smul_single_sub_single v₀ x hx
    · rw [Prod.snd_sum]
      simp only [Prod.smul_snd, smul_zero, Finset.sum_const_zero]
  rw [heq]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (single_sub_single_fst_mem a b hH v v₀)

theorem pair_snd_mem_range [Fintype V]
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (v₀ : V) (y : V → ℤ) (hy : y ∈ characterLattice V) :
    ((0 : V → ℤ), y) ∈ LinearMap.range (jointMap a b) := by
  have heq : ((0 : V → ℤ), y) = ∑ v, y v • ((0 : V → ℤ), Pi.single v (1 : ℤ) - Pi.single v₀ 1) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst, smul_zero, Finset.sum_const_zero]
    · rw [Prod.snd_sum]
      simp only [Prod.smul_snd]
      exact eq_sum_smul_single_sub_single v₀ y hy
  rw [heq]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (single_sub_single_snd_mem a b hH v v₀)

theorem exists_of_doubleCover_connected [Fintype V]
    (hH : ∀ Q : Set (V ⊕ V), (∀ e : E, Sum.inl (a e) ∈ Q ↔ Sum.inr (b e) ∈ Q) → Q = ∅ ∨ Q = Set.univ)
    (x y : V → ℤ) (hx : x ∈ characterLattice V) (hy : y ∈ characterLattice V) :
    ∃ D : E → ℤ, D ∈ characterLattice E ∧
      (degeneracyMatrix a).mulVec D = x ∧ (degeneracyMatrix b).mulVec D = y := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · refine ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · ext v; exact isEmptyElim v
    · ext v; exact isEmptyElim v
  · have hxy : (x, y) ∈ LinearMap.range (jointMap a b) := by
      have := (LinearMap.range (jointMap a b)).add_mem (pair_fst_mem_range a b hH v₀ x hx)
        (pair_snd_mem_range a b hH v₀ y hy)
      rwa [Prod.mk_add_mk, add_zero, zero_add] at this
    obtain ⟨D, hD⟩ := LinearMap.mem_range.mp hxy
    rw [jointMap_apply, Prod.mk.injEq] at hD
    refine ⟨D, ?_, hD.1, hD.2⟩

    have hdeg : degreeOn E D = degreeOn V x := by
      rw [← degreeOn_pushforward a D]
      show degreeOn V ((degeneracyMatrix a).mulVecLin D) = degreeOn V x
      rw [Matrix.mulVecLin_apply, hD.1]
    have hx0 : degreeOn V x = 0 := hx
    show D ∈ LinearMap.ker (degreeOn E)
    rw [LinearMap.mem_ker, hdeg, hx0]

end LinearAlgebra

end DoubleCoverGraph
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.CerednikDrinfeld.DoubleCoverGraph"

end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.CerednikDrinfeld.DoubleCoverGraph P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.CerednikDrinfeld"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.CerednikDrinfeld in

theorem solution
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] (a b : E → V)
    (hsymm : ∀ e : E, ∃ e' : E, a e' = b e ∧ b e' = a e)
    (hconn : ∀ P : Set V, (∀ e : E, a e ∈ P ↔ b e ∈ P) → P = ∅ ∨ P = Set.univ)
    (hodd : ∀ P : Set V, P.Nonempty → ∃ e : E, (a e ∈ P ↔ b e ∈ P))
    (x y : V → ℤ) (hx : x ∈ characterLattice V) (hy : y ∈ characterLattice V) :
    ∃ D : E → ℤ, D ∈ characterLattice E ∧
      (CerednikDrinfeld.degeneracyMatrix a).mulVec D = x ∧
      (CerednikDrinfeld.degeneracyMatrix b).mulVec D = y :=
  DoubleCoverGraph.exists_of_doubleCover_connected a b
    (DoubleCoverGraph.sum_closed_eq_empty_or_eq_univ a b hsymm hconn hodd) x y hx hy

end S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite (solution)
