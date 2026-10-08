-- Prove2me | solution 1 for Conway99Formal.automorphisms.order_eleven_aut_cell_map_with_cycles
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T18:33:19.547612+00:00
-- url     : https://prove2.me/submissions/dfc57c09-b6bc-4544-b439-9e3edce3c983

import Definitions.Def_Automorphisms
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

namespace Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









theorem fixedSet_eq_empty_iff (σ : Equiv.Perm V) :
    fixedSet σ = ∅ ↔ ∀ x, σ x ≠ x := by
  simp [fixedSet, Finset.filter_eq_empty_iff]



/-- A fixed-point-free permutation of order eleven on 99 vertices consists of
nine eleven-cycles. -/
theorem order_eleven_cycleType_of_fixed_point_free
    (hcard : Fintype.card V = 99) (σ : Equiv.Perm V)
    (hord : orderOf σ = 11) (hfpf : fixedSet σ = ∅) :
    σ.cycleType = Multiset.replicate 9 11 := by
  have hfull : σ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact (fixedSet_eq_empty_iff σ).mp hfpf x
  have hsupport : σ.support.card = 99 := by
    rw [hfull, Finset.card_univ, hcard]
  have hprime : (orderOf σ).Prime := by
    rw [hord]
    norm_num
  obtain ⟨n, hn⟩ := σ.cycleType_prime_order hprime
  have hsum := σ.sum_cycleType
  rw [hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hord, hsupport] at hsum
  have hn9 : n + 1 = 9 := by omega
  simpa only [hord, hn9] using hn

private theorem order_eleven_cell_map_with_cycles_of_fixed_point_free
    (hcard : Fintype.card V = 99) (σ : Equiv.Perm V)
    (hord : orderOf σ = 11) (hfpf : fixedSet σ = ∅) :
    ∃ c : V → Fin 9,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      ∀ x y, c x = c y → σ.SameCycle x y := by
  classical
  have hcycle := order_eleven_cycleType_of_fixed_point_free hcard σ hord hfpf
  have hfactor : σ.cycleFactorsFinset.card = 9 := by
    have hm : σ.cycleType.card = σ.cycleFactorsFinset.card := by
      simp [Equiv.Perm.cycleType_def]
    simpa [hcycle] using hm.symm
  let label : σ.cycleFactorsFinset ≃ Fin 9 :=
    Finset.equivFinOfCardEq hfactor
  have hsupport (x : V) : x ∈ σ.support := by
    exact Equiv.Perm.mem_support.mpr ((fixedSet_eq_empty_iff σ).mp hfpf x)
  let factor (x : V) : σ.cycleFactorsFinset :=
    ⟨σ.cycleOf x,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (hsupport x)⟩
  let c (x : V) : Fin 9 := label (factor x)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro x
    apply congrArg label
    apply Subtype.ext
    exact σ.cycleOf_self_apply x
  · intro i
    let d : σ.cycleFactorsFinset := label.symm i
    have hsize : d.val.support.card = 11 := by
      have hm : d.val.support.card ∈ σ.cycleType := by
        rw [σ.cycleType_def]
        exact Multiset.mem_map.mpr ⟨d.val, d.property, rfl⟩
      simpa [hcycle] using hm
    have hfiber :
        (Finset.univ.filter fun x : V => c x = i) = d.val.support := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
        σ d.val d.property x
      constructor
      · intro hc
        have hd : factor x = d := by
          apply label.injective
          simpa [c, d] using hc
        exact hiff.mp ((congrArg Subtype.val hd).symm)
      · intro hx
        have hd : factor x = d := Subtype.ext ((hiff.mpr hx).symm)
        change label (factor x) = i
        rw [hd]
        exact label.apply_symm_apply i
    rw [hfiber]
    exact hsize
  · intro x y hxy
    apply (σ.sameCycle_iff_cycleOf_eq_of_mem_support
      (hsupport x) (hsupport y)).mpr
    exact congrArg Subtype.val (label.injective hxy)





/-- The common-neighbor set of two fixed vertices is invariant under the automorphism. -/
theorem commonNeighbors_mem_iff_apply (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (a b : V) (ha : σ a = a) (hb : σ b = b) (y : V) :
    y ∈ G.commonNeighbors a b ↔ σ y ∈ G.commonNeighbors a b := by
  simpa only [SimpleGraph.mem_commonNeighbors, ha, hb] using
    (hσ a y).and (hσ b y)

/-- The unique common neighbor of adjacent fixed vertices is fixed. -/
theorem fixed_common_neighbor_of_adj
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (a b : V) (ha : σ a = a) (hb : σ b = b) (hab : G.Adj a b)
    (y : V) (hy : y ∈ G.commonNeighbors a b) : σ y = y := by
  have hcard : Fintype.card (G.commonNeighbors a b) = 1 := h.of_adj a b hab
  haveI : Subsingleton (G.commonNeighbors a b) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hσy : σ y ∈ G.commonNeighbors a b :=
    (commonNeighbors_mem_iff_apply G σ hσ a b ha hb y).mp hy
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨σ y, hσy⟩ : G.commonNeighbors a b) ⟨y, hy⟩)

/-- Both common neighbors of distinct nonadjacent fixed vertices are fixed by
an order-eleven automorphism. -/
theorem fixed_common_neighbor_of_not_adj
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11)
    (a b : V) (ha : σ a = a) (hb : σ b = b)
    (hne : a ≠ b) (hnadj : ¬ G.Adj a b)
    (y : V) (hy : y ∈ G.commonNeighbors a b) : σ y = y := by
  let S : Set V := G.commonNeighbors a b
  have hS : ∀ z : V, σ z ∈ S ↔ z ∈ S := fun z =>
    (commonNeighbors_mem_iff_apply G σ hσ a b ha hb z).symm
  let τ : Equiv.Perm S := σ.subtypePerm hS
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hpow : σ ^ 11 = 1 := by
    simpa only [← hord] using pow_orderOf_eq_one σ
  have hτpow : τ ^ 11 = 1 := by
    unfold τ
    simp only [Equiv.Perm.subtypePerm_pow, hpow]
    rfl
  have hcard : Fintype.card S = 2 := h.of_not_adj hne hnadj
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 11) (n := 1)
    (by simpa only [pow_one] using hτpow)
  rw [hcard] at hmod
  have hle : τ.supportᶜ.card ≤ 2 := by
    simpa only [hcard] using Finset.card_le_univ τ.supportᶜ
  change τ.supportᶜ.card % 11 = 2 % 11 at hmod
  have hfixedcard : τ.supportᶜ.card = 2 := by omega
  have hfull : τ.supportᶜ = Finset.univ :=
    (Finset.card_eq_iff_eq_univ τ.supportᶜ).mp
      (by simpa only [hcard] using hfixedcard)
  have hmem : (⟨y, hy⟩ : S) ∈ τ.supportᶜ := by simp [hfull]
  have hyfix : τ ⟨y, hy⟩ = ⟨y, hy⟩ := by
    simpa [Equiv.Perm.mem_support] using hmem
  simpa only [τ, Equiv.Perm.subtypePerm_apply] using congrArg Subtype.val hyfix

/-- If an order-eleven automorphism fixes a vertex and all its neighbors,
then it fixes every vertex of the target graph. -/
theorem fixed_all_of_fixed_neighborhood
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11)
    (x : V) (hx : σ x = x)
    (hfixN : ∀ y : V, G.Adj x y → σ y = y) :
    ∀ y : V, σ y = y := by
  intro y
  by_cases hyx : y = x
  · simpa only [hyx] using hx
  by_cases hxy : G.Adj x y
  · exact hfixN y hxy
  have hcard : Fintype.card (G.commonNeighbors x y) = 2 :=
    h.of_not_adj (Ne.symm hyx) hxy
  have hgt : 1 < Fintype.card (G.commonNeighbors x y) := by omega
  obtain ⟨p, q, hpq⟩ :=
    (Fintype.one_lt_card_iff (α := G.commonNeighbors x y)).mp hgt
  have hp : G.Adj x (p : V) ∧ G.Adj y (p : V) :=
    p.property
  have hq : G.Adj x (q : V) ∧ G.Adj y (q : V) :=
    q.property
  have hpn : σ (p : V) = p := hfixN p hp.1
  have hqn : σ (q : V) = q := hfixN q hq.1
  have hpqne : (p : V) ≠ (q : V) := by
    intro heq
    exact hpq (Subtype.ext heq)
  have hpqnadj : ¬ G.Adj (p : V) (q : V) := by
    intro hadj
    have hpaircard : Fintype.card (G.commonNeighbors (p : V) (q : V)) = 1 :=
      h.of_adj p q hadj
    haveI : Subsingleton (G.commonNeighbors (p : V) (q : V)) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hxm : x ∈ G.commonNeighbors (p : V) (q : V) :=
      ⟨hp.1.symm, hq.1.symm⟩
    have hym : y ∈ G.commonNeighbors (p : V) (q : V) :=
      ⟨hp.2.symm, hq.2.symm⟩
    have hxe : x = y := congrArg Subtype.val
      (Subsingleton.elim (⟨x, hxm⟩ : G.commonNeighbors (p : V) (q : V)) ⟨y, hym⟩)
    exact hyx hxe.symm
  exact fixed_common_neighbor_of_not_adj G h σ hσ hord p q hpn hqn
    hpqne hpqnadj y ⟨hp.2.symm, hq.2.symm⟩



/-- An order-eleven automorphism fixing a vertex fixes either three or all
fourteen of its neighbors. The fixed set is measured in the induced permutation. -/
theorem fixed_neighbor_count_three_or_fourteen
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11)
    (x : V) (hx : σ x = x) :
    (neighborPerm G σ hσ x hx).supportᶜ.card = 3 ∨
      (neighborPerm G σ hσ x hx).supportᶜ.card = 14 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hpow : σ ^ 11 = 1 := by
    simpa only [← hord] using pow_orderOf_eq_one σ
  have hneighborPow : (neighborPerm G σ hσ x hx) ^ 11 = 1 := by
    unfold neighborPerm
    simp only [Equiv.Perm.subtypePerm_pow, hpow]
    rfl
  have hcount : Fintype.card (G.neighborFinset x) = 14 := by
    calc
      Fintype.card (G.neighborFinset x) = (G.neighborFinset x).card :=
        Fintype.card_coe _
      _ = G.degree x := rfl
      _ = 14 := h.regular x
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 11) (n := 1)
    (by simpa only [pow_one] using hneighborPow)
  rw [hcount] at hmod
  have hle : (neighborPerm G σ hσ x hx).supportᶜ.card ≤ 14 := by
    simpa only [hcount] using Finset.card_le_univ
      (neighborPerm G σ hσ x hx).supportᶜ
  change (neighborPerm G σ hσ x hx).supportᶜ.card % 11 = 14 % 11 at hmod
  omega

/-- The all-fourteen branch would make the order-eleven automorphism the identity. -/
theorem fixed_neighbor_count_ne_fourteen
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11)
    (x : V) (hx : σ x = x) :
    (neighborPerm G σ hσ x hx).supportᶜ.card ≠ 14 := by
  intro h14
  have hcount : Fintype.card (G.neighborFinset x) = 14 := by
    calc
      Fintype.card (G.neighborFinset x) = (G.neighborFinset x).card :=
        Fintype.card_coe _
      _ = G.degree x := rfl
      _ = 14 := h.regular x
  have hfull : (neighborPerm G σ hσ x hx).supportᶜ = Finset.univ :=
    (Finset.card_eq_iff_eq_univ (neighborPerm G σ hσ x hx).supportᶜ).mp
      (by simpa only [hcount] using h14)
  have hfixN : ∀ y : V, G.Adj x y → σ y = y := by
    intro y hy
    have hym : y ∈ G.neighborFinset x := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    have hmem : (⟨y, hym⟩ : G.neighborFinset x) ∈
        (neighborPerm G σ hσ x hx).supportᶜ := by simp [hfull]
    have hyfix : neighborPerm G σ hσ x hx ⟨y, hym⟩ = ⟨y, hym⟩ := by
      simpa [Equiv.Perm.mem_support] using hmem
    simpa only [neighborPerm, Equiv.Perm.subtypePerm_apply] using
      congrArg Subtype.val hyfix
  have hσone : σ = 1 := by
    apply Equiv.ext
    intro y
    simpa using fixed_all_of_fixed_neighborhood G h σ hσ hord x hx hfixN y
  have hone : orderOf σ = 1 := by simp [hσone]
  omega

/-- A fixed vertex of an order-eleven automorphism has exactly three fixed neighbors. -/
theorem fixed_neighbor_count_eq_three
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11)
    (x : V) (hx : σ x = x) :
    (neighborPerm G σ hσ x hx).supportᶜ.card = 3 := by
  rcases fixed_neighbor_count_three_or_fourteen G h σ hσ hord x hx with h3 | h14
  · exact h3
  · exact (fixed_neighbor_count_ne_fourteen G h σ hσ hord x hx h14).elim

/-- Inducing on a set containing every common neighbor preserves the count for
the selected pair. -/
theorem card_commonNeighbors_induce_of_subset
    (S : Set V) [Fintype S] (a b : S)
    (hsub : G.commonNeighbors (a : V) (b : V) ⊆ S) :
    Fintype.card ((G.induce S).commonNeighbors a b) =
      Fintype.card (G.commonNeighbors (a : V) (b : V)) := by
  classical
  let e : (G.induce S).commonNeighbors a b ≃
      G.commonNeighbors (a : V) (b : V) :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun z => ⟨⟨z.1, hsub z.2⟩, z.2⟩
      left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  exact Fintype.card_congr e

/-- The graph induced on the fixed vertices has the parameters asserted by the
fixed-locus step of the order-eleven source argument. -/
theorem fixed_locus_is_srg
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    (G.induce {y : V | σ y = y}).IsSRGWith
      (Fintype.card {y : V // σ y = y}) 3 1 2 := by
  classical
  let S : Set V := {y | σ y = y}
  have hdegree (x : S) : (G.induce S).degree x = 3 := by
    have hx : σ (x : V) = x := x.property
    let τ := neighborPerm G σ hσ (x : V) hx
    have hτ : τ.supportᶜ.card = 3 :=
      fixed_neighbor_count_eq_three G h σ hσ hord x hx
    let e : (G.induce S).neighborFinset x ≃
        {y : G.neighborFinset (x : V) // σ (y : V) = y} :=
      { toFun := fun y =>
          ⟨⟨y.1.1, by
              simpa only [SimpleGraph.mem_neighborFinset,
                SimpleGraph.induce_adj] using y.2⟩, y.1.2⟩
        invFun := fun y =>
          ⟨⟨y.1.1, y.2⟩, by
            simpa only [SimpleGraph.mem_neighborFinset,
              SimpleGraph.induce_adj] using y.1.2⟩
        left_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl }
    have hFin :
        ({y : G.neighborFinset (x : V) | σ (y : V) = y} : Finset _) =
          τ.supportᶜ := by
      ext y
      simp [τ, neighborPerm, Equiv.Perm.mem_support,
        Equiv.Perm.subtypePerm_apply]
    have hcard :
        Fintype.card {y : G.neighborFinset (x : V) // σ (y : V) = y} =
          τ.supportᶜ.card := by
      rw [Fintype.card_subtype (fun y : G.neighborFinset (x : V) => σ (y : V) = y)]
      rw [hFin]
    calc
      (G.induce S).degree x = ((G.induce S).neighborFinset x).card :=
        ((G.induce S).card_neighborFinset_eq_degree x).symm
      _ = Fintype.card ((G.induce S).neighborFinset x) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card {y : G.neighborFinset (x : V) // σ (y : V) = y} :=
        Fintype.card_congr e
      _ = τ.supportᶜ.card := hcard
      _ = 3 := hτ
  change (G.induce S).IsSRGWith (Fintype.card S) 3 1 2
  refine ⟨rfl, hdegree, ?_, ?_⟩
  · intro a b hab
    have hsub : G.commonNeighbors (a : V) (b : V) ⊆ S := by
      intro y hy
      exact fixed_common_neighbor_of_adj G h σ hσ a b a.property b.property
        hab y hy
    rw [card_commonNeighbors_induce_of_subset G S a b hsub]
    exact h.of_adj a b hab
  · intro a b hab hnadj
    have hne : (a : V) ≠ (b : V) := by
      intro heq
      exact hab (Subtype.ext heq)
    have hsub : G.commonNeighbors (a : V) (b : V) ⊆ S := by
      intro y hy
      exact fixed_common_neighbor_of_not_adj G h σ hσ hord a b
        a.property b.property hne hnadj y hy
    rw [card_commonNeighbors_induce_of_subset G S a b hsub]
    exact h.of_not_adj hne hnadj

/-- An order-eleven automorphism of the actual target graph fixes no vertex. -/
theorem order_eleven_fixed_point_free
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    fixedSet σ = ∅ := by
  apply (fixedSet_eq_empty_iff σ).mpr
  intro x hx
  let S : Set V := {y | σ y = y}
  let H : SimpleGraph S := G.induce S
  have hsrg : H.IsSRGWith (Fintype.card S) 3 1 2 :=
    fixed_locus_is_srg G h σ hσ hord
  have hpos : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  have hp := SimpleGraph.IsSRGWith.param_eq H hsrg hpos
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
    ∃ c : V → Fin 9,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      ∀ x y, c x = c y → σ.SameCycle x y :=
  order_eleven_cell_map_with_cycles_of_fixed_point_free h.card σ hord
    (order_eleven_fixed_point_free G h σ hσ hord)
