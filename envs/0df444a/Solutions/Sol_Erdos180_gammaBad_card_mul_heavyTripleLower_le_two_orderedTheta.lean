-- Prove2me | solution 1 for Erdos180.gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:59:18.790465+00:00
-- url     : https://prove2.me/submissions/497821fe-a6fe-4de1-a65a-b06b8ac2dabe

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Theorems.Thm_Erdos180_card_nonbacktrackingNeighbor
import Theorems.Thm_Erdos180_fintype_card_sigma_lower
import Theorems.Thm_Erdos180_gammaGood_of_independentThetaTriple_fiber
import Theorems.Thm_Erdos180_mem_gammaBadVertices
import Theorems.Thm_Erdos180_proposedFamilyFree_four_cycle
import Theorems.Thm_Erdos180_proposedFamilyFree_six_cycle

namespace Erdos180

noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_nonbacktrackingFourPath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (NonbacktrackingFourPath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hthird (a : G.neighborSet u)
      (w : NonbacktrackingNeighbor G u (a : V)) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
            NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep w.property.1.symm
    · intro b
      exact hstep b.property.1.symm
  have hsecond (a : G.neighborSet u) :
      (d - 1) * ((d - 1) * (d - 1)) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
              NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · exact hthird a
  have hfirst : d ≤ Fintype.card (G.neighborSet u) := by
    simpa [G.card_neighborSet_eq_degree] using hdegree u
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
          NonbacktrackingNeighbor G (w : V) (b : V))
    hfirst hsecond
  simpa [pow_succ, mul_assoc] using hcount

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathPair_injective
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathPair G
        (u := u)) := by
  rintro ⟨a, w, b, v⟩ ⟨a', w', b', v'⟩ hpair
  change ((v : V), (w : V)) =
    ((v' : V), (w' : V)) at hpair
  have hv : (v : V) = (v' : V) :=
    congrArg Prod.fst hpair
  have hw : (w : V) = (w' : V) :=
    congrArg Prod.snd hpair
  have hwa' : G.Adj (w : V) (a' : V) := by
    rw [hw]
    exact w'.property.1.symm
  have haa' : (a : V) = (a' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm
      a.property w.property.1.symm
      a'.property hwa'
  have ha : a = a' := Subtype.ext haa'
  subst a'
  have hw' : w = w' := Subtype.ext hw
  subst w'
  have hvb' : G.Adj (v : V) (b' : V) := by
    rw [hv]
    exact v'.property.1.symm
  have hbb' : (b : V) = (b' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      v.property.2.symm
      b.property.1 v.property.1.symm
      b'.property.1 hvb'
  have hb : b = b' := Subtype.ext hbb'
  subst b'
  have hv' : v = v' := Subtype.ext hv
  subst v'
  rfl

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathWitness G hbip hfour hsix
        (u := u)) := by
  intro p q hpq
  apply nonbacktrackingFourPathPair_injective G hfour
  exact congrArg Subtype.val hpq

lemma four_path_endpoint_witness_count_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (FourPathEndpointWitness G u) := by
  calc
    d * (d - 1) ^ 3 ≤
        Fintype.card (NonbacktrackingFourPath G u) :=
      card_nonbacktrackingFourPath_lower G d hdegree u
    _ ≤ Fintype.card (FourPathEndpointWitness G u) :=
      Fintype.card_le_of_injective
        (nonbacktrackingFourPathWitness G hbip hfour hsix)
        (nonbacktrackingFourPathWitness_injective G hbip hfour hsix)

omit [DecidableEq V] in
lemma fourPathEndpointWitness_card_eq_sum
    (G : SimpleGraph V) (u : V) :
    Fintype.card (FourPathEndpointWitness G u) =
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [Fintype.card_congr (fourPathEndpointWitnessEquiv G u),
    Fintype.card_sigma]

theorem four_path_common_second_neighbor_sum_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [← fourPathEndpointWitness_card_eq_sum G u]
  exact four_path_endpoint_witness_count_lower
    G hbip hfour hsix d hdegree u

end

noncomputable section
open Finset SimpleGraph

theorem finite_heavy_fiber_mass_half
    {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ)
    (hN : 0 < N)
    (hcapacity : Fintype.card α ≤ N)
    (htotal : p ≤ ∑ x : α, weight x) :
    (p : ℝ) / 2 ≤ finiteHeavyFiberMass weight N p := by
  classical
  let R : ℝ := fourPathHeavyThreshold N p
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hsum :
      (∑ x : α, (weight x : ℝ)) ≤
        (∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) +
          (Fintype.card α : ℝ) * R := by
    calc
      (∑ x : α, (weight x : ℝ)) ≤
          ∑ x : α,
            ((if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) + R) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · linarith
        · have : (weight x : ℝ) < R := lt_of_not_ge hx
          linarith
      _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hcapacityReal : (Fintype.card α : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcapacity
  have hthreshold : (N : ℝ) * R = (p : ℝ) / 2 := by
    dsimp [R, fourPathHeavyThreshold]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  have htotalReal :
      (p : ℝ) ≤ ∑ x : α, (weight x : ℝ) := by
    exact_mod_cast htotal
  change (p : ℝ) / 2 ≤
    ∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0
  nlinarith [mul_le_mul_of_nonneg_right hcapacityReal hR]

end

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma unrelated_four_path_endpoint_card_le
    (G : SimpleGraph V) (u : V) :
    Fintype.card (UnrelatedFourPathEndpoint G u) ≤ Fintype.card V := by
  exact Fintype.card_le_of_injective
    (fun v : UnrelatedFourPathEndpoint G u => (v : V))
    Subtype.val_injective

lemma four_path_heavy_common_second_neighbor_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 2 ≤
      finiteHeavyFiberMass
        (fun v : UnrelatedFourPathEndpoint G u =>
          Fintype.card (CommonSecondNeighbor G u (v : V)))
        (Fintype.card V) (d * (d - 1) ^ 3) := by
  apply finite_heavy_fiber_mass_half
  · exact Fintype.card_pos_iff.mpr ⟨u⟩
  · exact unrelated_four_path_endpoint_card_le G u
  · exact four_path_common_second_neighbor_sum_lower
      G hbip hfour hsix d hdegree u

end

noncomputable section
open Finset SimpleGraph

lemma choose_three_factorial_identity (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose t 3).symm

lemma choose_three_cubic_lower {t : ℕ} (ht : 3 ≤ t) :
    (t : ℝ) ^ 3 / 27 ≤ (t.choose 3 : ℝ) := by
  have hone : 1 ≤ t := by omega
  have htwo : 2 ≤ t := by omega
  have hidentity := congrArg (fun value : ℕ => (value : ℝ))
    (choose_three_factorial_identity t)
  norm_num [Nat.cast_sub hone, Nat.cast_sub htwo] at hidentity
  have htReal : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfactor :
      0 ≤ (t : ℝ) * ((t : ℝ) - 3) *
        (7 * (t : ℝ) - 6) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)
  nlinarith

end

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma four_path_common_second_neighbor_triple_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass G u : ℝ) := by
  classical
  let p : ℕ := d * (d - 1) ^ 3
  let R : ℝ := fourPathHeavyThreshold (Fintype.card V) p
  let weight : UnrelatedFourPathEndpoint G u → ℕ :=
    fun v => Fintype.card (CommonSecondNeighbor G u (v : V))
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hRthree : (3 : ℝ) ≤ R := by
    simpa [R, p] using hthreshold
  have hheavy :
      (p : ℝ) / 2 ≤
        finiteHeavyFiberMass weight (Fintype.card V) p := by
    simpa [weight, p] using
      (four_path_heavy_common_second_neighbor_mass_lower
        G hbip hfour hsix d hdegree u)
  have hpoint (v : UnrelatedFourPathEndpoint G u) :
      R ^ 2 *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) / 27 ≤
        ((weight v).choose 3 : ℝ) := by
    split_ifs with hv
    · have htReal : (3 : ℝ) ≤ (weight v : ℝ) := hRthree.trans hv
      have ht : 3 ≤ weight v := by exact_mod_cast htReal
      have hsquare : R ^ 2 ≤ (weight v : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hR
          (sub_nonneg.mpr hv),
          mul_nonneg (Nat.cast_nonneg (weight v))
            (sub_nonneg.mpr hv)]
      have hcubic :
          R ^ 2 * (weight v : ℝ) ≤ (weight v : ℝ) ^ 3 := by
        calc
          R ^ 2 * (weight v : ℝ) ≤
              (weight v : ℝ) ^ 2 * (weight v : ℝ) :=
            mul_le_mul_of_nonneg_right hsquare
              (Nat.cast_nonneg (weight v))
          _ = (weight v : ℝ) ^ 3 := by ring
      calc
        R ^ 2 * (weight v : ℝ) / 27 ≤
            (weight v : ℝ) ^ 3 / 27 := by linarith
        _ ≤ ((weight v).choose 3 : ℝ) :=
          choose_three_cubic_lower ht
    · simp
  change R ^ 2 * (p : ℝ) / 54 ≤
    (commonSecondNeighborTripleMass G u : ℝ)
  calc
    R ^ 2 * (p : ℝ) / 54 =
        (R ^ 2 / 27) * ((p : ℝ) / 2) := by ring
    _ ≤ (R ^ 2 / 27) *
        finiteHeavyFiberMass weight (Fintype.card V) p :=
      mul_le_mul_of_nonneg_left hheavy (by positivity)
    _ = ∑ v : UnrelatedFourPathEndpoint G u,
          R ^ 2 *
            (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) /
              27 := by
      simp only [finiteHeavyFiberMass, Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro v hv
        change (R ^ 2 / 27) *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) = _
        ring
    _ ≤ ∑ v : UnrelatedFourPathEndpoint G u,
          ((weight v).choose 3 : ℝ) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (commonSecondNeighborTripleMass G u : ℝ) := by
      simp [commonSecondNeighborTripleMass, weight]

theorem proposedFamilyFree_four_path_triple_mass_lower
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (u : Fin n)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass host u : ℝ) := by
  have hthreshold' : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card (Fin n))
        (d * (d - 1) ^ 3) := by
    simpa using hthreshold
  simpa using four_path_common_second_neighbor_triple_mass_lower
    host hbip (proposedFamilyFree_four_cycle hfree)
    (proposedFamilyFree_six_cycle hfree) d hdegree u hthreshold'

end

noncomputable section
open Finset SimpleGraph

lemma finite_bad_fiber_card_le_two
    {α β : Type*} [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    [DecidablePred good]
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex)
    (index : α) :
    ((fibers index).filter fun vertex => ¬ good vertex).card ≤ 2 := by
  classical
  by_cases hlarge : 3 ≤ (fibers index).card
  · have hempty :
        (fibers index).filter (fun vertex => ¬ good vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro vertex hvertex hbad
      exact hbad (hgood index vertex hvertex hlarge)
    simp [hempty]
  · have hcard :=
      Finset.card_filter_le (fibers index)
        (fun vertex => ¬ good vertex)
    omega

lemma finite_bad_fiber_mass_le_two
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex) :
    finiteBadFiberMass fibers good ≤ 2 * Fintype.card α := by
  classical
  simpa [finiteBadFiberMass, Nat.mul_comm] using
    Finset.sum_le_card_nsmul Finset.univ
      (fun index => ((fibers index).filter fun vertex => ¬ good vertex).card)
      2 (fun index _ => finite_bad_fiber_card_le_two fibers good hgood index)

end

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma independentThetaTripleOrderedWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by
  intro left right heq
  have hbase : independentThetaTripleBase G left =
      independentThetaTripleBase G right := by
    funext index
    fin_cases index
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.2.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.1) heq
  apply Subtype.ext
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G left hvertex
    rw [hbase]
    exact independentThetaTripleBase_mem G right index
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G right hvertex
    rw [← hbase]
    exact independentThetaTripleBase_mem G left index

lemma orderedThetaWitness_card
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by
  classical
  simp [OrderedThetaWitness, orderedThetaTripleCount,
    Fintype.card_sigma, Fintype.card_coe]

lemma independentThetaTriple_card_le_orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    Fintype.card (IndependentThetaTriple host) ≤
      orderedThetaTripleCount host := by
  calc
    Fintype.card (IndependentThetaTriple host) ≤
        Fintype.card (OrderedThetaWitness host) :=
      Fintype.card_le_of_injective
        (independentThetaTripleOrderedWitness host hbip hfour hsix)
        (independentThetaTripleOrderedWitness_injective
          host hbip hfour hsix)
    _ = orderedThetaTripleCount host := orderedThetaWitness_card host

theorem gamma_bad_triple_fiber_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by
  exact (finite_bad_fiber_mass_le_two _ _ (fun triple vertex hvertex hcard =>
    gammaGood_of_independentThetaTriple_fiber
      host hbip hfour hsix triple vertex hvertex hcard)).trans
    (Nat.mul_le_mul_left 2
      (independentThetaTriple_card_le_orderedThetaTripleCount
        host hbip hfour hsix))

omit [DecidableEq V] in
lemma commonSecondNeighborFinset_card
    (G : SimpleGraph V) (u v : V) :
    (commonSecondNeighborFinset G u v).card =
      Fintype.card (CommonSecondNeighbor G u v) := by
  classical
  rw [Fintype.card_subtype]
  rfl

lemma fourPathTripleToIndependentThetaTriple_endpoint_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    (endpoint : V) ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change (endpoint : V) ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).2

lemma badIndependentThetaTriple_other_center_unique
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G)
    (u : V)
    (hu : u ∈ commonCenterFinset G triple.val)
    (hbad : ¬ GammaGood G u)
    {v w : V}
    (hv : v ∈ commonCenterFinset G triple.val)
    (hw : w ∈ commonCenterFinset G triple.val)
    (huv : u ≠ v) (huw : u ≠ w) :
    v = w := by
  classical
  by_contra hvw
  have hsubset :
      ({u, v, w} : Finset V) ⊆ commonCenterFinset G triple.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hcard : 3 ≤ (commonCenterFinset G triple.val).card := by
    calc
      3 = ({u, v, w} : Finset V).card := by
        simp [huv, huw, hvw]
      _ ≤ (commonCenterFinset G triple.val).card :=
        Finset.card_le_card hsubset
  exact hbad (gammaGood_of_independentThetaTriple_fiber
    G hbip hfour hsix triple u hu hcard)

lemma badFourPathTripleToBadIndependentTriple_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (badFourPathTripleToBadIndependentTriple
        G hbip hfour hsix) := by
  rintro ⟨u, v, base⟩ ⟨u', v', base'⟩ heq
  have hcenter := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      (witness.2 : V)) heq
  change (u : V) = (u' : V) at hcenter
  have husub : u = u' := Subtype.ext hcenter
  subst u'
  have hbase := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      witness.1.val) heq
  change base.val = base'.val at hbase
  let triple := fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix (u : V) v base
  have hu : (u : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_center_mem
      G hbip hfour hsix (u : V) v base
  have hv : (v : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v base
  have hv' : (v' : V) ∈ commonCenterFinset G triple.val := by
    change (v' : V) ∈ commonCenterFinset G base.val
    rw [hbase]
    exact fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v' base'
  have hendpoint : (v : V) = (v' : V) :=
    badIndependentThetaTriple_other_center_unique
      G hbip hfour hsix triple (u : V) hu u.property hv hv'
      v.property.1 v'.property.1
  have hvsub : v = v' := Subtype.ext hendpoint
  subst v'
  have hbasesub : base = base' := Subtype.ext hbase
  subst base'
  rfl

omit [DecidableEq V] in
lemma badFourPathTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadFourPathTripleWitness G) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe,
    Finset.card_powersetCard, commonSecondNeighborFinset_card]
  change
    (∑ u : {u : V // ¬ GammaGood G u},
      commonSecondNeighborTripleMass G u) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u
  symm
  apply Finset.sum_subtype
    (gammaBadVertices G)
    (fun u => (mem_gammaBadVertices G u))

lemma badIndependentTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadIndependentTripleWitness G) =
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  classical
  rw [Fintype.card_sigma]
  unfold finiteBadFiberMass
  apply Finset.sum_congr
  · rfl
  · intro triple htriple
    rw [Fintype.card_subtype]
    congr 1
    ext center
    simp

lemma gammaBad_four_path_triple_mass_le_bad_fiber_mass
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    (∑ u ∈ gammaBadVertices G,
      commonSecondNeighborTripleMass G u) ≤
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  rw [← badFourPathTripleWitness_card,
    ← badIndependentTripleWitness_card]
  exact Fintype.card_le_of_injective
    (badFourPathTripleToBadIndependentTriple
      G hbip hfour hsix)
    (badFourPathTripleToBadIndependentTriple_injective
      G hbip hfour hsix)

theorem gammaBad_four_path_triple_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    (∑ u ∈ gammaBadVertices host,
      commonSecondNeighborTripleMass host u) ≤
      2 * orderedThetaTripleCount host := by
  exact (gammaBad_four_path_triple_mass_le_bad_fiber_mass
    host hbip hfour hsix).trans
      (gamma_bad_triple_fiber_mass_le_two_orderedTheta
        host hbip hfour hsix)

end

end Erdos180

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        (fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54) ≤
      2 * (orderedThetaTripleCount host : ℝ) := by
  classical
  let lower : ℝ :=
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54
  have hpoint (u : Fin n) :
      lower ≤ (commonSecondNeighborTripleMass host u : ℝ) := by
    exact proposedFamilyFree_four_path_triple_mass_lower
      host hfree hbip d hdegree u hthreshold
  change ((gammaBadVertices host).card : ℝ) * lower ≤
    2 * (orderedThetaTripleCount host : ℝ)
  calc
    ((gammaBadVertices host).card : ℝ) * lower =
        ∑ u ∈ gammaBadVertices host, lower := by simp
    _ ≤ ∑ u ∈ gammaBadVertices host,
        (commonSecondNeighborTripleMass host u : ℝ) := by
      gcongr with u hu
      exact hpoint u
    _ = ((∑ u ∈ gammaBadVertices host,
          commonSecondNeighborTripleMass host u) : ℝ) := by
      simp
    _ ≤ ((2 * orderedThetaTripleCount host : ℕ) : ℝ) := by
      exact_mod_cast
        (gammaBad_four_path_triple_mass_le_two_orderedTheta
          host hbip (proposedFamilyFree_four_cycle hfree)
          (proposedFamilyFree_six_cycle hfree))
    _ = 2 * (orderedThetaTripleCount host : ℝ) := by
      norm_num
