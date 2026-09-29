-- Prove2me | solution 1 for Erdos180.gammaBad_card_mul_fourpath_power_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:01:12.449205+00:00
-- url     : https://prove2.me/submissions/5d09e54a-cdd4-47c8-9993-90b6fcdb3a35

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Theorems.Thm_Erdos180_gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
import Theorems.Thm_Erdos180_gluedThetaBase_color_eq
import Theorems.Thm_Erdos180_jQuotient_mem_proposedFamily
import Theorems.Thm_Erdos180_thetaCopy_base_center_color_eq

namespace Erdos180

noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma commonNeighborIndependent_neighborhood_injective
    (G : SimpleGraph V) (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    Function.Injective
      (fun pair :
        (Σ x : {x : V // x ∈ vertices},
          G.neighborSet (x : V)) =>
          (pair.2 : V)) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ hab
  have hxy : (x : V) = (y : V) := by
    by_contra hne
    apply hindependent x.property y.property hne
    refine ⟨hne, (a : V), a.property, ?_⟩
    have hyb : G.Adj (y : V) (b : V) := b.property
    exact Eq.mp
      (congrArg (G.Adj (y : V)) hab.symm) hyb
  have hsub : x = y := Subtype.ext hxy
  subst y
  have hneighbor : a = b := Subtype.ext hab
  subst b
  rfl

lemma commonNeighborIndependent_sum_degree_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    (∑ x : {x : V // x ∈ vertices}, G.degree (x : V)) ≤
      Fintype.card V := by
  have hcard := Fintype.card_le_of_injective
    (fun pair :
      (Σ x : {x : V // x ∈ vertices},
        G.neighborSet (x : V)) =>
        (pair.2 : V))
    (commonNeighborIndependent_neighborhood_injective
      G vertices hindependent)
  simpa only [Fintype.card_sigma,
    SimpleGraph.card_neighborSet_eq_degree] using hcard

lemma commonNeighborIndependent_card_mul_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) :
    vertices.card * d ≤ Fintype.card V := by
  calc
    vertices.card * d = ∑ _x : {x : V // x ∈ vertices}, d := by simp
    _ ≤ ∑ x : {x : V // x ∈ vertices}, G.degree (x : V) :=
      Finset.sum_le_sum fun x _ => hdegree x
    _ ≤ Fintype.card V :=
      commonNeighborIndependent_sum_degree_le_card G vertices hindependent

end

noncomputable section
open SimpleGraph

lemma kernelNormalForm_jAdmissible
    {V : Type*} (g : JVertex → V)
    (hcolor : ∀ u v, g u = g v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => g (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v | InJCopy copy v}) :
    JAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro u v huv
    apply hbase
    exact (kernelNormalForm_eq_iff g _ _).mp huv
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

theorem proposedFamilyFree_no_jTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : jTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) : False := by
  let f := kernelNormalForm hom
  have hf : JAdmissible f :=
    kernelNormalForm_jAdmissible hom hcolor hbase hcopies
  have hmember := jQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph jTemplate f) host
    (kernelQuotientCopy jTemplate host hom)⟩

end

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_jThetaVertex
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (vertex : SubdivisionVertex 2) :
    gluedJVertex copies joining (jThetaVertex copy vertex) =
      copies copy vertex := by
  rcases vertex with (base | center) | pair
  · exact gluedJBase_jBase copies hfirst hsecond copy base
  · simp [jThetaVertex, gluedJVertex]
  · simp [jThetaVertex, gluedJVertex]

lemma inJCopy_iff_exists_jThetaVertex
    (copy : Fin 2) (vertex : JVertex) :
    InJCopy copy vertex ↔
      ∃ source : SubdivisionVertex 2,
        jThetaVertex copy source = vertex := by
  constructor
  · intro h
    rcases vertex with (base | center) | (pair | joining)
    · obtain ⟨source, hsource⟩ := h
      refine ⟨.inl (.inl source), ?_⟩
      simpa [jThetaVertex] using congrArg
        (fun value : Fin 4 => (Sum.inl (Sum.inl value) : JVertex))
        hsource.symm
    · rcases center with ⟨index, center⟩
      change copy = index at h
      subst index
      exact ⟨.inl (.inr center), rfl⟩
    · rcases pair with ⟨index, base, center⟩
      change copy = index at h
      subst index
      exact ⟨.inr (base, center), rfl⟩
    · exact False.elim h
  · rintro ⟨source, rfl⟩
    exact jThetaVertex_mem copy source

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by
  intro left hleft right hright heq
  change InJCopy copy left at hleft
  change InJCopy copy right at hright
  obtain ⟨source, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy left).mp hleft
  obtain ⟨target, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy right).mp hright
  change
    gluedJVertex copies joining (jThetaVertex copy source) =
      gluedJVertex copies joining (jThetaVertex copy target) at heq
  rw [gluedJVertex_jThetaVertex copies joining hfirst hsecond copy,
    gluedJVertex_jThetaVertex copies joining hfirst hsecond copy] at heq
  have hequal := (copies copy).injective heq
  subst target
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_injective
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by
  have hcopy (index : Fin 2) {i j : Fin 3}
      (hij : i ≠ j) :
      copies index (.inl (.inl i)) ≠
        copies index (.inl (.inl j)) := by
    intro h
    apply hij
    simpa using (copies index).injective h
  have h02 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) :=
    hcopy 0 (by decide)
  have h03 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h23 :
      copies 0 (.inl (.inl (1 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h12 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 1))
      (h.trans hfirst.symm)
  have h13 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 2))
      (h.trans hsecond.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [gluedJBase]

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (base : Fin 4) :
    color (gluedJBase copies base) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases base
  · rfl
  · exact gluedThetaBase_color_eq copies hfirst color 1 0
  · exact gluedThetaBase_color_eq copies hfirst color 0 1
  · exact gluedThetaBase_color_eq copies hfirst color 0 2

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (color : G.Coloring (Fin 2))
    (vertex : JVertex) :
    jColor vertex = false ↔
      color (gluedJVertex copies joining vertex) =
        color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  rcases vertex with (base | center) | (pair | star)
  · simpa [jColor, gluedJVertex] using
      gluedJBase_color_eq copies hfirst color base
  · rcases center with ⟨copy, center⟩
    simp only [jColor, gluedJVertex, true_iff]
    calc
      color (copies copy (.inl (.inr center))) =
          color (copies copy (.inl (.inl (0 : Fin 3)))) :=
        (thetaCopy_base_center_color_eq
          color (copies copy) 0 center).symm
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        gluedThetaBase_color_eq copies hfirst color copy 0
  · rcases pair with ⟨copy, base, center⟩
    simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    have hedge := (copies copy).toHom.map_rel
      (theta_base_pair_adj base center)
    have hvalid := color.valid hedge
    apply hvalid
    exact (gluedThetaBase_color_eq
      copies hfirst color copy base).trans heq.symm
  · simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    exact (color.valid hjoinFirst) heq.symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    ∀ left right,
      gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond left =
          gluedJHom copies joining hfirst hsecond
            hjoinFirst hjoinSecond right →
        jColor left = jColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hcolor :
      color (gluedJVertex copies joining left) =
        color (gluedJVertex copies joining right) :=
    congrArg color heq
  cases hleft : jColor left <;> cases hright : jColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mp hleft
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mpr
        (hcolor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mp hright
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mpr
        (hcolor.trans hbase)
    simp [hleft] at hfalse
  · rfl

lemma thetaBaseExtensions_commonNeighborIndependent
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (y z : Fin n) :
    CommonNeighborIndependent host (thetaBaseExtensions host y z) := by
  intro x x' hx hx' hdistinct
  rintro ⟨_, joining, hxjoin, hx'join⟩
  obtain ⟨first, hfirstX, hfirstY, hfirstZ⟩ :=
    (mem_thetaBaseExtensions host x y z).mp hx
  obtain ⟨second, hsecondX, hsecondY, hsecondZ⟩ :=
    (mem_thetaBaseExtensions host x' y z).mp hx'
  let copies : Fin 2 → SimpleGraph.Copy thetaGraph host :=
    ![first, second]
  have hsharedFirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    change second (.inl (.inl (1 : Fin 3))) =
      first (.inl (.inl (1 : Fin 3)))
    exact hsecondY.trans hfirstY.symm
  have hsharedSecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    change second (.inl (.inl (2 : Fin 3))) =
      first (.inl (.inl (2 : Fin 3)))
    exact hsecondZ.trans hfirstZ.symm
  have hjoinFirst :
      host.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (first (.inl (.inl (0 : Fin 3)))) joining
    rw [hfirstX]
    exact hxjoin
  have hjoinSecond :
      host.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (second (.inl (.inl (0 : Fin 3)))) joining
    rw [hsecondX]
    exact hx'join
  have hbaseDistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3))) := by
    change first (.inl (.inl (0 : Fin 3))) ≠
      second (.inl (.inl (0 : Fin 3)))
    rw [hfirstX, hsecondX]
    exact hdistinct
  apply proposedFamilyFree_no_jTemplate hfree
    (gluedJHom copies joining hsharedFirst hsharedSecond
      hjoinFirst hjoinSecond)
  · exact gluedJHom_color_respecting hbip copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond
  · change Function.Injective (gluedJBase copies)
    exact gluedJBase_injective copies hsharedFirst
      hsharedSecond hbaseDistinct
  · intro copy
    exact gluedJHom_injOn_marked_copy copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond copy

lemma thetaBaseExtensions_card_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (y z : Fin n) :
    (thetaBaseExtensions host y z).card * d ≤ n := by
  simpa using
    (commonNeighborIndependent_card_mul_degree_le
      host (thetaBaseExtensions host y z)
      (thetaBaseExtensions_commonNeighborIndependent
        host hfree hbip y z)
      d hdegree)

end

noncomputable section
open Finset SimpleGraph

lemma orderedThetaTripleCount_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    orderedThetaTripleCount host * d ≤ n ^ 3 := by
  classical
  calc
    orderedThetaTripleCount host * d =
        ∑ y : Fin n, ∑ z : Fin n,
          (thetaBaseExtensions host y z).card * d := by
      simp [orderedThetaTripleCount, Finset.sum_mul]
    _ ≤ ∑ _y : Fin n, ∑ _z : Fin n, n := by
      gcongr with y _ z _
      exact thetaBaseExtensions_card_mul_degree_le
        host hfree hbip d hdegree y z
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]

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
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by
  have hn : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [fourPathHeavyThreshold] at hthreshold
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let p : ℕ := d * (d - 1) ^ 3
  let bad : ℕ := (gammaBadVertices host).card
  let theta : ℕ := orderedThetaTripleCount host
  have hmass :
      (bad : ℝ) *
        (fourPathHeavyThreshold n p ^ 2 *
          (p : ℝ) / 54) ≤ 2 * (theta : ℝ) := by
    exact gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
      host hfree hbip d hdegree hthreshold
  have hnormalized :
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) ≤ 2 * (theta : ℝ) := by
    calc
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) =
        (bad : ℝ) *
          (fourPathHeavyThreshold n p ^ 2 * (p : ℝ) / 54) := by
            unfold fourPathHeavyThreshold
            field_simp [ne_of_gt hnReal]
            ring
      _ ≤ 2 * (theta : ℝ) := hmass
  have hden : 0 < (216 : ℝ) * (n : ℝ) ^ 2 := by
    positivity
  have hclear := (div_le_iff₀ hden).mp hnormalized
  have hbadpoly :
      (bad : ℝ) * (p : ℝ) ^ 3 ≤
        432 * (theta : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have htheta :
      (theta : ℝ) * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast
      (orderedThetaTripleCount_mul_degree_le
        host hfree hbip d hdegree)
  have hfinal :
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 5 := by
    calc
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
          (432 * (theta : ℝ) * (n : ℝ) ^ 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbadpoly (Nat.cast_nonneg d)
      _ = 432 * ((theta : ℝ) * (d : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ 432 * (n : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
        gcongr
      _ = 432 * (n : ℝ) ^ 5 := by ring
  exact_mod_cast hfinal
