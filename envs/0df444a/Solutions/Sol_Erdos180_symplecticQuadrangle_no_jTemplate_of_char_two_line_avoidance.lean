-- Prove2me | solution 1 for Erdos180.symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:15:21.948811+00:00
-- url     : https://prove2.me/submissions/9e838309-f551-4c40-8263-df0c9e56b8bc

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.Thm_Erdos180_subdivisionGraph_base_pair_adj
import Theorems.Thm_Erdos180_subdivisionGraph_center_pair_adj
import Theorems.Thm_Erdos180_subdivisionLine_base_of_line_center
import Theorems.Thm_Erdos180_subdivisionLine_bases_disjoint
import Theorems.Thm_Erdos180_subdivisionLine_center_of_line_base
import Theorems.Thm_Erdos180_subdivisionLine_centers_injective
import Theorems.Thm_Erdos180_subdivisionLine_pair_incidence
import Theorems.Thm_Erdos180_subdivisionPoint_base_center_related
import Theorems.Thm_Erdos180_subdivisionPoint_center_of_point_base
import Theorems.Thm_Erdos180_subdivisionPoint_pair_incidence
import Theorems.Thm_Erdos180_symplecticPointRelated_symm
import Theorems.Thm_Erdos180_symplecticPoint_sup_finrank
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_point
import Theorems.Thm_Erdos180_symplectic_triangle_lines_eq

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem standardSymplecticBilin_isAlt :
    (standardSymplecticBilin K).IsAlt := by
  intro u
  exact standardSymplecticForm_self K u

lemma symplecticPointRelated_iff_orthogonal
    (p q : SymplecticPoint K) :
    SymplecticPointRelated K p q ↔
      p ≠ q ∧ p.1 ≤ SymplecticPointOrthogonal K q := by
  constructor
  · rintro ⟨hpq, L, hpL, hqL⟩
    refine ⟨hpq, ?_⟩
    intro x hx
    change ∀ y ∈ q.1, standardSymplecticForm K y x = 0
    intro y hy
    exact L.2.2 y (hqL hy) x (hpL hx)
  · rintro ⟨hpq, hporth⟩
    let U : Submodule K (SymplecticVector K) := p.1 ⊔ q.1
    have hdim : Module.finrank K U = 2 :=
      symplecticPoint_sup_finrank K hpq
    have hqU : q.1 ≤ U := le_sup_right
    have hUorth : U ≤ SymplecticPointOrthogonal K q :=
      sup_le hporth (symplecticPoint_le_orthogonal K q)
    exact ⟨hpq,
      ⟨U, hdim, symplectic_two_plane_isotropic K hdim hqU hUorth⟩,
      le_sup_left, le_sup_right⟩

lemma symplecticPointRelated_of_quadrangle_common_neighbor
    {p q : SymplecticPoint K}
    (hpq : p ≠ q) {v : QuadrangleVertex K}
    (hpv : (symplecticQuadrangle K).Adj (.inl p) v)
    (hqv : (symplecticQuadrangle K).Adj (.inl q) v) :
    SymplecticPointRelated K p q := by
  obtain ⟨L, hv, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hpv
  rw [hv] at hqv
  exact ⟨hpq, L, hpL,
    (symplecticQuadrangle_incidence_adj K q L).mp hqv⟩

lemma subdivisionPoint_base_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ q : SymplecticPoint K,
      copy (.inl (.inl otherBase)) = .inl q := by
  obtain ⟨c, hc⟩ := subdivisionPoint_center_of_point_base K
    copy (center := center) hbase
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (otherBase, center))) at hcenteradj
  rw [hc] at hcenteradj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj
  have hotheradj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl otherBase)))
    (copy (.inr (otherBase, center))) at hotheradj
  rw [hpair] at hotheradj
  obtain ⟨q, hq, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hotheradj.symm
  exact ⟨q, hq⟩

lemma subdivisionPoint_bases_unrelated
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (p : Fin 3 → SymplecticPoint K)
    (c : Fin k → SymplecticPoint K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inl (c center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    ¬ SymplecticPointRelated K (p i) (p j) := by
  obtain ⟨Li, hi_pair, hpiLi, hcLi⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase i)
      (hcenter center)
  obtain ⟨Lj, hj_pair, hpjLj, hcLj⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase j)
      (hcenter center)
  have hic : SymplecticPointRelated K (p i) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase i)
      (hcenter center)
  have hjc : SymplecticPointRelated K (p j) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase j)
      (hcenter center)
  rintro ⟨_, Lij, hpiLij, hpjLij⟩
  have hlines : Li = Lj :=
    symplectic_triangle_lines_eq K hic.1
      (symplecticPointRelated_symm K hjc).1
      hpiLi hcLi hpiLij hpjLij hcLj hpjLj
  have hpair :
      copy (.inr (i, center)) = copy (.inr (j, center)) := by
    rw [hi_pair, hj_pair, hlines]
  have hsource :
      (Sum.inr (i, center) : SubdivisionVertex k) =
        .inr (j, center) := copy.injective hpair
  exact hij (congrArg Prod.fst (Sum.inr.inj hsource))

lemma symplecticPointSpan_orthogonal_finrank
    {y z : SymplecticPoint K} (hyz : y ≠ z) :
    Module.finrank K
      ((standardSymplecticBilin K).orthogonal
        (y.1 ⊔ z.1)) = 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K),
    symplecticPoint_sup_finrank K hyz]
  simp [SymplecticVector]

lemma symplecticPoint_centers_span_orthogonal
    {y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    c.1 ⊔ d.1 =
      (standardSymplecticBilin K).orthogonal (y.1 ⊔ z.1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hcy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hcz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hdy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hdz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
  · rw [symplecticPoint_sup_finrank K hcd,
      symplecticPointSpan_orthogonal_finrank K hyz]

lemma symplecticPoint_mem_span_of_two_centers
    {x y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcx : c.1 ≤ SymplecticPointOrthogonal K x)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdx : d.1 ≤ SymplecticPointOrthogonal K x)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    x.1 ≤ y.1 ⊔ z.1 := by
  have hcenters := symplecticPoint_centers_span_orthogonal K
    hyz hcd hcy hcz hdy hdz
  have hxorth :
      x.1 ≤ (standardSymplecticBilin K).orthogonal (c.1 ⊔ d.1) := by
    intro w hw
    change ∀ u ∈ c.1 ⊔ d.1,
      standardSymplecticForm K u w = 0
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [standardSymplecticForm_add_left]
    have haorth : standardSymplecticForm K a w = 0 := by
      have h := hcx ha w hw
      change standardSymplecticForm K w a = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    have hborth : standardSymplecticForm K b w = 0 := by
      have h := hdx hb w hw
      change standardSymplecticForm K w b = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    rw [haorth, hborth, add_zero]
  rw [hcenters,
    LinearMap.BilinForm.orthogonal_orthogonal
      (standardSymplecticBilin_nondegenerate K)
      (standardSymplecticBilin_isAlt K).isRefl] at hxorth
  exact hxorth

theorem symplecticPoint_point_class_avoidance
    {x x' y z c d c' d' : SymplecticPoint K}
    (hyz : y ≠ z)
    (hyz_unrelated : ¬ SymplecticPointRelated K y z)
    (hxx' : x ≠ x')
    (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hcx : SymplecticPointRelated K c x)
    (hcy : SymplecticPointRelated K c y)
    (hcz : SymplecticPointRelated K c z)
    (hdx : SymplecticPointRelated K d x)
    (hdy : SymplecticPointRelated K d y)
    (hdz : SymplecticPointRelated K d z)
    (hc'x' : SymplecticPointRelated K c' x')
    (hc'y : SymplecticPointRelated K c' y)
    (hc'z : SymplecticPointRelated K c' z)
    (hd'x' : SymplecticPointRelated K d' x')
    (hd'y : SymplecticPointRelated K d' y)
    (hd'z : SymplecticPointRelated K d' z) :
    ¬ SymplecticPointRelated K x x' := by
  have hxspan : x.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hcd
      ((symplecticPointRelated_iff_orthogonal K c x).mp hcx).2
      ((symplecticPointRelated_iff_orthogonal K c y).mp hcy).2
      ((symplecticPointRelated_iff_orthogonal K c z).mp hcz).2
      ((symplecticPointRelated_iff_orthogonal K d x).mp hdx).2
      ((symplecticPointRelated_iff_orthogonal K d y).mp hdy).2
      ((symplecticPointRelated_iff_orthogonal K d z).mp hdz).2
  have hx'span : x'.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hc'd'
      ((symplecticPointRelated_iff_orthogonal K c' x').mp hc'x').2
      ((symplecticPointRelated_iff_orthogonal K c' y).mp hc'y).2
      ((symplecticPointRelated_iff_orthogonal K c' z).mp hc'z).2
      ((symplecticPointRelated_iff_orthogonal K d' x').mp hd'x').2
      ((symplecticPointRelated_iff_orthogonal K d' y).mp hd'y).2
      ((symplecticPointRelated_iff_orthogonal K d' z).mp hd'z).2
  intro hrelated
  obtain ⟨_, L, hxL, hx'L⟩ := hrelated
  have hspan : x.1 ⊔ x'.1 = y.1 ⊔ z.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hxspan hx'span)
    rw [symplecticPoint_sup_finrank K hxx',
      symplecticPoint_sup_finrank K hyz]
  have hyzL : y.1 ⊔ z.1 ≤ L.1 := by
    rw [← hspan]
    exact sup_le hxL hx'L
  exact hyz_unrelated
    ⟨hyz, L, le_sup_left.trans hyzL, le_sup_right.trans hyzL⟩

theorem symplecticQuadrangle_no_point_jTemplate
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (p : Fin 4 → SymplecticPoint K)
    (c : Fin 2 → Fin 2 → SymplecticPoint K)
    (hbase : ∀ base : Fin 4,
      hom (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ (copy center : Fin 2),
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center)) : False := by
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) (base : Fin 3) :
      θ copy (.inl (.inl base)) =
        .inl (p (jBase copy base)) := by
    change hom (jThetaVertex copy (.inl (.inl base))) = _
    simpa [jThetaVertex] using hbase (jBase copy base)
  have hθcenter (copy center : Fin 2) :
      θ copy (.inl (.inr center)) =
        .inl (c copy center) := by
    change hom (jThetaVertex copy (.inl (.inr center))) = _
    simpa [jThetaVertex] using hcenter copy center
  have hcenters_inj (copy : Fin 2) :
      Function.Injective (c copy) := by
    intro i j hij
    have himage :
        θ copy (.inl (.inr i)) =
          θ copy (.inl (.inr j)) := by
      rw [hθcenter copy i, hθcenter copy j, hij]
    have hsource :
        (Sum.inl (Sum.inr i) : SubdivisionVertex 2) =
          .inl (.inr j) := (θ copy).injective himage
    exact Sum.inr.inj (Sum.inl.inj hsource)
  have hpoints_inj : Function.Injective p := by
    intro i j hij
    apply hbase_inj
    change hom (.inl (.inl i)) = hom (.inl (.inl j))
    rw [hbase i, hbase j, hij]
  have hyz : p 2 ≠ p 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hpoints_inj h)
  have hxx' : p 0 ≠ p 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hpoints_inj h)
  have hyz_unrelated :
      ¬ SymplecticPointRelated K (p 2) (p 3) := by
    have h := subdivisionPoint_bases_unrelated K (θ 0)
      (fun base => p (jBase 0 base)) (c 0)
      (hθbase 0) (hθcenter 0)
      (by decide : (1 : Fin 3) ≠ 2) 0
    simpa [jBase] using h
  have hrelated (copy : Fin 2) (base : Fin 3)
      (center : Fin 2) :
      SymplecticPointRelated K
        (c copy center) (p (jBase copy base)) :=
    symplecticPointRelated_symm K
      (subdivisionPoint_base_center_related K
        (θ copy) (hθbase copy base) (hθcenter copy center))
  have hcd : c 0 0 ≠ c 0 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 0 h)
  have hc'd' : c 1 0 ≠ c 1 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 1 h)
  have havoid := symplecticPoint_point_class_avoidance K
    (x := p 0) (x' := p 1) (y := p 2) (z := p 3)
    (c := c 0 0) (d := c 0 1)
    (c' := c 1 0) (d' := c 1 1)
    hyz hyz_unrelated hxx' hcd hc'd'
    (by simpa [jBase] using hrelated 0 0 0)
    (by simpa [jBase] using hrelated 0 1 0)
    (by simpa [jBase] using hrelated 0 2 0)
    (by simpa [jBase] using hrelated 0 0 1)
    (by simpa [jBase] using hrelated 0 1 1)
    (by simpa [jBase] using hrelated 0 2 1)
    (by simpa [jBase] using hrelated 1 0 0)
    (by simpa [jBase] using hrelated 1 1 0)
    (by simpa [jBase] using hrelated 1 2 0)
    (by simpa [jBase] using hrelated 1 0 1)
    (by simpa [jBase] using hrelated 1 1 1)
    (by simpa [jBase] using hrelated 1 2 1)
  have hjoin0 : jTemplate.Adj
      (.inl (.inl (0 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoin1 : jTemplate.Adj
      (.inl (.inl (1 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hleft := hom.map_rel hjoin0
  have hright := hom.map_rel hjoin1
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hleft
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hright
  rw [hbase 0] at hleft
  rw [hbase 1] at hright
  exact havoid
    (symplecticPointRelated_of_quadrangle_common_neighbor K
      hxx' hleft hright)

theorem symplecticQuadrangle_no_point_jTemplate_of_bases
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hpoint : ∀ base : Fin 4,
      ∃ p : SymplecticPoint K,
        hom (.inl (.inl base)) = .inl p) : False := by
  classical
  let p : Fin 4 → SymplecticPoint K :=
    fun base => Classical.choose (hpoint base)
  have hp (base : Fin 4) :
      hom (.inl (.inl base)) = .inl (p base) :=
    Classical.choose_spec (hpoint base)
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) :
      θ copy (.inl (.inl (0 : Fin 3))) =
        .inl (p (jBase copy 0)) := by
    change hom (jThetaVertex copy (.inl (.inl 0))) = _
    simpa [jThetaVertex] using hp (jBase copy 0)
  have hcenter_exists (copy center : Fin 2) :
      ∃ q : SymplecticPoint K,
        hom (.inl (.inr (copy, center))) = .inl q := by
    have h := subdivisionPoint_center_of_point_base K
      (θ copy) (center := center) (hθbase copy)
    change ∃ q : SymplecticPoint K,
      hom (jThetaVertex copy (.inl (.inr center))) = .inl q at h
    simpa [jThetaVertex] using h
  let c : Fin 2 → Fin 2 → SymplecticPoint K :=
    fun copy center => Classical.choose (hcenter_exists copy center)
  have hc (copy center : Fin 2) :
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center) :=
    Classical.choose_spec (hcenter_exists copy center)
  exact symplecticQuadrangle_no_point_jTemplate K hom
    hbase_inj hcopies p c hp hc

theorem symplecticQuadrangle_no_point_jTemplate_of_first_base
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hfirst : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (0 : Fin 4))) = .inl p) : False := by
  obtain ⟨p₀, hp₀⟩ := hfirst
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hx : θ 0 (.inl (.inl (0 : Fin 3))) = .inl p₀ := by
    change hom (jThetaVertex 0 (.inl (.inl 0))) = _
    simpa [jThetaVertex, jBase] using hp₀
  have hy : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (2 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (1 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  have hz : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (3 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (2 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  obtain ⟨py, hpy⟩ := hy
  have hy' : θ 1 (.inl (.inl (1 : Fin 3))) = .inl py := by
    change hom (jThetaVertex 1 (.inl (.inl 1))) = _
    simpa [jThetaVertex, jBase] using hpy
  have hx' : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (1 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 1)
      (otherBase := (0 : Fin 3)) 0 hy'
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  apply symplecticQuadrangle_no_point_jTemplate_of_bases K
    hom hbase_inj hcopies
  intro base
  fin_cases base
  · exact ⟨p₀, hp₀⟩
  · exact hx'
  · exact ⟨py, hpy⟩
  · exact hz

theorem symplecticQuadrangle_jTemplate_first_base_is_line
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) :
    ∃ L : SymplecticLine K,
      hom (.inl (.inl (0 : Fin 4))) = .inr L := by
  cases h : hom (.inl (.inl (0 : Fin 4))) with
  | inl p =>
      exact False.elim
        (symplecticQuadrangle_no_point_jTemplate_of_first_base K
          hom hbase_inj hcopies ⟨p, h⟩)
  | inr L => exact ⟨L, rfl⟩

lemma subdivisionLine_base_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ M : SymplecticLine K,
      copy (.inl (.inl otherBase)) = .inr M := by
  obtain ⟨C, hC⟩ := subdivisionLine_center_of_line_base K
    copy (center := center) hbase
  exact subdivisionLine_base_of_line_center K
    copy (base := otherBase) hC

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (havoid : CharTwoLinePairAvoidance K)
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun i : Fin 4 => hom (.inl (.inl i))))
    (hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v | InJCopy i v}) :
    False := by
  classical
  let θ (i : Fin 2) := jThetaHomCopy hom hcopies i
  obtain ⟨X, hX⟩ :=
    symplecticQuadrangle_jTemplate_first_base_is_line
      K hom hbase_inj hcopies
  have hθ0X :
      θ 0 (.inl (.inl (0 : Fin 3))) = .inr X := by
    change
      hom (jThetaVertex 0 (.inl (.inl (0 : Fin 3)))) =
        .inr X
    simpa [jThetaVertex, jBase] using hX
  obtain ⟨Y, hθ0Y⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (1 : Fin 3)) (0 : Fin 2) hθ0X
  have hY :
      hom (.inl (.inl (2 : Fin 4))) = .inr Y := by
    change
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) =
        .inr Y at hθ0Y
    simpa [jThetaVertex, jBase] using hθ0Y
  obtain ⟨Z, hθ0Z⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (2 : Fin 3)) (0 : Fin 2) hθ0X
  have hZ :
      hom (.inl (.inl (3 : Fin 4))) = .inr Z := by
    change
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) =
        .inr Z at hθ0Z
    simpa [jThetaVertex, jBase] using hθ0Z
  have hθ1Y :
      θ 1 (.inl (.inl (1 : Fin 3))) = .inr Y := by
    change
      hom (jThetaVertex 1 (.inl (.inl (1 : Fin 3)))) =
        .inr Y
    simpa [jThetaVertex, jBase] using hY
  obtain ⟨X', hθ1X'⟩ :=
    subdivisionLine_base_of_line_base K (θ 1)
      (otherBase := (0 : Fin 3)) (0 : Fin 2) hθ1Y
  have hX' :
      hom (.inl (.inl (1 : Fin 4))) = .inr X' := by
    change
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) =
        .inr X' at hθ1X'
    simpa [jThetaVertex, jBase] using hθ1X'
  let B : Fin 3 → SymplecticLine K := ![X, Y, Z]
  let B' : Fin 3 → SymplecticLine K := ![X', Y, Z]
  have hθ1Z :
      θ 1 (.inl (.inl (2 : Fin 3))) = .inr Z := by
    change
      hom (jThetaVertex 1 (.inl (.inl (2 : Fin 3)))) =
        .inr Z
    simpa [jThetaVertex, jBase] using hZ
  have hB : ∀ i : Fin 3,
      θ 0 (.inl (.inl i)) = .inr (B i) := by
    intro i
    fin_cases i
    · simpa [B] using hθ0X
    · simpa [B] using hθ0Y
    · simpa [B] using hθ0Z
  have hB' : ∀ i : Fin 3,
      θ 1 (.inl (.inl i)) = .inr (B' i) := by
    intro i
    fin_cases i
    · simpa [B'] using hθ1X'
    · simpa [B'] using hθ1Y
    · simpa [B'] using hθ1Z
  have hC_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 0 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 0)
      (base := (0 : Fin 3)) (center := i) (hB 0)
  choose C hC using hC_exists
  have hC'_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 1 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 1)
      (base := (0 : Fin 3)) (center := i) (hB' 0)
  choose C' hC' using hC'_exists
  have hXX' : X ≠ X' := by
    intro heq
    have hbaseeq : (0 : Fin 4) = 1 := by
      apply hbase_inj
      change
        hom (.inl (.inl (0 : Fin 4))) =
          hom (.inl (.inl (1 : Fin 4)))
      rw [hX, hX', heq]
    exact (by decide : (0 : Fin 4) ≠ 1) hbaseeq
  have hYZ : Disjoint Y.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (1 : Fin 3) ≠ 2) (0 : Fin 2)
  have hXY : Disjoint X.1 Y.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hXZ : Disjoint X.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hX'Y : Disjoint X'.1 Y.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hX'Z : Disjoint X'.1 Z.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hdisjoint : Disjoint X.1 X'.1 := by
    apply havoid Y Z X X'
      hYZ hXY hXZ hX'Y hX'Z hXX' C C'
      (subdivisionLine_centers_injective K (θ 0) C hC)
      (subdivisionLine_centers_injective K (θ 1) C' hC')
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 1) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 2) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 0) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 1) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 2) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 0) (hC' i)
      exact ⟨p, hpB, hpC⟩
  have hjoinX : jTemplate.Adj
      (.inl (.inl (0 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoinX' : jTemplate.Adj
      (.inl (.inl (1 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hadjX := hom.map_rel hjoinX
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX
  rw [hX] at hadjX
  obtain ⟨p, hpjoin, hpX⟩ :=
    symplecticQuadrangle_adjacent_to_line K hadjX
  have hadjX' := hom.map_rel hjoinX'
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX'
  rw [hX', hpjoin] at hadjX'
  have hpX' : p.1 ≤ X'.1 :=
    (symplecticQuadrangle_incidence_adj K p X').mp
      hadjX'.symm
  have hpzero :
      p.1 = (⊥ : Submodule K (SymplecticVector K)) :=
    eq_bot_iff.mpr
      ((le_inf hpX hpX').trans hdisjoint.le_bot)
  have hdim := p.2
  rw [hpzero] at hdim
  simp at hdim
