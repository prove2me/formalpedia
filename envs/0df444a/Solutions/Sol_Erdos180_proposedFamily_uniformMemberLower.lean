-- Prove2me | solution 1 for Erdos180.proposedFamily_uniformMemberLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:22:56.379945+00:00
-- url     : https://prove2.me/submissions/7976857f-76a4-4f2f-9119-10a498e119d2

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.Thm_Erdos180_coordinateCenterLine_direction_det_ne_zero_of_ne
import Theorems.Thm_Erdos180_cycleGraph_no_isolated
import Theorems.Thm_Erdos180_encodeFiniteGraph_no_isolated
import Theorems.Thm_Erdos180_jQuotient_mem_proposedFamily
import Theorems.Thm_Erdos180_kQuotient_mem_proposedFamily
import Theorems.Thm_Erdos180_projectiveDirection_nonzero_left
import Theorems.Thm_Erdos180_projectiveDirection_nonzero_right
import Theorems.Thm_Erdos180_proposedFamily_even_characteristic_avoidance
import Theorems.Thm_Erdos180_proposedFamily_induction
import Theorems.Thm_Erdos180_quadrangle_uniform_lower_of_prime_power_avoidance
import Theorems.Thm_Erdos180_quotientGraph_no_isolated
import Theorems.Thm_Erdos180_subdivisionLine_base_of_line_center
import Theorems.Thm_Erdos180_subdivisionLine_bases_disjoint
import Theorems.Thm_Erdos180_subdivisionLine_center_of_line_base
import Theorems.Thm_Erdos180_subdivisionLine_centers_injective
import Theorems.Thm_Erdos180_subdivisionLine_pair_incidence
import Theorems.Thm_Erdos180_symmetricGraphLine_coordinateCenter_common_point_iff
import Theorems.Thm_Erdos180_symplecticAutomorphismLineEquiv_apply
import Theorems.Thm_Erdos180_symplecticAutomorphism_disjoint_iff
import Theorems.Thm_Erdos180_symplecticAutomorphism_incidence_iff
import Theorems.Thm_Erdos180_symplecticLineNormalizer_map_left
import Theorems.Thm_Erdos180_symplecticLineNormalizer_map_right
import Theorems.Thm_Erdos180_symplecticLine_eq_coordinateCenterLine_of_common_points
import Theorems.Thm_Erdos180_symplecticLine_eq_invertible_symmetricGraphLine
import Theorems.Thm_Erdos180_symplecticLine_eq_of_points
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_point
import Theorems.Thm_Erdos180_symplecticQuadrangle_encodeFiniteGraph_free_iff
import Theorems.Thm_Erdos180_symplectic_triangle_lines_eq

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem symplecticQuadrangle_common_neighbor_unique
    {u v : QuadrangleVertex K} (huv : u ≠ v)
    {w z : QuadrangleVertex K}
    (huw : (symplecticQuadrangle K).Adj u w)
    (hvw : (symplecticQuadrangle K).Adj v w)
    (huz : (symplecticQuadrangle K).Adj u z)
    (hvz : (symplecticQuadrangle K).Adj v z) : w = z := by
  rcases u with p | L <;>
    rcases v with q | M <;>
    rcases w with r | R <;>
    rcases z with s | S <;>
    simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at huw hvw huz hvz
  · apply congrArg Sum.inr
    apply symplecticLine_eq_of_points K
      (fun hpq => huv (congrArg Sum.inl hpq))
    · exact huw
    · exact hvw
    · exact huz
    · exact hvz
  · apply congrArg Sum.inl
    by_contra hrs
    have hlines : L = M := symplecticLine_eq_of_points K hrs
      huw huz hvw hvz
    exact huv (congrArg Sum.inr hlines)

theorem symplecticQuadrangle_four_cycle_free :
    (SimpleGraph.cycleGraph 4).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h21 : (symplecticQuadrangle K).Adj (copy 2) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h03 : (symplecticQuadrangle K).Adj (copy 0) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h02 : copy 0 ≠ copy 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (copy.injective h)
  have h13 : copy 1 = copy 3 :=
    symplecticQuadrangle_common_neighbor_unique K h02 h01 h21 h03 h23
  exact (by decide : (1 : Fin 4) ≠ 3) (copy.injective h13)

theorem symplecticQuadrangle_six_cycle_free :
    (SimpleGraph.cycleGraph 6).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 0 1 by decide)
  have h12 : (symplecticQuadrangle K).Adj (copy 1) (copy 2) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 1 2 by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 2 3 by decide)
  have h34 : (symplecticQuadrangle K).Adj (copy 3) (copy 4) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 3 4 by decide)
  have h45 : (symplecticQuadrangle K).Adj (copy 4) (copy 5) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 4 5 by decide)
  have h50 : (symplecticQuadrangle K).Adj (copy 5) (copy 0) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 5 0 by decide)
  cases h0 : copy 0 with
  | inl p =>
      rw [h0] at h01 h50
      obtain ⟨L, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_point K h01
      rw [h1] at h12
      obtain ⟨q, h2, hqL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h12
      rw [h2] at h23
      obtain ⟨M, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h23
      rw [h3] at h34
      obtain ⟨r, h4, hrM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h34
      rw [h4] at h45
      obtain ⟨N, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h45
      rw [h5] at h50
      have hpN : p.1 ≤ N.1 :=
        (symplecticQuadrangle_incidence_adj K p N).mp h50.symm
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (0 : Fin 6) ≠ 2)
        apply copy.injective
        change copy 0 = copy 2
        rw [h0, h2, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (2 : Fin 6) ≠ 4)
        apply copy.injective
        change copy 2 = copy 4
        rw [h2, h4, heq]
      have hLM : L = M := symplectic_triangle_lines_eq K hpq hqr
        hpL hqL hpN hrN hqM hrM
      apply (by decide : (1 : Fin 6) ≠ 3)
      apply copy.injective
      change copy 1 = copy 3
      rw [h1, h3, hLM]
  | inr L =>
      rw [h0] at h01 h50
      obtain ⟨p, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h01
      rw [h1] at h12
      obtain ⟨M, h2, hpM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h12
      rw [h2] at h23
      obtain ⟨q, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h23
      rw [h3] at h34
      obtain ⟨N, h4, hqN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h34
      rw [h4] at h45
      obtain ⟨r, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_line K h45
      rw [h5] at h50
      have hrL : r.1 ≤ L.1 :=
        (symplecticQuadrangle_incidence_adj K r L).mp h50
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (1 : Fin 6) ≠ 3)
        apply copy.injective
        change copy 1 = copy 3
        rw [h1, h3, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (3 : Fin 6) ≠ 5)
        apply copy.injective
        change copy 3 = copy 5
        rw [h3, h5, heq]
      have hMN : M = N := symplectic_triangle_lines_eq K hpq hqr
        hpM hqM hpL hrL hqN hrN
      apply (by decide : (2 : Fin 6) ≠ 4)
      apply copy.injective
      change copy 2 = copy 4
      rw [h2, h4, hMN]

theorem symplecticQuadrangle_kTemplate_has_line_gamma
    (hom : kTemplate →g symplecticQuadrangle K)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) :
    ∃ (i : Fin 2) (L : SymplecticLine K),
      (kGammaHomCopy hom hcopies i) kSpecifiedCenter = .inr L := by
  have hjoin : kTemplate.Adj
      ((0 : Fin 2), kSpecifiedCenter)
      ((1 : Fin 2), kSpecifiedCenter) := by
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kSpecifiedCenter]
  have hadj := hom.map_rel hjoin
  change (symplecticQuadrangle K).Adj
    (hom ((0 : Fin 2), kSpecifiedCenter))
    (hom ((1 : Fin 2), kSpecifiedCenter)) at hadj
  cases hzero : hom ((0 : Fin 2), kSpecifiedCenter) with
  | inl p =>
      rw [hzero] at hadj
      obtain ⟨L, hL, _⟩ :=
        symplecticQuadrangle_adjacent_to_point K hadj
      refine ⟨1, L, ?_⟩
      change hom (kGammaVertex 1 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hL
  | inr L =>
      refine ⟨0, L, ?_⟩
      change hom (kGammaVertex 0 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hzero

end

noncomputable section
open SimpleGraph

lemma jTemplate_no_isolated :
    GraphHasNoIsolated jTemplate := by
  intro u
  rcases u with (base | ⟨copy, center⟩) |
    (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inl (0, (1, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
    · refine ⟨.inr (.inl (0, (2, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
  · refine ⟨.inr (.inl (copy, (0, center))), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl (jBase copy base)), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl 0), ?_⟩
    cases lastVertex
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]

lemma kTemplate_no_isolated :
    GraphHasNoIsolated kTemplate := by
  intro u
  rcases u with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · refine ⟨(copy, .inr (base, 0)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inr (0, center)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inl (.inl base)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]

lemma encodedJQuotient_no_isolated
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph jTemplate f)
    (quotientGraph_no_isolated jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h)
      jTemplate_no_isolated f hf.1)

lemma encodedKQuotient_no_isolated
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph kTemplate f)
    (quotientGraph_no_isolated kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h)
      kTemplate_no_isolated f hf.1)

theorem proposedFamily_member_no_isolated
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    GraphHasNoIsolated forbidden.graph :=
  proposedFamily_induction (P := fun graph => GraphHasNoIsolated graph.graph)
    (cycleGraph_no_isolated 2) (cycleGraph_no_isolated 4)
    (fun _ hf => encodedJQuotient_no_isolated hf)
    (fun _ hf => encodedKQuotient_no_isolated hf)
    forbidden hforbidden

theorem four_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 4)
    (by simpa using cycleGraph_no_isolated 2)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_four_cycle_free _) hn

theorem six_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 6)
    (by simpa using cycleGraph_no_isolated 4)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_six_cycle_free _) hn

end

section
variable {K : Type*} [Field K]

lemma symmetricQuadraticEvaluationMatrix_det
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by
  rw [Matrix.det_fin_three]
  simp [symmetricQuadraticEvaluationMatrix]
  ring

lemma symmetricQuadratic_no_three_independent_roots
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  let A := symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂
  have hdet : A.det ≠ 0 := by
    rw [symmetricQuadraticEvaluationMatrix_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo h01) h02) h12
  have hmul : A.mulVec ![a, b, c] = 0 := by
    funext i
    fin_cases i
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₀
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₁
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₂
  have hzero : ![a, b, c] = (0 : Fin 3 → K) :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have ha : a = 0 := congrFun hzero 0
  have hb : b = 0 := congrFun hzero 1
  have hc : c = 0 := congrFun hzero 2
  exact hcoeff.elim (fun h => h ha)
    (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))

lemma symmetricQuadratic_no_three_roots_of_det_ne_zero
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  apply symmetricQuadratic_no_three_independent_roots
    htwo (a := a) (b := b) (c := c) (x₀ := x₀) (y₀ := y₀)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂)
    (h01 := h01) (h02 := h02) (h12 := h12)
    (hroot₀ := hroot₀) (hroot₁ := hroot₁) (hroot₂ := hroot₂)
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  apply hdet
  simp [symmetricDet, ha, hb, hc]

end

noncomputable section
variable (K : Type*) [Field K]

lemma symmetricGraphLine_odd_no_three_actual_centers
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by
  apply symmetricQuadratic_no_three_roots_of_det_ne_zero
    htwo hdet h01 h02 h12
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K h01)).mp hcenter₀
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h01)).mp hcenter₁
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h02)).mp hcenter₂

end

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticCanonical_line_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (X : SymplecticLine K)
    (hXH :
      Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV :
      Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  classical
  obtain ⟨a, b, c, hXgraph, hdet⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine
      K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 3) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hdir {i j : Fin 3} (hij : i ≠ j) :
      x i * y j - x j * y i ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy i) (hxy j)
    intro heq
    apply hij
    apply hcenters
    exact (hrepr i).trans (heq.trans (hrepr j).symm)
  have h01 : x 0 * y 1 - x 1 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 1)
  have h02 : x 0 * y 2 - x 2 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 2)
  have h12 : x 1 * y 2 - x 2 * y 1 ≠ 0 :=
    hdir (by decide : (1 : Fin 3) ≠ 2)
  apply symmetricGraphLine_odd_no_three_actual_centers K
    htwo hdet h01 h02 h12
  · obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 2
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 2]
      exact hpC

theorem symplecticLine_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (Y Z X : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hY : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (centers i).1)
    (hZ : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  have hleft :
      symplecticAutomorphismLine K e Y =
        symmetricGraphLine K 0 0 0 := by
    exact symplecticLineNormalizer_map_left K Y Z hYZ
  have hright :
      symplecticAutomorphismLine K e Z =
        symplecticVerticalLine K := by
    exact symplecticLineNormalizer_map_right K Y Z hYZ
  apply symplecticCanonical_line_no_three_common_centers K htwo
    (symplecticAutomorphismLine K e X)
    (centers := fun i =>
      symplecticAutomorphismLine K e (centers i))
  · rw [← hleft]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  · rw [← hright]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  · intro i j hij
    apply hcenters
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  · intro i
    obtain ⟨p, hpY, hpC⟩ := hY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hleft]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpZ, hpC⟩ := hZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hright]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpX, hpC⟩ := hX i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · exact (symplecticAutomorphism_incidence_iff K e p X).mpr hpX
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC

theorem symplecticQuadrangle_no_line_gamma_of_odd
    (htwo : (2 : K) ≠ 0)
    (copy : SimpleGraph.Copy gammaGraph
      (symplecticQuadrangle K))
    (C : SymplecticLine K)
    (hC : copy kSpecifiedCenter = .inr C) :
    False := by
  classical
  have hspecified :
      copy (.inl (.inr (0 : Fin 3))) = .inr C := by
    simpa [kSpecifiedCenter] using hC
  have hbase_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inl i)) = .inr L :=
    subdivisionLine_base_of_line_center K copy
      (base := i) (center := (0 : Fin 3)) hspecified
  choose bases hbase using hbase_exists
  have hcenter_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K copy
      (base := (0 : Fin 3)) (center := i) (hbase 0)
  choose centers hcenter using hcenter_exists
  apply symplecticLine_no_three_common_centers K htwo
    (bases 1) (bases 2) (bases 0)
    (centers := centers)
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (1 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 1) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_centers_injective K copy centers hcenter
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 1) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 2) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 0) (hcenter i)
    exact ⟨p, hpB, hpC⟩

theorem symplecticQuadrangle_no_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (quotientGraph kTemplate f).Free
      (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  let hom : kTemplate →g symplecticQuadrangle K :=
    copy.toHom.comp (kQuotientProjectionHom hf)
  have hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = i} := by
    intro i u hu v hv huv
    change
      copy (⟨f u, u, rfl⟩ : Set.range f) =
        copy (⟨f v, v, rfl⟩ : Set.range f)
      at huv
    apply hf.2 i hu hv
    exact congrArg Subtype.val (copy.injective huv)
  obtain ⟨i, L, hL⟩ :=
    symplecticQuadrangle_kTemplate_has_line_gamma
      K hom hcopies
  exact symplecticQuadrangle_no_line_gamma_of_odd K htwo
    (kGammaHomCopy hom hcopies i) L hL

theorem symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  (symplecticQuadrangle_encodeFiniteGraph_free_iff K
    (quotientGraph kTemplate f)).mpr
    (symplecticQuadrangle_no_kQuotient_of_odd K htwo hf)

end

noncomputable section
open Filter Finset SimpleGraph
open scoped Topology

theorem four_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    four_cycle_uniform_manuscript_lower hn

theorem six_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    six_cycle_uniform_manuscript_lower hn

theorem member_eventual_lower_of_prime_power_avoidance
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount t)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    quadrangle_uniform_lower_of_prime_power_avoidance
      forbidden.graph
      (proposedFamily_member_no_isolated hmember)
      t ht htgap hfree hn

theorem uniformMemberLower_of_characteristic_avoidance
    (hj : ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)))
    (hk : ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j))) :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  proposedFamily_induction
    (P := fun graph => ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n graph.graph : ℝ))
    (by simpa [finiteCycle] using four_cycle_eventual_manuscript_lower)
    (by simpa [finiteCycle] using six_cycle_eventual_manuscript_lower)
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (jQuotient_mem_proposedFamily hf)
      2 (by norm_num) (by norm_num) (hj f hf))
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (kQuotient_mem_proposedFamily hf)
      3 (by norm_num) (by norm_num) (hk f hf))

end

noncomputable section
open SimpleGraph

theorem proposedFamily_odd_characteristic_avoidance :
    ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j)) := by
  intro f hf j _
  exact symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (GaloisField 3 j)
    ((CharP.cast_eq_zero_iff (GaloisField 3 j) 3 2).not.mpr (by norm_num)) hf

end

end Erdos180

open Erdos180
open SimpleGraph

theorem solution :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  uniformMemberLower_of_characteristic_avoidance
    proposedFamily_even_characteristic_avoidance
    proposedFamily_odd_characteristic_avoidance
