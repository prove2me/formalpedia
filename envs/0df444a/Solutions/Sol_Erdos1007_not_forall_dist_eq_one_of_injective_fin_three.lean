-- Prove2me | solution 1 for Erdos1007.not_forall_dist_eq_one_of_injective_fin_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:21.298539+00:00
-- url     : https://prove2.me/submissions/f68d6b8d-8645-46e0-9090-b8dbcdee7b75

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
section
namespace Erdos1007
open Module Submodule AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace
private lemma dist_right_eq {a b : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hdist : ∀ i j, dist (a i) (b j) = 1) (i j j' : Fin 3) :
    dist (b j) (a i) = dist (b j') (a i) := by
  rw [dist_comm (b j) (a i), dist_comm (b j') (a i), hdist i j, hdist i j']
private lemma range_fin_two {α : Type*} (d1 d2 : α) :
    Set.range ![d1, d2] = ({d1, d2} : Set α) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
private lemma mem_orthogonal_span_pair {d1 d2 v : EuclideanSpace ℝ (Fin 3)}
    (h1 : ⟪d1, v⟫ = 0) (h2 : ⟪d2, v⟫ = 0) :
    v ∈ (span ℝ ({d1, d2} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
  intro w hw
  obtain ⟨s, t, rfl⟩ := mem_span_pair.mp hw
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
  ring
private lemma b_vsub_mem_orthogonal (a b : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hdist : ∀ i j, dist (a i) (b j) = 1) (j j' : Fin 3) :
    b j -ᵥ b j' ∈ (span ℝ (Set.range ![a 1 -ᵥ a 0, a 2 -ᵥ a 0]))ᗮ := by
  rw [range_fin_two]
  refine mem_orthogonal_span_pair ?_ ?_
  · exact inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_right_eq hdist 0 j' j)
      (dist_right_eq hdist 1 j' j)
  · exact inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_right_eq hdist 0 j' j)
      (dist_right_eq hdist 2 j' j)
private lemma inner_vsub_eq_half_norm_sq {a c p : EuclideanSpace ℝ (Fin 3)}
    (ha : dist a p = 1) (hc : dist c p = 1) :
    ⟪p -ᵥ a, c -ᵥ a⟫ = ‖c -ᵥ a‖ ^ 2 / 2 := by
  have hmem : p ∈ perpBisector a c :=
    (mem_perpBisector_iff_dist_eq').mpr (ha.trans hc.symm)
  rw [(mem_perpBisector_iff_inner_eq).mp hmem,
    dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 3)) a c, ← neg_vsub_eq_vsub_rev a c, norm_neg]
private lemma eq_zero_or_one_of_inner_norm_sq {x d : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hd : d ≠ 0) (hx : ⟪x, d⟫ = ‖d‖ ^ 2 / 2) (hy : ⟪x, r • d⟫ = ‖r • d‖ ^ 2 / 2) :
    r = 0 ∨ r = 1 := by
  have hmul : ⟪x, r • d⟫ = r * ⟪x, d⟫ := real_inner_smul_right x d r
  have hnorm : ‖r • d‖ ^ 2 = r ^ 2 * ‖d‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hx2 : ⟪x, d⟫ * 2 = ‖d‖ ^ 2 := (eq_div_iff two_ne_zero).mp hx
  have hy2 : ⟪x, r • d⟫ * 2 = ‖r • d‖ ^ 2 := (eq_div_iff two_ne_zero).mp hy
  have hrN : r * ‖d‖ ^ 2 = r ^ 2 * ‖d‖ ^ 2 := by
    calc
      r * ‖d‖ ^ 2 = r * (⟪x, d⟫ * 2) := by rw [← hx2]
      _ = (r * ⟪x, d⟫) * 2 := by ring
      _ = ⟪x, r • d⟫ * 2 := by rw [← hmul]
      _ = ‖r • d‖ ^ 2 := hy2
      _ = r ^ 2 * ‖d‖ ^ 2 := hnorm
  have hdiff : (r - r ^ 2) * ‖d‖ ^ 2 = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hrN
  have hd2 : ‖d‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hrsub : r - r ^ 2 = 0 := (mul_eq_zero.mp hdiff).resolve_right hd2
  have hfac : r * (1 - r) = 0 := by
    have hrlin : r - r ^ 2 = r * (1 - r) := by ring
    rw [← hrlin]
    exact hrsub
  exact (mul_eq_zero.mp hfac).imp_right fun h => (sub_eq_zero.mp h).symm
private lemma false_of_not_linearIndependent_centers
    (a b : Fin 3 → EuclideanSpace ℝ (Fin 3)) (ha : Function.Injective a)
    (hdist : ∀ i j, dist (a i) (b j) = 1)
    (hdep : ¬ LinearIndependent ℝ ![a 1 -ᵥ a 0, a 2 -ᵥ a 0]) : False := by
  have hd : a 1 -ᵥ a 0 ≠ 0 := by
    intro h
    exact ha.ne (by decide : (1 : Fin 3) ≠ 0) ((vsub_eq_zero_iff_eq).mp h)
  rw [LinearIndependent.pair_iff' hd] at hdep
  push Not at hdep
  obtain ⟨r, hr⟩ := hdep
  have hx := inner_vsub_eq_half_norm_sq (hdist 0 0) (hdist 1 0)
  have hy := inner_vsub_eq_half_norm_sq (hdist 0 0) (hdist 2 0)
  rw [← hr] at hy
  rcases eq_zero_or_one_of_inner_norm_sq hd hx hy with rfl | rfl
  · rw [zero_smul] at hr
    exact ha.ne (by decide : (2 : Fin 3) ≠ 0) ((vsub_eq_zero_iff_eq).mp hr.symm)
  · rw [one_smul] at hr
    exact ha.ne (by decide : (1 : Fin 3) ≠ 2) (vsub_left_cancel hr)
private lemma false_of_linearIndependent_centers
    (a b : Fin 3 → EuclideanSpace ℝ (Fin 3)) (hb : Function.Injective b)
    (hdist : ∀ i j, dist (a i) (b j) = 1)
    (hli : LinearIndependent ℝ ![a 1 -ᵥ a 0, a 2 -ᵥ a 0]) : False := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    span ℝ (Set.range ![a 1 -ᵥ a 0, a 2 -ᵥ a 0])
  have hK : finrank ℝ K = 2 := by
    change finrank ℝ (span ℝ (Set.range ![a 1 -ᵥ a 0, a 2 -ᵥ a 0])) = 2
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hKo : finrank ℝ Kᗮ = 1 := by
    have hsum := finrank_add_finrank_orthogonal K
    rw [hK, finrank_euclideanSpace_fin] at hsum
    exact Nat.add_left_cancel (show 2 + finrank ℝ Kᗮ = 2 + 1 from hsum)
  let v := b 1 -ᵥ b 0
  have hv : v ≠ 0 := by
    intro h
    exact hb.ne (by decide : (1 : Fin 3) ≠ 0) ((vsub_eq_zero_iff_eq).mp h)
  have hmem1 : v ∈ Kᗮ := b_vsub_mem_orthogonal a b hdist 1 0
  have hmem2 : b 2 -ᵥ b 0 ∈ Kᗮ := b_vsub_mem_orthogonal a b hdist 2 0
  have hspan : Kᗮ = ℝ ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hKo hmem1 hv
  obtain ⟨t, ht⟩ := mem_span_singleton.mp (hspan ▸ hmem2)
  have hdist1 : dist ((1 : ℝ) • v +ᵥ b 0) (a 0) = dist (b 0) (a 0) := by
    rw [one_smul, show v = b 1 -ᵥ b 0 from rfl, vsub_vadd]
    calc
      dist (b 1) (a 0) = dist (a 0) (b 1) := dist_comm _ _
      _ = dist (a 0) (b 0) := (hdist 0 1).trans (hdist 0 0).symm
      _ = dist (b 0) (a 0) := dist_comm _ _
  have h1param := (dist_smul_vadd_eq_dist (b 0) (a 0) hv (1 : ℝ)).mp hdist1
  have hbt : b 2 = t • v +ᵥ b 0 :=
    (eq_vadd_iff_vsub_eq (b 2) (t • v) (b 0)).mpr ht.symm
  have hdistt : dist (t • v +ᵥ b 0) (a 0) = dist (b 0) (a 0) := by
    rw [← hbt]
    calc
      dist (b 2) (a 0) = dist (a 0) (b 2) := dist_comm _ _
      _ = dist (a 0) (b 0) := (hdist 0 2).trans (hdist 0 0).symm
      _ = dist (b 0) (a 0) := dist_comm _ _
  have htparam := (dist_smul_vadd_eq_dist (b 0) (a 0) hv t).mp hdistt
  rcases h1param with h10 | h1f
  · exact absurd h10 one_ne_zero
  · rcases htparam with ht0 | htf
    · have hb20 : b 2 -ᵥ b 0 = 0 := by rw [← ht, ht0, zero_smul]
      exact hb.ne (by decide : (2 : Fin 3) ≠ 0) ((vsub_eq_zero_iff_eq).mp hb20)
    · have ht1 : t = 1 := htf.trans h1f.symm
      have hb21 : b 2 -ᵥ b 0 = b 1 -ᵥ b 0 := by
        rw [← ht, ht1, one_smul, show v = b 1 -ᵥ b 0 from rfl]
      exact hb.ne (by decide : (2 : Fin 3) ≠ 1) (vsub_left_cancel hb21)
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
open Module Submodule AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace
public section
namespace Erdos1007
theorem _root_.solution
    (a b : Fin 3 → EuclideanSpace ℝ (Fin 3)) (ha : Function.Injective a)
    (hb : Function.Injective b) (hdist : ∀ i j, dist (a i) (b j) = 1) : False := by
  -- Collinear centres give no common point; otherwise the points lie on one line.
  by_cases hli : LinearIndependent ℝ ![a 1 -ᵥ a 0, a 2 -ᵥ a 0]
  · exact false_of_linearIndependent_centers a b hb hdist hli
  · exact false_of_not_linearIndependent_centers a b ha hdist hli
end Erdos1007
