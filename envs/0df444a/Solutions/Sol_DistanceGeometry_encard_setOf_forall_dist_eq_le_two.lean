-- Prove2me | solution 1 for DistanceGeometry.encard_setOf_forall_dist_eq_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:17.035548+00:00
-- url     : https://prove2.me/submissions/1d75bce7-5198-45a6-8d2e-588de31d38cb

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import Definitions.Def_LeanPool_DistanceGeometry_Trilateration
public import Theorems.Thm_DistanceGeometry_mem_sphereIntersection
attribute [local simp] DistanceGeometry.mem_sphereIntersection
section
@[expose] public section
namespace DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
section General
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}
omit [FiniteDimensional ℝ V] in
/-- For two solutions `p₁`, `p₂`, the difference vector is orthogonal to every center
difference `c i -ᵥ c i₀`, hence lies in `(vectorSpan ℝ (range c))ᗮ`. -/
private theorem vsub_mem_orthogonal [Nonempty ι] {p₁ p₂ : P}
    (h₁ : p₁ ∈ sphereIntersection c r) (h₂ : p₂ ∈ sphereIntersection c r) :
    (p₂ -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := by
  -- It suffices to be orthogonal to each generator `c i -ᵥ c i₀` of the span.
  rw [vectorSpan_range_eq_span_range_vsub_right ℝ c (Classical.arbitrary ι)]
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact inner_vsub_vsub_of_dist_eq_of_dist_eq
      (by rw [h₁ _, h₂ _]) (by rw [h₁ i, h₂ i])
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
private theorem eq_or_eq_or_eq_of_finrank_orthogonal_eq_one [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) {p p₁ p₂ : P}
    (hp : p ∈ sphereIntersection c r) (h₁ : p₁ ∈ sphereIntersection c r)
    (h₂ : p₂ ∈ sphereIntersection c r) : p = p₁ ∨ p = p₂ ∨ p₁ = p₂ := by
  -- If the two reference solutions coincide, the third disjunct holds.
  by_cases hp12 : p₁ = p₂
  · exact Or.inr (Or.inr hp12)
  refine Or.imp_right Or.inl ?_
  -- `p₁ ≠ p₂`, so `p₂ -ᵥ p₁` is a nonzero vector in the 1-dimensional `Wᗮ`.
  have hw2 : (p₂ -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := vsub_mem_orthogonal h₁ h₂
  have hw2ne : (p₂ -ᵥ p₁ : V) ≠ 0 := vsub_ne_zero.mpr (fun h => hp12 h.symm)
  have hwp : (p -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := vsub_mem_orthogonal h₁ hp
  -- `Wᗮ` is 1-dimensional and contains the nonzero `p₂ -ᵥ p₁`, hence `Wᗮ = span{p₂ -ᵥ p₁}`.
  have hspan : (vectorSpan ℝ (Set.range c))ᗮ = ℝ ∙ (p₂ -ᵥ p₁) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]; exact hw2
    · rw [finrank_span_singleton hw2ne, hc]
  -- So `p -ᵥ p₁` is a scalar multiple of `p₂ -ᵥ p₁`.
  rw [hspan, Submodule.mem_span_singleton] at hwp
  obtain ⟨t, ht⟩ := hwp
  -- `p = t • (p₂ -ᵥ p₁) +ᵥ p₁`.
  have hpval : p = t • (p₂ -ᵥ p₁) +ᵥ p₁ := by rw [ht, vsub_vadd]
  -- Distance of `p` to `c i₀` is `r i₀ = dist p₁ (c i₀)`; feed into the quadratic.
  have hd : dist (t • (p₂ -ᵥ p₁) +ᵥ p₁) (c (Classical.arbitrary ι))
      = dist p₁ (c (Classical.arbitrary ι)) := by
    rw [← hpval, hp _, h₁ _]
  rw [dist_smul_vadd_eq_dist _ _ hw2ne] at hd
  -- The other root `t = 1` corresponds to `p₂` (which also satisfies the equation).
  have hd2 : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) (c (Classical.arbitrary ι))
      = dist p₁ (c (Classical.arbitrary ι)) := by
    rw [one_smul, vsub_vadd, h₂ _, h₁ _]
  rw [dist_smul_vadd_eq_dist _ _ hw2ne] at hd2
  -- `hd2 : 1 = 0 ∨ 1 = root`; the second disjunct pins down the nonzero root.
  have hroot : (1 : ℝ)
      = -2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ c (Classical.arbitrary ι)⟫ / ⟪p₂ -ᵥ p₁, p₂ -ᵥ p₁⟫ :=
    hd2.resolve_left one_ne_zero
  rcases hd with h | h
  · -- `t = 0` ⇒ `p = p₁`.
    left; rw [hpval, h, zero_smul, zero_vadd]
  · -- `t = root = 1` ⇒ `p = p₂`.
    right
    have ht1 : t = 1 := by rw [h, ← hroot]
    rw [hpval, ht1, one_smul, vsub_vadd]
private theorem sphereIntersection_subset_pair [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) (r : ι → ℝ) :
    ∃ p₁ p₂ : P, sphereIntersection c r ⊆ {p₁, p₂} := by
  by_cases hnonempty : (sphereIntersection c r).Nonempty
  · obtain ⟨p₁, hp₁⟩ := hnonempty
    by_cases hsecond : ∃ p₂ ∈ sphereIntersection c r, p₂ ≠ p₁
    · obtain ⟨p₂, hp₂, hp₂ne⟩ := hsecond
      refine ⟨p₁, p₂, ?_⟩
      intro p hp
      rcases eq_or_eq_or_eq_of_finrank_orthogonal_eq_one hc hp hp₁ hp₂ with
        hpEq | hpEq | hp₁Eq
      · exact Set.mem_insert_iff.mpr (Or.inl hpEq)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hpEq))
      · exact (hp₂ne hp₁Eq.symm).elim
    · push Not at hsecond
      refine ⟨p₁, p₁, ?_⟩
      intro p hp
      have hpEq : p = p₁ := hsecond p hp
      exact Set.mem_insert_iff.mpr (Or.inl hpEq)
  · let p₀ := c (Classical.arbitrary ι)
    refine ⟨p₀, p₀, ?_⟩
    intro p hp
    exact (hnonempty ⟨p, hp⟩).elim
end General
variable {c : Fin 3 → EuclideanSpace ℝ (Fin 3)}
end DistanceGeometry
end
end

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}
namespace DistanceGeometry
theorem _root_.solution [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) (r : ι → ℝ) :
    Set.encard {p : P | ∀ i, dist p (c i) = r i} ≤ 2 := by
  change (sphereIntersection c r).encard ≤ 2
  obtain ⟨p₁, p₂, hsubset⟩ := sphereIntersection_subset_pair hc r
  calc
    (sphereIntersection c r).encard ≤ ({p₁, p₂} : Set P).encard :=
      Set.encard_mono hsubset
    _ ≤ ({p₂} : Set P).encard + 1 := Set.encard_insert_le {p₂} p₁
    _ = 2 := by norm_num
end DistanceGeometry
