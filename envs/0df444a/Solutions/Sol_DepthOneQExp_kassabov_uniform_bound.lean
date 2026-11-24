-- Prove2me | solution 1 for DepthOneQExp.kassabov_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:57:59.793008+00:00
-- url     : https://prove2.me/submissions/d1692474-82f7-48e0-b1c9-cf800a2cad30

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_blockElem
import Definitions.Def_DepthOneQExp_sigma
import Theorems.Thm_DepthOneQExp_relT_gem
import Theorems.Thm_DepthOneQExp_root_subgroups_kazhdan
import Theorems.Thm_DepthOneQExp_gem_generation_small

open scoped InnerProductSpace
open DepthOneQExp

namespace DepthOneQExp.KUBAux

abbrev SLs (s : ℕ) := Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)

variable {s : ℕ} (ρ : ConstGapCircuits.UnitaryRep (SLs s))

noncomputable def U (g : SLs s) : EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)

theorem U_mul (g h : SLs s) (w : EuclideanSpace ℂ (Fin ρ.dim)) : U ρ (g * h) w = U ρ g (U ρ h w) := by
  simp only [U, map_mul]
  rw [Submonoid.coe_mul, map_mul]; rfl

theorem U_one (w : EuclideanSpace ℂ (Fin ρ.dim)) : U ρ 1 w = w := by simp [U]

theorem U_iso (g : SLs s) (w : EuclideanSpace ℂ (Fin ρ.dim)) : ‖U ρ g w‖ = ‖w‖ := by
  have h : ⟪U ρ g w, U ρ g w⟫_ℂ = ⟪w, w⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, U,
      ← map_star, ← ContinuousLinearMap.mul_apply, ← map_mul,
      (Matrix.mem_unitaryGroup_iff'.1 (ρ.hom g).2), map_one, ContinuousLinearMap.one_apply]
  have h2 : ‖U ρ g w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- displacement of a product is at most the sum of displacements -/
theorem disp_mul (g h : SLs s) (w : EuclideanSpace ℂ (Fin ρ.dim)) :
    ‖U ρ (g * h) w - w‖ ≤ ‖U ρ g w - w‖ + ‖U ρ h w - w‖ := by
  rw [U_mul]
  calc ‖U ρ g (U ρ h w) - w‖ = ‖U ρ g (U ρ h w - w) + (U ρ g w - w)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖U ρ g (U ρ h w - w)‖ + ‖U ρ g w - w‖ := norm_add_le _ _
    _ = ‖U ρ g w - w‖ + ‖U ρ h w - w‖ := by rw [U_iso]; ring

theorem disp_list (l : List (SLs s)) (w : EuclideanSpace ℂ (Fin ρ.dim)) (c : ℝ)
    (hc : ∀ g ∈ l, ‖U ρ g w - w‖ ≤ c) : ‖U ρ l.prod w - w‖ ≤ l.length * c := by
  induction l with
  | nil => simp [U_one]
  | cons g l ih =>
    rw [List.prod_cons]
    refine (disp_mul ρ g l.prod w).trans ?_
    have h1 := hc g (List.mem_cons_self ..)
    have h2 := ih (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg'))
    simp only [List.length_cons]; push_cast; linarith

/-- center of mass: if every element moves `v` by less than `√2`, there is a nonzero invariant
vector -/
theorem center_of_mass (v : EuclideanSpace ℂ (Fin ρ.dim)) (hv : ‖v‖ = 1)
    (h : ∀ g, ‖U ρ g v - v‖ ^ 2 < 2) :
    ∃ w : EuclideanSpace ℂ (Fin ρ.dim), w ≠ 0 ∧ ∀ g, U ρ g w = w := by
  refine ⟨∑ g : SLs s, U ρ g v, ?_, ?_⟩
  · intro h0
    have hre : RCLike.re ⟪∑ g : SLs s, U ρ g v, v⟫_ℂ = ∑ g : SLs s, (1 - ‖U ρ g v - v‖ ^ 2 / 2) := by
      rw [sum_inner, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [@norm_sub_sq ℂ, U_iso, hv]
      ring
    rw [h0, inner_zero_left, map_zero] at hre
    have : 0 < ∑ g : SLs s, (1 - ‖U ρ g v - v‖ ^ 2 / 2) :=
      Finset.sum_pos (fun g _ => by linarith [h g]) Finset.univ_nonempty
    linarith
  · intro h'
    rw [map_sum]
    simp_rw [← U_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft h') _ _ fun g => rfl

theorem E_zero (a b : Fin 3) (h : a ≠ b) :
    (show SLs s from ⟨blockElem s a b 0, det_blockElem s h 0⟩) = 1 := by
  apply Subtype.ext
  show blockElem s a b 0 = 1
  unfold blockElem
  have : (Matrix.of fun p q : Fin 3 × Fin s => if p.1 = a ∧ q.1 = b then
      (0 : Matrix (Fin s) (Fin s) (ZMod 2)) p.2 q.2 else 0) = 0 := by
    ext p q; simp
  rw [this, add_zero, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

end DepthOneQExp.KUBAux

open DepthOneQExp.KUBAux in
theorem solution (s : ℕ) (hs : 1 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (hρ : ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) → v = 0)
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (hv : ‖v‖ = 1) :
    (1 / 250 : ℝ) ≤ ⨆ i : Fin 14, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ := by
  set ε := ⨆ i : Fin 14, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ with hεdef
  have hbdd : BddAbove (Set.range fun i : Fin 14 => ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖) := (Set.finite_range _).bddAbove
  have hvi : ∀ i : Fin 14, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ ε := fun i => le_ciSup hbdd i
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hvi 0)
  by_contra hlt
  push Not at hlt
  have hK1 := relT_gem s hs ρ v ε hε0 hvi
  by_cases hs3 : 3 ≤ s
  · obtain ⟨r, h⟩ := root_subgroups_kazhdan s hs3 ρ hρ v hv
    rcases h with h | h | h
    · have := (hK1 r 0).2.2.1
      rw [E_zero (s := s) 0 2 (by decide), mul_one] at this
      linarith
    · have := (hK1 0 r).1
      rw [E_zero (s := s) 0 2 (by decide), one_mul] at this
      linarith
    · have := (hK1 r 0).2.2.2
      rw [E_zero (s := s) 2 1 (by decide), mul_one] at this
      linarith
  · have hs2 : s ≤ 2 := by omega
    have hall : ∀ g : SLs s, ‖U ρ g v - v‖ ≤ 19 * (18 * ε) := by
      intro g
      obtain ⟨h, hh, rfl⟩ := gem_generation_small s hs hs2 g
      have := disp_list ρ (List.ofFn h) v (18 * ε) (by
        intro g hg
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hg
        obtain ⟨r₁, r₂, hk | hk | hk | hk⟩ := hh k <;> rw [hk]
        · exact (hK1 r₁ r₂).1
        · exact (hK1 r₁ r₂).2.1
        · exact (hK1 r₁ r₂).2.2.1
        · exact (hK1 r₁ r₂).2.2.2)
      simpa using this
    obtain ⟨w, hw0, hw⟩ := center_of_mass ρ v hv (fun g => by
      have h1 := hall g
      have h2 : 19 * (18 * ε) < 1.4 := by linarith
      have h3 : ‖U ρ g v - v‖ < 1.4 := lt_of_le_of_lt h1 h2
      nlinarith [norm_nonneg (U ρ g v - v)])
    exact hw0 (hρ w hw)
