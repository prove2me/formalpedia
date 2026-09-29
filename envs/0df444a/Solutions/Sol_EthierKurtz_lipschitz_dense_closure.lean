-- Prove2me | solution 1 for EthierKurtz.lipschitz_dense_closure
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T05:11:43.899627+00:00
-- url     : https://prove2.me/submissions/3fdca50f-4d20-4077-abd7-aaf891d72a14

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Topology BoundedContinuousFunction NNReal

theorem solution (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) :
    ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ h' : (closure Ω) →ᵇ ℝ, (∃ K : NNReal, LipschitzWith K ⇑h') ∧
        ‖h' - h‖ < delta := by
  intro h delta hdelta
  by_cases hempty : IsEmpty (closure Ω)
  · refine ⟨h, ⟨0, fun x y => (hempty.false x).elim⟩, ?_⟩
    simp only [sub_self, norm_zero]
    exact hdelta
  · haveI : Nonempty (closure Ω) := not_isEmpty_iff.mp hempty
    have hcomp : IsCompact (closure Ω) := hbounded.isCompact_closure
    haveI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hcomp
    let A : Subalgebra ℝ (ContinuousMap (closure Ω) ℝ) :=
      { carrier := {f | ∃ K_ : NNReal, LipschitzWith K_ ⇑f}
        mul_mem' := by
          intro f g hf hg
          obtain ⟨Kf, hff⟩ := hf
          obtain ⟨Kg, hgg⟩ := hg
          let Ff := BoundedContinuousFunction.mkOfCompact f
          let Fg := BoundedContinuousFunction.mkOfCompact g
          refine ⟨‖Ff‖₊ * Kg + Kf * ‖Fg‖₊, ?_⟩
          rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          have e1 : ((f * g) : ContinuousMap (closure Ω) ℝ) x
              = f x * g x := rfl
          have e2 : ((f * g) : ContinuousMap (closure Ω) ℝ) y
              = f y * g y := rfl
          rw [e1, e2]
          have hMf : ∀ z, |f z| ≤ ‖Ff‖ := fun z => by
            rw [← Real.norm_eq_abs]
            exact Ff.norm_coe_le_norm z
          have hMg : ∀ z, |g z| ≤ ‖Fg‖ := fun z => by
            rw [← Real.norm_eq_abs]
            exact Fg.norm_coe_le_norm z
          have hEf : ∀ a b, |f a - f b| ≤ ↑Kf * dist a b := by
            intro a b
            have hxy := hff.dist_le_mul a b
            rwa [Real.dist_eq (f a) (f b)] at hxy
          have hEg : ∀ a b, |g a - g b| ≤ ↑Kg * dist a b := by
            intro a b
            have hxy := hgg.dist_le_mul a b
            rwa [Real.dist_eq (g a) (g b)] at hxy
          have hring : f x * g x - f y * g y
              = f x * (g x - g y) + (f x - f y) * g y := by ring
          have hfin : |f x * g x - f y * g y|
              ≤ ‖Ff‖ * (↑Kg * dist x y) + (↑Kf * dist x y) * ‖Fg‖ := by
            calc |f x * g x - f y * g y|
                = |f x * (g x - g y) + (f x - f y) * g y| := by rw [hring]
              _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := by
                simp only [← Real.norm_eq_abs]
                exact norm_add_le _ _
              _ = |f x| * |g x - g y| + (|f x - f y| * |g y|) := by
                  rw [abs_mul, abs_mul]
              _ ≤ ‖Ff‖ * (↑Kg * dist x y) + ((↑Kf * dist x y) * ‖Fg‖) := by
                  apply add_le_add
                  · exact mul_le_mul (hMf x) (hEg x y) (abs_nonneg _)
                      (by positivity)
                  · exact mul_le_mul (hEf x y) (hMg y) (abs_nonneg _)
                      (by positivity)
          have hform : ‖Ff‖ * (↑Kg * dist x y) + (↑Kf * dist x y) * ‖Fg‖
              = ↑(‖Ff‖₊ * Kg + Kf * ‖Fg‖₊) * dist x y := by
            push_cast
            ring
          rw [Real.dist_eq (f x * g x) (f y * g y)]
          exact hform ▸ hfin
        add_mem' := by
          intro f g hf hg
          obtain ⟨Kf, hff⟩ := hf
          obtain ⟨Kg, hgg⟩ := hg
          refine ⟨Kf + Kg, ?_⟩
          rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          have e1 : ((f + g) : ContinuousMap (closure Ω) ℝ) x
              = f x + g x := rfl
          have e2 : ((f + g) : ContinuousMap (closure Ω) ℝ) y
              = f y + g y := rfl
          rw [e1, e2]
          have h1 := hff.dist_le_mul x y
          have h2 := hgg.dist_le_mul x y
          have hle : dist (f x + g x) (f y + g y)
              ≤ dist (f x) (f y) + dist (g x) (g y) := by
            simp only [Real.dist_eq, ← Real.norm_eq_abs]
            have hrr : (f x + g x) - (f y + g y)
                = (f x - f y) + (g x - g y) := by ring
            rw [hrr]
            exact norm_add_le _ _
          calc dist (f x + g x) (f y + g y)
              ≤ dist (f x) (f y) + dist (g x) (g y) := hle
            _ ≤ ↑Kf * dist x y + ↑Kg * dist x y := add_le_add h1 h2
            _ = ↑(Kf + Kg) * dist x y := by push_cast; ring
        algebraMap_mem' := by
          intro r
          refine ⟨0, ?_⟩
          have e : ⇑(algebraMap ℝ (ContinuousMap (closure Ω) ℝ) r)
              = fun _ => r := by
            funext x
            simp [Algebra.algebraMap_eq_smul_one]
          rw [e]
          rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          simp }
    have hsep : A.SeparatesPoints := by
      intro x y hxy
      have hsep1 := Set.separatesPoints_lipschitzWith_one (closure Ω)
      obtain ⟨f_, hf_mem, hf_ne⟩ := hsep1 hxy
      let d : ContinuousMap (closure Ω) ℝ := ⟨f_, hf_mem.continuous⟩
      have hmem : d ∈ A := ⟨1, hf_mem⟩
      exact ⟨⇑d, ⟨d, hmem, rfl⟩, hf_ne⟩
    obtain ⟨g, hg⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A
        hsep ⇑h
        h.continuous (delta / 2) (half_pos hdelta)
    have hmem : ∃ K_ : NNReal, LipschitzWith K_ ⇑(g : ContinuousMap (closure Ω) ℝ) :=
      g.property
    obtain ⟨K_, hKg⟩ := hmem
    refine ⟨BoundedContinuousFunction.mkOfCompact (g : ContinuousMap (closure Ω) ℝ),
      ⟨K_, hKg⟩, ?_⟩
    have hle : ‖BoundedContinuousFunction.mkOfCompact
        (g : ContinuousMap (closure Ω) ℝ) - h‖ ≤ delta / 2 := by
      rw [BoundedContinuousFunction.norm_le (half_pos hdelta).le]
      intro x
      have hx := hg x
      exact le_of_lt hx
    exact lt_of_le_of_lt hle (half_lt_self hdelta)
