-- Prove2me | solution 1 for ChanceStateCtrl.PDE.theorem_2_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:15:36.938047+00:00
-- url     : https://prove2.me/submissions/495e8535-8d35-4366-8171-61627bee78ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model
import Theorems.Thm_ChanceStateCtrl_PDE_theorem_2_15
import Theorems.Thm_ChanceStateCtrl_PDE_corollary_2_12

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise
open ChanceStateCtrl.PDE

theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hξlaw : P.map ξ = multivariateGaussian 0 Sigma)
    (F : L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (h41 : ∃ uh : L2 D, p < probFn P ξ (gPDE Ainv f₀ φ α) uh)
    (us : L2 D) (hus : p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us)
    (h42 : ∀ x : closure D, stateS Ainv f₀ φ us 0 x < α) :
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us →
      ∃ lam : ℝ, 0 ≤ lam ∧ (∃ y ∈ integralSet Ainv f₀ φ α Sigma us, gradient F us = -lam • y) ∧
        lam * ((P {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α}).toReal - p) = 0) ∧
    (EqCond Ainv f₀ φ α Sigma us →
      ∀ lam : ℝ, 0 ≤ lam → (∃ y ∈ integralSet Ainv f₀ φ α Sigma us, gradient F us = -lam • y) →
        lam * ((P {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α}).toReal - p) = 0 →
        IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us) := by
  -- the event of (44) is the event `g(u*, ξ) ≤ 0` defining `φ(u*)`
  have hne : Nonempty (closure D) := by
    obtain ⟨x, hx⟩ := hDne; exact ⟨⟨x, subset_closure hx⟩⟩
  have hdense : Dense {x : closure D | x.1 ∈ D} := by
    intro x
    rw [closure_subtype]
    have : ((↑) : closure D → EuclideanSpace ℝ (Fin d)) '' {x : closure D | x.1 ∈ D} = D := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
    rw [this]; exact x.2
  have hevent : {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α} =
      {w | gPDE Ainv f₀ φ α us (ξ w) ≤ 0} := by
    ext w
    simp only [Set.mem_setOf_eq, gPDE, sub_nonpos]
    set f := stateS Ainv f₀ φ us (ξ w)
    have hbdd : BddAbove (Set.range fun x : closure D => f x) :=
      (isCompact_range f.continuous).bddAbove
    rw [ciSup_le_iff hbdd]
    constructor
    · intro h x
      have hcl : IsClosed {x : closure D | f x ≤ α} := isClosed_le f.continuous continuous_const
      have hsub : {x : closure D | x.1 ∈ D} ⊆ {x : closure D | f x ≤ α} := fun x hx => h x hx
      have := closure_minimal hsub hcl
      rw [hdense.closure_eq] at this
      exact this (Set.mem_univ x)
    · intro h x _; exact h x
  have hprob : (P {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α}).toReal =
      probFn P ξ (gPDE Ainv f₀ φ α) us := by
    rw [hevent]; rfl
  have h215 := theorem_2_15 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma P ξ hξ hξlaw
    us h42
  have h212 := (corollary_2_12 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma P ξ hξ
    hξlaw F hFconv hFdiff p hp us hus h42 h41).1
  rw [hprob]
  constructor
  · intro hsol
    obtain ⟨lam, hlam, hgrad, -, hcs⟩ := h212.mp hsol
    obtain ⟨w, hw, hgw⟩ := hgrad
    refine ⟨lam, hlam, ⟨-w, ?_, ?_⟩, hcs⟩
    · have := h215.2.1 hw
      simpa [Set.mem_neg] using this
    · rw [← hgw]; simp
  · intro heq lam hlam ⟨y, hy, hgy⟩ hcs
    refine h212.mpr ⟨lam, hlam, ?_, hus, hcs⟩
    refine ⟨-y, ?_, ?_⟩
    · rw [h215.2.2 heq]; simpa [Set.mem_neg] using hy
    · rw [hgy]; simp
