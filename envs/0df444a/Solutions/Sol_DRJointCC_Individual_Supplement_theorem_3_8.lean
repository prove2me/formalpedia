-- Prove2me | solution 1 for DRJointCC.Individual.Supplement.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:44:31.754411+00:00
-- url     : https://prove2.me/submissions/aa63c5b7-92b9-41db-aaba-3a853b5a8c36

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Algorithm

open MeasureTheory
open scoped ENNReal

open DRJointCC
open DRJointCC.Individual
open DRJointCC.Individual.Supplement

/-- Theorem 3.8, p. 25: if `x_init ∈ 𝒳` is feasible in (45) for some `α ∈ Ā`, then along every
run of Algorithm 3.1 the objective values `f^t = cᵀx^t` are monotonically decreasing
(nonincreasing); if `𝒳` is bounded, the iterates `x^t` are bounded and `f^t` converges to a
finite limit. -/
theorem solution {m n k : ℕ} (hm : 0 < m) (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (δ : ℝ) (hδ : 0 < δ)
    (X : Set (Fin n → ℝ)) (c : Fin n → ℝ) (xinit : Fin n → ℝ)
    (hinit : xinit ∈ X ∧ ∃ α₀ ∈ Abar m δ, DRJointCC.Joint.Jfun D μ Sig ε xinit α₀ ≤ 0)
    (x : ℕ → Fin n → ℝ) (α : ℕ → Fin m → ℝ)
    (hrun : IsAlg31Run D μ Sig ε δ X c xinit x α) :
    Antitone (fun t => c ⬝ᵥ x t) ∧
      (Bornology.IsBounded X →
        Bornology.IsBounded (Set.range x) ∧
          ∃ L : ℝ, Filter.Tendsto (fun t => c ⬝ᵥ x t) Filter.atTop (nhds L)) := by
            obtain ⟨h0, h2, h3⟩ := hrun
            obtain ⟨hxX, α₀, hα₀, hJ₀⟩ := hinit
            have hmem : ∀ t, x t ∈ X := by
              intro t
              cases t with
              | zero => rw [h0]; exact hxX
              | succ t => exact (h3 t).1
            have hfeas : ∀ t, DRJointCC.Joint.Jfun D μ Sig ε (x t) (α (t + 1)) ≤ 0 := by
              intro t
              cases t with
              | zero =>
                rw [h0]
                have := (h2 0).2 α₀ hα₀
                rw [h0] at this
                exact le_trans this hJ₀
              | succ t =>
                have := (h2 (t + 1)).2 (α (t + 1)) (h2 t).1
                exact le_trans this (h3 t).2.1
            have hanti : Antitone (fun t => c ⬝ᵥ x t) := by
              apply antitone_nat_of_succ_le
              intro t
              exact (h3 t).2.2 (x t) (hmem t) (hfeas t)
            refine ⟨hanti, fun hX => ?_⟩
            have hsub : Set.range x ⊆ X := by
              rintro _ ⟨t, rfl⟩; exact hmem t
            have hrb : Bornology.IsBounded (Set.range x) := hX.subset hsub
            refine ⟨hrb, ?_⟩
            have hcont : Continuous (fun v : Fin n → ℝ => c ⬝ᵥ v) := by
              unfold dotProduct
              fun_prop
            have hbdd : BddBelow ((fun v : Fin n → ℝ => c ⬝ᵥ v) '' closure (Set.range x)) :=
              (hrb.isCompact_closure).bddBelow_image hcont.continuousOn
            have hbdd2 : BddBelow (Set.range (fun t => c ⬝ᵥ x t)) := by
              apply hbdd.mono
              rintro _ ⟨t, rfl⟩
              exact ⟨x t, subset_closure ⟨t, rfl⟩, rfl⟩
            exact ⟨_, tendsto_atTop_ciInf hanti hbdd2⟩
