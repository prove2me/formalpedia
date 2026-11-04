-- Prove2me | solution 1 for DRUQChance.Markov.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:05:22.513584+00:00
-- url     : https://prove2.me/submissions/ead5aec0-788b-4d7e-9be1-fb083f17b0a5

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic
import Theorems.Thm_DRUQChance_Markov_theorem_7_if
import Theorems.Thm_DRUQChance_Markov_sec5_feasible_iff
import Theorems.Thm_DRUQChance_Markov_conic_certificate_essStrict

open MeasureTheory Matrix DRConvexOpt.Reform DRUQChance.Markov

theorem solution {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (s : Fin nP → ℝ) (t ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | s ⬝ᵥ ω.1 ≤ t}) ↔
      ∃ (β : ℝ) (γ : Fin nK → ℝ) (φ ψ : Fin (amb.L 0) → ℝ) (τ : ℝ),
        System26 amb s t ε β γ φ ψ τ := by
  constructor
  · intro hcc
    set S : Matrix (Fin 1) (Fin nP) ℝ := Matrix.of fun _ => s with hSdef
    set tv : Fin 1 → ℝ := fun _ => t with htv
    have hset : {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ tv} =
        {ω | s ⬝ᵥ ω.1 ≤ t} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Pi.le_def]
      constructor
      · intro h; simpa [S, tv, mulVec, dotProduct] using h 0
      · intro h i; simpa [S, tv, mulVec, dotProduct] using h
    have hcc' : ∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | S *ᵥ ω.1 ≤ tv} := by
      rw [hset]; exact hcc
    obtain ⟨γ, lam, kap, φ, τ1, ψ1, hfeas, hobj⟩ :=
      (sec5_feasible_iff amb hM hK hE hS S tv ε hε0 hε1).mp hcc'
    obtain ⟨hlam, hkap, hφ, h2, h4, h5, hL⟩ := hfeas
    simp only [uqObjective, hM.1, hM.2, one_mul] at hobj
    -- the dual cone is closed under nonnegative scaling
    have hdual_smul : ∀ (a : ℝ), 0 ≤ a → ∀ θ ∈ dualCone (amb.K 0), a • θ ∈ dualCone (amb.K 0) := by
      intro a ha θ hθ x hx
      rw [dotProduct_smul, smul_eq_mul]; exact mul_nonneg ha (hθ x hx)
    by_cases h0 : (0 : Fin 1) ∈ violIdx amb S tv
    · obtain ⟨hτ, hψ, h3, h6, h7⟩ := hL 0 h0
      have hS0 : S 0 = s := rfl
      rw [hS0] at h6
      have htv0 : tv 0 = t := rfl
      rw [htv0] at h3
      generalize τ1 0 = r at *
      generalize ψ1 0 = p at *
      rcases hτ.lt_or_eq with hτpos | hτ0
      · set a := r⁻¹ with ha
        have ha0 : 0 < a := inv_pos.mpr hτpos
        have haτ : a * r = 1 := inv_mul_cancel₀ hτpos.ne'
        refine ⟨a * (lam - kap), a • γ, a • φ, a • p, a, ?_⟩
        refine ⟨hdual_smul a ha0.le φ hφ, hdual_smul a ha0.le p hψ, ha0.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [dotProduct_smul, smul_eq_mul]
          have := mul_le_mul_of_nonneg_left hobj ha0.le
          nlinarith
        · rw [dotProduct_smul, smul_eq_mul]
          have := mul_le_mul_of_nonneg_left h2 ha0.le
          nlinarith
        · rw [dotProduct_smul, smul_eq_mul]
          have := mul_le_mul_of_nonneg_left h3 ha0.le
          have e : a * (r * t) = t := by rw [← mul_assoc, haτ, one_mul]
          nlinarith
        · rw [mulVec_smul, mulVec_smul, h4]
        · rw [mulVec_smul, mulVec_smul, h5]
        · rw [mulVec_smul, mulVec_smul, ← h6, smul_add, smul_smul, haτ, one_smul]
        · rw [mulVec_smul, mulVec_smul, h7]
      · -- r = 0 is impossible under (S)
        exfalso
        subst hτ0
        rw [zero_smul, add_zero] at h6
        obtain ⟨ω, hω, hωb⟩ := interior_subset hS
        have hb : amb.b ⬝ᵥ γ = p ⬝ᵥ (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2) := by
          rw [← hωb, dotProduct_comm, dotProduct_add, dotProduct_add, dotProduct_mulVec,
            dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec, ← mulVec_transpose,
            ← mulVec_transpose, ← mulVec_transpose, ← mulVec_transpose, h6, h7]
        have hb2 := hψ _ hω
        rw [sub_dotProduct, dotProduct_comm _ p, dotProduct_comm _ p] at hb2
        rw [dotProduct_comm (amb.c 0)] at h3
        nlinarith
    · -- no point of C₁ violates sᵀz ≤ t
      have hsafe : ∀ ω ∈ confSet (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0), s ⬝ᵥ ω.1 ≤ t := by
        intro ω hω
        by_contra hlt
        apply h0
        simp only [violIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ω, hω, lt_of_not_ge hlt⟩
      obtain ⟨ψ, hψ, hC, hD, hc⟩ :=
        conic_certificate_essStrict (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0) hE s t hsafe
      refine ⟨0, 0, 0, ψ, 0, ?_⟩
      refine ⟨fun x _ => by simp, hψ, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hc
      · simp
      · simp
      · simpa using hC.symm
      · simpa using hD.symm
  · rintro ⟨β, γ, φ, ψ, τ, h26⟩
    exact theorem_7_if amb hM hK s t ε hε0 hε1 β γ φ ψ τ h26
