-- Prove2me | solution 1 for DirichletUnitTheorem.nrPlaces_eq_card_roots_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:28:59.3067+00:00
-- url     : https://prove2.me/submissions/f2cd1163-e460-4e9a-b49e-9a81afcf0646

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] (α : K)
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    InfinitePlace.nrRealPlaces K = ((minpoly ℚ α).rootSet ℝ).ncard ∧
      2 * InfinitePlace.nrComplexPlaces K =
        {z : ℂ | z ∈ (minpoly ℚ α).rootSet ℂ ∧ z.im ≠ 0}.ncard := by
  classical
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hp0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hint
  have hAdj : Algebra.adjoin ℚ {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hdeg : (minpoly ℚ α).natDegree = Module.finrank ℚ K := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  -- embeddings are determined by the image of `α`
  have inj : ∀ φ ψ : K →+* ℂ, φ α = ψ α → φ = ψ := by
    intro φ ψ h
    have := AlgHom.ext_of_adjoin_eq_top hAdj (φ₁ := φ.toRatAlgHom) (φ₂ := ψ.toRatAlgHom)
      (by intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact h)
    ext x
    exact congrArg (fun f : K →ₐ[ℚ] ℂ => f x) this
  have hroot : ∀ φ : K →+* ℂ, φ α ∈ (minpoly ℚ α).rootSet ℂ := by
    intro φ
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom α (minpoly ℚ α)
    rw [minpoly.aeval, map_zero] at this
    simpa using this
  let f : (K →+* ℂ) → (minpoly ℚ α).rootSet ℂ := fun φ => ⟨φ α, hroot φ⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun φ ψ h => inj φ ψ (congrArg Subtype.val h), ?_⟩
    rw [NumberField.Embeddings.card, Polynomial.card_rootSet_eq_natDegree
      (Algebra.IsSeparable.isSeparable ℚ α) (IsAlgClosed.splits _), hdeg]
  have hsurj : ∀ z ∈ (minpoly ℚ α).rootSet ℂ, ∃ φ : K →+* ℂ, φ α = z := by
    intro z hz
    obtain ⟨φ, hφ⟩ := hf.2 ⟨z, hz⟩
    exact ⟨φ, congrArg Subtype.val hφ⟩
  -- an embedding is real iff the image of `α` is real
  have hreal : ∀ φ : K →+* ℂ, ComplexEmbedding.IsReal φ ↔ (φ α).im = 0 := by
    intro φ
    rw [ComplexEmbedding.isReal_iff, ← Complex.conj_eq_iff_im]
    constructor
    · intro h
      rw [← ComplexEmbedding.conjugate_coe_eq, h]
    · intro h
      exact inj _ _ (by rw [ComplexEmbedding.conjugate_coe_eq, h])
  have hinjOn : ∀ s : Set (K →+* ℂ), Set.InjOn (fun φ : K →+* ℂ => φ α) s :=
    fun s φ _ ψ _ h => inj φ ψ h
  constructor
  · rw [← InfinitePlace.card_real_embeddings, ← Nat.card_eq_fintype_card,
      show Nat.card {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} = _ from
        Nat.card_coe_set_eq {φ : K →+* ℂ | ComplexEmbedding.IsReal φ}]
    rw [show ((minpoly ℚ α).rootSet ℝ).ncard =
        ((fun x : ℝ => (x : ℂ)) '' (minpoly ℚ α).rootSet ℝ).ncard from
      (Set.ncard_image_of_injective _ Complex.ofReal_injective).symm]
    rw [← (hinjOn {φ | ComplexEmbedding.IsReal φ}).ncard_image]
    · congr 1
      ext z
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨φ, hφ, rfl⟩
        refine ⟨(φ α).re, ?_, ?_⟩
        · rw [Polynomial.mem_rootSet]
          refine ⟨hp0, ?_⟩
          have h1 := ((Polynomial.mem_rootSet).mp (hroot φ)).2
          have h2 : ((φ α).re : ℂ) = φ α := Complex.ext rfl (by simp [(hreal φ).mp hφ])
          rw [← h2, show (((φ α).re : ℝ) : ℂ) = algebraMap ℝ ℂ (φ α).re from rfl,
            Polynomial.aeval_algebraMap_apply] at h1
          exact (FaithfulSMul.algebraMap_injective ℝ ℂ) (by rw [h1, map_zero])
        · exact Complex.ext rfl (by simp [(hreal φ).mp hφ])
      · rintro ⟨x, hx, rfl⟩
        have hz : (x : ℂ) ∈ (minpoly ℚ α).rootSet ℂ := by
          rw [Polynomial.mem_rootSet] at hx ⊢
          refine ⟨hp0, ?_⟩
          rw [show (x : ℂ) = algebraMap ℝ ℂ x from rfl, Polynomial.aeval_algebraMap_apply, hx.2,
            map_zero]
        obtain ⟨φ, hφ⟩ := hsurj _ hz
        exact ⟨φ, (hreal φ).mpr (by rw [hφ]; simp), hφ⟩
  · rw [← InfinitePlace.card_complex_embeddings, ← Nat.card_eq_fintype_card,
      show Nat.card {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ} = _ from
        Nat.card_coe_set_eq {φ : K →+* ℂ | ¬ComplexEmbedding.IsReal φ},
      ← (hinjOn {φ | ¬ComplexEmbedding.IsReal φ}).ncard_image]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨hroot φ, fun h => hφ ((hreal φ).mpr h)⟩
    · rintro ⟨hz, him⟩
      obtain ⟨φ, rfl⟩ := hsurj _ hz
      exact ⟨φ, fun h => him ((hreal φ).mp h), rfl⟩
