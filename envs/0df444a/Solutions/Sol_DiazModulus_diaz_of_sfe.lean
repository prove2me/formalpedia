-- Prove2me | solution 1 for DiazModulus.diaz_of_sfe
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-09T06:30:45.946542+00:00
-- url     : https://prove2.me/submissions/9d08897b-121a-4869-bd1b-6ddcd1b89e15

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace DZSfeRoot
open DiazModulus

theorem mem_tilde_of_alg {z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ LogAlgTilde := by
  have h1 : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)
  have h2 := Submodule.smul_mem LogAlgTilde (⟨z, mem_Qbar_iff.mpr h⟩ : ↥Qbar) h1
  have h3 : (⟨z, mem_Qbar_iff.mpr h⟩ : ↥Qbar) • (1 : ℂ) = z := by
    show (z : ℂ) * 1 = z
    ring
  rwa [h3] at h2

theorem mem_tilde_of_log {z : ℂ} (h : IsAlgebraic ℚ (Complex.exp z)) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

/-- `![1, z]` is `Q̄`-linearly independent exactly when `z` is transcendental. -/
theorem indep_one_of_transcendental {z : ℂ} (hz : Transcendental ℚ z) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), z] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_contra hcon
  push_neg at hcon
  by_cases ht : t = 0
  · subst ht
    have hs0 : (s : ℂ) = 0 := by
      have : (s : ℂ) * 1 + (0 : ↥Qbar) * z = 0 := hst
      simpa using this
    exact hcon (Subtype.ext hs0) rfl
  · exfalso
    refine hz ?_
    have htC : (t : ℂ) ≠ 0 := fun h => ht (Subtype.ext h)
    have hst' : (s : ℂ) * 1 + (t : ℂ) * z = 0 := hst
    have : z = -(s : ℂ) / (t : ℂ) := by
      field_simp
      linear_combination hst'
    rw [this]
    exact (mem_Qbar_iff.mp (div_mem (neg_mem s.2) t.2))

end DZSfeRoot

namespace DZSfeRoot
open DiazModulus

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- **The claim.** Strong four exponentials, with Hermite–Lindemann, settles the conjecture
outright — by a single instantiation `x = (1, u)`, `y = (1, conj u)`. -/
theorem diaz_of_sfe_hl (hHL : HermiteLindemann) (hS : StrongFourExponentials) :
    DiazModulusConjecture := by
  intro u hu hnorm hexp
  by_cases halg : IsAlgebraic ℚ u
  · exact hHL u hu halg hexp
  · have hut : Transcendental ℚ u := halg
    have hct : Transcendental ℚ (conj u) := by
      intro hc
      exact hut (by simpa using alg_conj hc)
    have hexpc : IsAlgebraic ℚ (Complex.exp (conj u)) := by
      rw [Complex.exp_conj]; exact alg_conj hexp
    have hprod : u * conj u = (((‖u‖ : ℝ) : ℂ)) ^ 2 := by
      have h1 : u * conj u = ((Complex.normSq u : ℝ) : ℂ) := Complex.mul_conj u
      have h2 : (Complex.normSq u : ℝ) = ‖u‖ ^ 2 := (Complex.normSq_eq_norm_sq u)
      rw [h1, h2]
      norm_cast
    refine hS 1 u 1 (conj u)
      (indep_one_of_transcendental hut) (indep_one_of_transcendental hct) ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using mem_tilde_of_alg (isAlgebraic_one)
    · simpa using mem_tilde_of_log hexpc
    · simpa using mem_tilde_of_log hexp
    · rw [hprod]
      exact mem_tilde_of_alg (hnorm.pow 2)

end DZSfeRoot


open DiazModulus in
theorem solution : StrongFourExponentials → DiazModulusConjecture :=
  fun hS => DZSfeRoot.diaz_of_sfe_hl DiazModulus.hermite_lindemann_holds hS
