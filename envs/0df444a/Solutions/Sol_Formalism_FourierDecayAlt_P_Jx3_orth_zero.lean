-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.orth_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:23.898113+00:00
-- url     : https://prove2.me/submissions/5be1529b-5ae1-4a30-b72c-3766282bf5eb

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
open InfinitePlace
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : CV E)
    (h : ∀ t : E, inner ℝ z (cemb E t) = 0) : z = 0 := by
  classical
  let v : InfinitePlace E × Bool → (E →* ℂ) := fun p =>
    if p.2 then (p.1.embedding : E →* ℂ) else ((ComplexEmbedding.conjugate p.1.embedding : E →+* ℂ) : E →* ℂ)
  have hne : ∀ w : InfinitePlace E, w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro w
    have hw : ¬ IsReal w := not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
  have hmk : ∀ p, ∃ φ : E →+* ℂ, (φ : E →* ℂ) = v p ∧ InfinitePlace.mk φ = p.1 ∧
      (φ = if p.2 then p.1.embedding else ComplexEmbedding.conjugate p.1.embedding) := by
    rintro ⟨w, b⟩
    cases b
    · exact ⟨ComplexEmbedding.conjugate w.embedding, by simp [v], by simp, by simp⟩
    · exact ⟨w.embedding, by simp [v], by simp, by simp⟩
  have hinj : Function.Injective v := by
    intro p q hpq
    obtain ⟨φ, h1, h2, h3⟩ := hmk p
    obtain ⟨φ', h1', h2', h3'⟩ := hmk q
    have hφ : φ = φ' := by
      apply RingHom.coe_monoidHom_injective
      show (φ : E →* ℂ) = (φ' : E →* ℂ)
      rw [h1, h1', hpq]
    have hw : p.1 = q.1 := by rw [← h2, ← h2', hφ]
    obtain ⟨w, b⟩ := p
    obtain ⟨w', b'⟩ := q
    simp only at hw
    subst hw
    rw [h3, h3'] at hφ
    cases b <;> cases b' <;> simp_all
    · exact absurd hφ.symm (hne w)
  have hli := (linearIndependent_monoidHom E ℂ).comp v hinj
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun p => if p.2 then conj (z p.1) else z p.1) (by
    ext t
    have ht := h t
    rw [PiLp.inner_apply] at ht
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_apply, Pi.smul_apply,
      Function.comp, v, smul_eq_mul, Pi.zero_apply]
    simp only [if_true, Bool.false_eq_true, if_false]
    have h2 : ∀ w : InfinitePlace E, conj (z w) * w.embedding t + z w * conj (w.embedding t) =
        ((2 * inner ℝ (z w) (cemb E t w) : ℝ) : ℂ) := by
      intro w
      have : cemb E t w = w.embedding t := rfl
      rw [this, Complex.inner]
      have h3 : z w * conj (w.embedding t) = conj (conj (z w) * w.embedding t) := by simp
      rw [h3, Complex.add_conj]
      congr 3
      ring
    have h4 : ∀ w : InfinitePlace E,
        conj (z w) * (w.embedding : E →* ℂ) t + z w * ((ComplexEmbedding.conjugate w.embedding : E →+* ℂ) : E →* ℂ) t
          = ((2 * inner ℝ (z w) (cemb E t w) : ℝ) : ℂ) := fun w => by
      rw [← h2 w]; rfl
    rw [Finset.sum_congr rfl (fun w _ => h4 w), ← Complex.ofReal_sum, ← Finset.mul_sum, ht]
    simp)
  ext w
  simpa using this (w, false)
end Formalism.FourierDecayAlt.P.Jx3
