-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerReal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:27.156349+00:00
-- url     : https://prove2.me/submissions/d2143e0b-26c4-4fc8-be6b-e77721d69384

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_ne_zero_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_phi_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open UnitConjugation
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (hG : LayerGalois) (hC : LayerConj) : LayerReal := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hGal, hfin, _hmul, hbij⟩ := hG n q d hn hqd L ζ a b h
  have h1 : ∀ (φ : L →+* ℂ) (σ : Gal(L/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n :=
    fun φ σ => hC n q d hn hqd L ζ a b h φ σ
  have hq : 0 < q := hqd.1.pos
  obtain ⟨σc, hσc⟩ := hbij.2 (JJ n)
  have hTC : IsTotallyComplex L := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw a
    rw [ComplexEmbedding.conjugate_coe_eq, phi_conj hq h.2.1] at h2
    have h3 : (2 : ℂ) * w.embedding a = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (ne_zero_of_sq hq h.2.1) h4
  have hCM : IsCMField L := by
    refine IsCMField.of_forall_isConj L (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact ((h1 φ σc).2 hσc x).symm
  have h5 : ∀ x : L, x ∈ maximalRealSubfield L ↔
      ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx σ hσ
      let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
      apply φ.injective
      rw [(h1 φ σ).2 hσ x]
      exact hx φ
    · intro hx φ
      have := (h1 φ σc).2 hσc x
      rw [hx σc hσc] at this
      exact this.symm
  have h4 : Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield L) L
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L, hfin,
      pow_succ] at h
    omega
  exact ⟨hCM, h5, h4⟩
end Formalism.TwoAdicCyclotomicDecomposition
