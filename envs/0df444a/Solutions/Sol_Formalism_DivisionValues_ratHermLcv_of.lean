-- Prove2me | solution 1 for Formalism.DivisionValues.ratHermLcv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:27:44.684808+00:00
-- url     : https://prove2.me/submissions/0a18e075-d4ac-4794-92b7-37d3fd65deb9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_emb_det
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_det_ne_zero
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_expand_std
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_det_of_ne_zero
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_gramR_eq_std
import Theorems.Thm_Formalism_DivisionValues_jwGram_of
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_finite_sum_conjugation
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution (hLB : LcvBasis) (hIC : IdxChange) (hEx : LocBasisEx) : RatHermLcv := by
  intro K _ _ _ _ K0 hcm d H X hR T hT
  classical
  have hJ := jwGram_of hIC
  set e : Fin d → Fin d → K := fun i => Pi.single i 1 with he_def
  have he : LinearIndependent K e := by
    have : e = ⇑(Pi.basisFun K (Fin d)) := funext fun i => (Pi.basisFun_apply K (Fin d) i).symm
    rw [this]
    exact (Pi.basisFun K (Fin d)).linearIndependent
  have hdetH := det_ne_zero hR
  obtain ⟨hfinA, hlcv⟩ := hLB K d X (fun v => (hR.2 v).1) T hT e he
  have hgram : ∀ v, gram X v e = H.map v.embedding := by
    intro v
    have hv : ∀ a : Fin d, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v (Pi.single a (1 : K)) =
        (Pi.single a 1 : Fin d → ℂ) := by
      intro a
      funext i
      unfold Formalism.HermitianLatticesTheory.vecAt
      rw [Pi.basisFun_repr]
      by_cases hia : i = a
      · subst hia; simp
      · simp [hia]
    rw [← (hR.2 v).2]
    refine Matrix.ext fun a c => ?_
    change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v (Pi.single a 1) (Pi.single c 1) = _
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv, hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply]
  have hlog : ∀ v, Real.log (gram X v e).det.re = Real.log ‖v.embedding H.det‖ := by
    intro v
    have h1 : v.embedding H.det = ((Complex.normSq ((X v)⁻¹.det) : ℝ) : ℂ) := by
      rw [emb_det hR v, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    have h2 : (gram X v e).det = v.embedding H.det := by
      rw [hgram, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h2, h1, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  obtain ⟨hfinC, hpf⟩ := prod_formula' K H.det hdetH
  choose f hf using fun w => hEx K d T hT w
  set S := Submodule.span (𝓞 K) (Set.range e) with hS
  have hpt : ∀ w, (jw H w T : ℝ) =
      -((idx w S T : ℝ) + (idx (conjPl w) S T : ℝ) + (vw w H.det : ℝ)) := by
    intro w
    have hexp := expand_std (f w)
    have hloc : IsLocBasis T w (fun i => ∑ k, (Matrix.of (f w))ᵀ k i • e k) := by
      rw [he_def, hexp]; exact hf w
    obtain ⟨i1, i2⟩ := hIC K d T hT e he w _ hloc
    have hj := hJ K K0 hcm d H X hR T hT w (f w) (hf w)
    have hδ := det_of_ne_zero (hf w).1
    rw [gramR_eq_std, ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (star_ne_zero.mpr hδ) hδ) hdetH,
      ValuationRepresentative.vw_mul w _ _ (star_ne_zero.mpr hδ) hδ, ((valuation_basic_properties K w).2.1)] at hj
    rw [hj, i1, i2]
    push_cast
    ring
  have hlw : ∀ w, lw (conjPl w) = lw w := fun w => (valuation_basic_properties K w).2.2.1
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (idx w S T : ℝ) with ha
  set c : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (vw w H.det : ℝ) with hc
  have hinj : Function.Injective (conjPl (K := K)) := fun x y hxy => by
    have := congrArg conjPl hxy
    rwa [ValuationRepresentative.conjPl_conjPl, ValuationRepresentative.conjPl_conjPl] at this
  have hfinA' : (Function.support fun w => a (conjPl w)).Finite := by
    rw [show (fun w => a (conjPl w)) = a ∘ conjPl from rfl, Function.support_comp_eq_preimage]
    exact hfinA.preimage hinj.injOn
  have pt2 : (fun w => lw w * (jw H w T : ℝ)) = fun w => -(a w + a (conjPl w) + c w) := by
    funext w
    simp only [ha, hc, hpt w, hlw w]
    ring
  have hsum1 : ∑ᶠ w, (a w + a (conjPl w)) = ∑ᶠ w, a w + ∑ᶠ w, a (conjPl w) :=
    finsum_add_distrib hfinA hfinA'
  have hfin12 : (Function.support fun w => a w + a (conjPl w)).Finite :=
    (hfinA.union hfinA').subset (Function.support_add _ _)
  have hsum2 : ∑ᶠ w, (a w + a (conjPl w) + c w) =
      ∑ᶠ w, (a w + a (conjPl w)) + ∑ᶠ w, c w :=
    finsum_add_distrib hfin12 hfinC
  have hconj : ∑ᶠ w, a (conjPl w) = ∑ᶠ w, a w := finite_sum_conjugation K a
  refine ⟨?_, ?_⟩
  · rw [pt2]
    change (Function.support (-(fun w => a w + a (conjPl w) + c w))).Finite
    rw [Function.support_neg]
    exact (hfin12.union hfinC).subset (Function.support_add _ _)
  · rw [pt2, finsum_neg_distrib, hsum2, hsum1, hconj, hlcv]
    simp only [hlog]
    rw [hpf]
    ring
end Formalism.DivisionValues
