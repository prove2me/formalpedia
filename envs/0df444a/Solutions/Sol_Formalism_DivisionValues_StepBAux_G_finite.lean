-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.G_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:22.741796+00:00
-- url     : https://prove2.me/submissions/3b8c4574-5013-46bc-88d0-edfcc3d0989b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_change
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_exists_coords
import Theorems.Thm_Formalism_DivisionValues_StepBAux_supp_add
import Theorems.Thm_Formalism_DivisionValues_StepBAux_supp_conj

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
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (hV : ValBasic) (hIC : IdxChange) (hLB : LcvBasis) (hPF : ProdFormula)
    [IsTotallyComplex K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (D : ℕ)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : ∀ v, IsUnit (XQ v).det)
    (abelian₂ : Submodule (𝓞 K) (Fin D → K)) (hLam : Submodule.IsLattice K abelian₂)
    (G : HeightOneSpectrum (𝓞 K) → K) (e : HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K)
    (he : ∀ w, IsLocBasis abelian₂ w (e w)) (hG : ∀ w, v0.embedding (G w) = (gram XQ v0 (e w)).det) :
    (Function.support fun w => lw w * (vw w (G w) : ℝ)).Finite := by
  classical
  by_cases hne : Nonempty (HeightOneSpectrum (𝓞 K))
  swap
  · rw [not_nonempty_iff] at hne
    exact Set.toFinite _
  obtain ⟨w1⟩ := hne
  have hb := (he w1).1
  choose γ hγ using fun w => exists_coords (e w1) hb (e w)
  have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
  have hGne : ∀ w, G w ≠ 0 := fun w h => gram_ne XQ hXQ (e w) (he w).1 v0 (by rw [← hG w, h, map_zero])
  have hdet : ∀ w, G w = star (γ w).det * (γ w).det * G w1 := by
    intro w
    apply v0.embedding.injective
    rw [hG w, hγ w, gram_change, ← hG w1, map_mul, map_mul, hv0', Complex.star_def]
  have hγne : ∀ w, (γ w).det ≠ 0 := by
    intro w h
    apply hGne w
    rw [hdet w, h]; simp
  have hval : ∀ w, vw w (G w) = idx w (Submodule.span (𝓞 K) (Set.range (e w1))) abelian₂ +
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range (e w1))) abelian₂ + vw w (G w1) := by
    intro w
    obtain ⟨hmul, hstar, -, -, -, -, -⟩ := hV K w
    have hloc := he w
    rw [hγ w] at hloc
    obtain ⟨i1, i2⟩ := hIC K D abelian₂ hLam (e w1) hb w (γ w) hloc
    rw [hdet w, hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hγne w)) (hγne w)) (hGne w1),
      hmul _ _ (star_ne_zero.mpr (hγne w)) (hγne w), hstar, i1, i2]
    ring
  have s1 := (hLB K D XQ hXQ abelian₂ hLam (e w1) hb).1
  have s2 := supp_conj hV _ s1
  have s3 := (hPF K (G w1) (hGne w1)).1
  refine (supp_add _ _ (supp_add _ _ s1 s2) s3).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw ⊢
  rw [hval w] at hw
  rw [(hV K w).2.2.1]
  push_cast at hw
  convert hw using 1
  ring
end Formalism.DivisionValues.StepBAux
