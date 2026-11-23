-- Prove2me | solution 1 for Formalism.DivisionValues.shift_eq_of_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:30.809863+00:00
-- url     : https://prove2.me/submissions/2edde17f-2dcd-4a4f-a3e6-11b19a9e0d75

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution {A B : Submodule (𝓞 K) (Fin d → K)}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) :
    A = B := by
  have key : ∀ {A B : Submodule (𝓞 K) (Fin d → K)},
      (∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) → A ≤ B := by
    intro A B h x hx
    by_contra hxB
    let I : Ideal (𝓞 K) := B.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin d → K) x)
    have hmem : ∀ t, t ∈ I ↔ t • x ∈ B := fun t => by
      simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    have hI : I ≠ ⊤ := by
      intro htop
      have h1 : (1 : 𝓞 K) ∈ I := htop ▸ Submodule.mem_top
      rw [hmem, one_smul] at h1
      exact hxB h1
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    have hMne : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)
    let w : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMne⟩
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A :=
      (imageLcv_mem_locP _ _ _).2 ⟨1, w.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hx⟩
    rw [h w] at hxA
    obtain ⟨s, hs, hsx⟩ := (imageLcv_mem_locP _ _ _).1 hxA
    exact hs (hIM ((hmem s).mpr hsx))
  exact le_antisymm (key h) (key fun w => (h w).symm)
end Formalism.DivisionValues
