-- Prove2me | solution 1 for Formalism.DivisionValues.shift_mem_ideal_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.010437+00:00
-- url     : https://prove2.me/submissions/19107e77-4ca7-43f8-a9ff-8cdfe9a7125b

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
import Theorems.Thm_Formalism_DivisionValues_shift_int_of_nonneg
import Theorems.Thm_Formalism_DivisionValues_shift_count_le_vw
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom


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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) (hv : vw w a = FractionalIdeal.count K w I) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ (t : K) * a ∈ I := by
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ a * I⁻¹ with hJ
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  have hJ0 : J ≠ 0 := mul_ne_zero hsa (inv_ne_zero hI)
  have hcJ : FractionalIdeal.count K w J = 0 := by
    rw [hJ, FractionalIdeal.count_mul K w hsa (inv_ne_zero hI), FractionalIdeal.count_inv]
    unfold vw at hv
    omega
  have hfg : (J : Submodule (𝓞 K) K).FG := by
    have : IsNoetherian (𝓞 K) (J : Submodule (𝓞 K) K) := FractionalIdeal.isNoetherian J
    exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)
  have hle : (J : Submodule (𝓞 K) K) ≤
      Formalism.HermitianLatticesTheory.locS w.asIdeal.primeCompl (1 : Submodule (𝓞 K) K) := by
    intro b hb
    by_cases hb0 : b = 0
    · rw [hb0]; exact Submodule.zero_mem _
    have h1 := shift_count_le_vw J w hb0 hb
    rw [hcJ] at h1
    obtain ⟨t, y, ht, hty⟩ := shift_int_of_nonneg w b hb0 h1
    refine ⟨t, ht, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨y, hty.symm⟩
  obtain ⟨t, ht, htJ⟩ := Formalism.HermitianLatticesTheory.indexBasic_denom w.asIdeal.primeCompl _ _ hfg hle
  refine ⟨t, ht, ?_⟩
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have h5 := htJ z hz
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
    exact h5
  have h3 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((t : K) * a) ≤ I := by
    have h4 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((t : K) * a) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J * I := by
      rw [hJ, ← FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc, mul_assoc,
        inv_mul_cancel₀ hI, mul_one]
    rw [h4]
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J * I ≤ 1 * I :=
          mul_le_mul_left h2 I
      _ = I := one_mul I
  exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h3
end Formalism.DivisionValues
