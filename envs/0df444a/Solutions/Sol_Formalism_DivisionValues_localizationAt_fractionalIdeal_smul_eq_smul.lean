-- Prove2me | solution 1 for Formalism.DivisionValues.localizationAt_fractionalIdeal_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.486593+00:00
-- url     : https://prove2.me/submissions/354b3112-994a-407f-bf91-4810921a36d4

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
import Theorems.Thm_Formalism_DivisionValues_shift_mem_smulLat
import Theorems.Thm_Formalism_DivisionValues_localizationAt_le_of_le_localizationAt
import Theorems.Thm_Formalism_DivisionValues_shift_smul_mem_locP
import Theorems.Thm_Formalism_DivisionValues_shift_count_le_vw
import Theorems.Thm_Formalism_DivisionValues_shift_mem_ideal_loc

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    {a : K} (ha : a ≠ 0) (hv : vw w a = FractionalIdeal.count K w I) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
  apply le_antisymm
  · apply localizationAt_le_of_le_localizationAt
    unfold Formalism.HermitianLatticesTheory.idealSmul
    rw [Submodule.span_le]
    rintro z ⟨b, hb, x, hx, rfl⟩
    refine shift_smul_mem_locP w N ha ?_ hx
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      rw [hv]
      exact shift_count_le_vw I w hb0 hb
  · apply localizationAt_le_of_le_localizationAt
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (shift_mem_smulLat a N z).mp hz
    obtain ⟨t, ht, hta⟩ := shift_mem_ideal_loc I hI w ha hv
    refine ⟨t, ht, ?_⟩
    have e : t • (a • x) = ((t : K) * a) • x := by
      rw [mul_smul]
      rfl
    rw [e]
    exact Submodule.subset_span ⟨_, hta, x, hx, rfl⟩
end Formalism.DivisionValues
