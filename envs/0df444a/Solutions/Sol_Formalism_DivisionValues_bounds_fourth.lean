-- Prove2me | solution 1 for Formalism.DivisionValues.bounds_fourth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:47.649922+00:00
-- url     : https://prove2.me/submissions/32dee86b-ec66-4878-a4ef-e7c2244518bd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeDual

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
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsIV := by
  intro K _ _ _ n d H hH hdet E Pr hO A B hA DG hDG hB w ϖ J hv hJ
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp [vw, FractionalIdeal.count_zero] at hv
  have hvJ : vw w (((ϖ ^ J : 𝓞 K)) : K) = J := by
    have e : (((ϖ ^ J : 𝓞 K)) : K) = (ϖ : K) ^ J := by exact map_pow (algebraMap (𝓞 K) K) ϖ J
    unfold vw
    rw [e, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
    unfold vw at hv
    rw [hv, mul_one]
  obtain ⟨h1, h2, h3, h4⟩ := ValuationLatticeDual K n d H hH hdet E Pr hO A B hA DG hDG hB w (ϖ ^ J)
    (pow_ne_zero J hϖ) hJ
  rw [hvJ] at h4
  exact ⟨h1, h2, h3, h4⟩
end Formalism.DivisionValues
