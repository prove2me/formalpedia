-- Prove2me | solution 1 for Formalism.DivisionValues.DualLatticeDivisor.mem_range_of_vw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:11.342673+00:00
-- url     : https://prove2.me/submissions/12231faf-9010-4643-9716-275d027c9b08

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DualLatticeDivisor
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.DualLatticeDivisor
theorem _root_.solution (a : K) (ha : a ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have key : ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K v I) := by
    refine finprod_induction
      (fun X : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
        ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = X)
      ⟨1, by simp⟩ ?_ ?_
    · rintro x y ⟨J1, h1⟩ ⟨J2, h2⟩
      exact ⟨J1 * J2, by rw [FractionalIdeal.coeIdeal_mul, h1, h2]⟩
    · intro v
      have hv : 0 ≤ FractionalIdeal.count K v I := h v
      refine ⟨v.asIdeal ^ (FractionalIdeal.count K v I).toNat, ?_⟩
      rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, Int.toNat_of_nonneg hv]
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI] at key
  obtain ⟨J, hJ⟩ := key
  have hmem : a ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hJ, hIdef]
    exact FractionalIdeal.mem_spanSingleton_self _ a
  obtain ⟨y, -, hy⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨y, hy⟩
end Formalism.DivisionValues.DualLatticeDivisor
