-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_count_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:46.212004+00:00
-- url     : https://prove2.me/submissions/95c84ffc-0e1c-41c3-9657-cd9d2b846dab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DegreeInfimum_PlaceDegreeSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.PlaceDegreeSums
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.Pj.QAt.PlaceDegreeSums
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K w I : ℝ) * logN w =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  classical
  have h00 := FractionalIdeal.finite_factors I
  have hfs : {v : HeightOneSpectrum (𝓞 K) | ¬ FractionalIdeal.count K v I = 0}.Finite :=
    Filter.eventually_cofinite.mp h00
  have hN : ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) : ℚ) : ℝ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I := by
    intro v
    simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : FractionalIdeal.absNorm I = ∏ v ∈ hfs.toFinset,
      FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) := by
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv
      by_contra h0
      apply hv
      have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
      simp [h0']), map_prod]
  have hterm : ∀ v : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K v I : ℝ) * logN v =
      Real.log ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v I) : ℚ) : ℝ) := by
    intro v
    rw [hN, Real.log_zpow, logN]
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_, hprod]
  · rw [Rat.cast_prod, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => hterm v
    · intro v _
      rw [hN]
      exact (zpow_pos (hNpos v) _).ne'
  · intro v hv
    by_contra h0
    apply hv
    have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
    simp [h0']
end Formalism.L2.Pj.QAt.PlaceDegreeSums
