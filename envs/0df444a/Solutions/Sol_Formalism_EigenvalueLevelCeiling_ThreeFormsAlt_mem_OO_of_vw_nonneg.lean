-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_OO_of_vw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:38.472487+00:00
-- url     : https://prove2.me/submissions/b98d9763-8e85-49c8-8ab8-8452fbaf4378

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_algebraMap_ne_zero_of_notMem
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_OO
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_isDVR_OO
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mem
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0)
    (h : 0 ≤ vw w a) : a ∈ OO w := by
  have := isDVR_OO w
  rcases ValuationRing.isInteger_or_isInteger (OO w) a with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [← hc]
    exact c.2
  · obtain ⟨r, s, hs, hrs⟩ := (mem_OO w _).mp c.2
    have hc' : a⁻¹ = algebraMap (𝓞 K) K r * (algebraMap (𝓞 K) K s)⁻¹ := by
      rw [← hrs, ← hc]
      rfl
    have hs0 := algebraMap_ne_zero_of_notMem w.asIdeal hs
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hc'
      exact inv_ne_zero ha hc'
    by_cases hr : r ∈ w.asIdeal
    · exfalso
      have hr0' : r ≠ 0 := fun h0 => hr0 (by rw [h0, map_zero])
      have h1 := idxChange_cnt_mem (K := K) w hr0' hr
      have h2 := idxChange_cnt_unit (K := K) w hs
      have h3 : algebraMap (𝓞 K) K s = a * algebraMap (𝓞 K) K r := by
        have : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
        rw [hc'] at this
        field_simp at this
        exact this.symm
      rw [h3, idxChange_cnt_mul w ha hr0] at h2
      unfold vw at h
      omega
    · refine (mem_OO w _).mpr ⟨s, r, hr, ?_⟩
      rw [← inv_inv a, hc']
      field_simp
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
