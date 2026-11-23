-- Prove2me | solution 1 for Formalism.DivisionValues.shift_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:53.28129+00:00
-- url     : https://prove2.me/submissions/d653ee01-6bc4-4817-a4b7-f357e1b70e9f

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
import Theorems.Thm_Formalism_DivisionValues_shift_vw_alg
import Theorems.Thm_Formalism_DivisionValues_shift_coe_ne_zero
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mem
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_unit
import Theorems.Thm_Formalism_DivisionValues_idxChange_unif


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ≠ 0 ∧ vw w (ϖ : K) = 1 ∧
      ∀ (n : ℕ) (x : 𝓞 K), x ≠ 0 → vw w (x : K) = n →
        ∃ t s : 𝓞 K, t ∉ w.asIdeal ∧ s ∉ w.asIdeal ∧ t * x = ϖ ^ n * s := by
  obtain ⟨ϖ, _, hϖ0, hcnt, t0, ht0, hdiv⟩ := idxChange_unif (K := K) w
  refine ⟨ϖ, hϖ0, hcnt, ?_⟩
  intro n
  induction n with
  | zero =>
    intro x hx hv
    refine ⟨1, x, ?_, ?_, by simp⟩
    · exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · intro h
      have := idxChange_cnt_mem (K := K) w hx h
      rw [← shift_vw_alg, hv] at this
      simp at this
  | succ n ih =>
    intro x hx hv
    have hxw : x ∈ w.asIdeal := by
      by_contra h
      have := idxChange_cnt_unit (K := K) w h
      rw [← shift_vw_alg, hv] at this
      push_cast at this
      omega
    obtain ⟨u, hu⟩ := hdiv x hxw
    have ht00 : t0 ≠ 0 := fun h => ht0 (h ▸ w.asIdeal.zero_mem)
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, mul_zero] at hu
      exact (mul_ne_zero ht00 hx) hu
    have hvu : vw w (u : K) = n := by
      have h1 : ((t0 : 𝓞 K) : K) * (x : K) = (ϖ : K) * (u : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hu
      have h2 := congrArg (vw w) h1
      rw [ValuationRepresentative.vw_mul w _ _ (shift_coe_ne_zero ht00) (shift_coe_ne_zero hx),
        ValuationRepresentative.vw_mul w _ _ (shift_coe_ne_zero hϖ0) (shift_coe_ne_zero hu0), hv] at h2
      have h3 : vw w (t0 : K) = 0 := idxChange_cnt_unit (K := K) w ht0
      have h4 : vw w (ϖ : K) = 1 := hcnt
      rw [h3, h4] at h2
      push_cast at h2
      omega
    obtain ⟨t, s, ht, hs, hts⟩ := ih u hu0 hvu
    refine ⟨t * t0, s, w.isPrime.mul_notMem ht ht0, hs, ?_⟩
    calc t * t0 * x = t * (t0 * x) := by ring
      _ = t * (ϖ * u) := by rw [hu]
      _ = ϖ * (t * u) := by ring
      _ = ϖ * (ϖ ^ n * s) := by rw [hts]
      _ = ϖ ^ (n + 1) * s := by ring
end Formalism.DivisionValues
