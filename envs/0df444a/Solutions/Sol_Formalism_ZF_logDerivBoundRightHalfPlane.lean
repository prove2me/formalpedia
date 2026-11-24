-- Prove2me | solution 1 for Formalism.ZF.logDerivBoundRightHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:31.734866+00:00
-- url     : https://prove2.me/submissions/bb5d1270-d104-46cc-bc93-e86d74ed6d3f

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Theorems.Thm_Formalism_ZF_lamF_anti
import Theorems.Thm_Formalism_ZF_lamF_eq_norm
import Theorems.Thm_Formalism_ZF_norm_logDeriv_le_lamF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : LogDerivRight := by
  obtain ⟨B, hB⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)
  refine ⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _),
    fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩
  have hσ1 : 0 < s.re - 1 := sub_pos.mpr hs
  have hpos : 0 < 1 / (s.re - 1) := by positivity
  rcases lt_or_ge s.re (1 + ε / 2) with hlt | hge
  · have hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]
    have hd : dist (s.re : ℂ) 1 < ε := by
      rw [Complex.dist_eq, hreal]; linarith
    have hne : (s.re : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]; exact hs.ne'
    have hb := hball hd hne
    simp only [norm_one, mul_one] at hb
    have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s.re : ℂ)) (by simpa using hs)
    rw [lamF_eq_norm hs, hL, neg_div, norm_neg]
    have htri : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ ≤
        ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹‖ +
          ‖((s.re : ℂ) - 1)⁻¹‖ := by
      have := norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) +
        ((s.re : ℂ) - 1)⁻¹) (((s.re : ℂ) - 1)⁻¹)
      simpa using this
    rw [norm_inv, hreal] at htri
    have : B ≤ max (max B 0) (lamF (1 + ε / 2)) :=
      le_max_of_le_left (le_max_left _ _)
    rw [one_div]
    linarith
  · have h1 : lamF s.re ≤ lamF (1 + ε / 2) := lamF_anti (by linarith) hge
    have : lamF (1 + ε / 2) ≤ max (max B 0) (lamF (1 + ε / 2)) := le_max_right _ _
    linarith
end Formalism.ZF
