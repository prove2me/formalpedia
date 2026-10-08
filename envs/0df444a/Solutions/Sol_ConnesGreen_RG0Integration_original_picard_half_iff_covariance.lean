-- Prove2me | solution 1 for ConnesGreen.RG0Integration.original_picard_half_iff_covariance
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:05:55.922877+00:00
-- url     : https://prove2.me/submissions/9004fa25-3991-415c-9797-fb90483c743a

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_all_regularized
import Theorems.Thm_WeilDefect_MarkerStability_half_bound_iff_covariance_le
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability
open scoped InnerProductSpace lp Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
private theorem half_all_regularized_iff_covariance
    {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (P : L →L[ℂ] H) (N : K →L[ℂ] H) :
    (∀ ε : ℝ, 0 < ε → (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤
      marker (P ∘L P.adjoint + ε • 1) N) ↔
      N ∘L N.adjoint ≤ P ∘L P.adjoint := by
  constructor
  · intro h
    have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun ε : ℝ => (P ∘L P.adjoint) + ε • 1)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds ((P ∘L P.adjoint))) := by
      simpa using (tendsto_const_nhds.add (hi.smul_const (1 : H →L[ℂ] H)))
    apply isClosed_Ici.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hs : IsStrictlyPositive ((P ∘L P.adjoint) + ε • 1) :=
      IsStrictlyPositive.nonneg_add
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
          (ContinuousLinearMap.isPositive_self_comp_adjoint _))
        ((isStrictlyPositive_one (A := H →L[ℂ] H)).smul hε)
    exact (half_bound_iff_covariance_le _ hs _).mp (h ε hε)
  · intro h ε hε
    have hs : IsStrictlyPositive ((P ∘L P.adjoint) + ε • 1) :=
      IsStrictlyPositive.nonneg_add
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
          (ContinuousLinearMap.isPositive_self_comp_adjoint _))
        ((isStrictlyPositive_one (A := H →L[ℂ] H)).smul hε)
    apply (half_bound_iff_covariance_le _ hs _).mpr
    exact h.trans (le_add_of_nonneg_right
      (smul_nonneg hε.le (zero_le_one : (0 : H →L[ℂ] H) ≤ 1)))

theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint ≤
      canonicalPositiveCovariance t ht := by
  rw [canonicalPicardMarker_lower_iff_all_regularized]
  exact half_all_regularized_iff_covariance
    (canonicalPositiveSynthesis t ht) (canonicalSelectedSynthesis t ht S)
