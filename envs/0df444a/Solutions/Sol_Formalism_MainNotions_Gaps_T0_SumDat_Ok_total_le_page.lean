-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.total_le_page
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:12.726213+00:00
-- url     : https://prove2.me/submissions/a5c7bf80-078b-4c39-82fb-732fb2370e7e

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}
namespace Formalism.MainNotions.Gaps.T0.SumDat
namespace Ok
theorem _root_.solution (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hp : X.Page PP C k b m δ₂ q DF) :
    X.total PP ≤ X.d * X.f * m * b * δ₂ := by
  obtain ⟨tableDegreeThreeBase, one_le_radius_alt, q0, C0, k0, b0, m0, δ₂0, Tγ, S1, ps0, ps1, cdef, g1, qlow, TPP, primeSetTwoBounds⟩ := hp
  have T0 : 0 < X.T := by linarith [h.T1]
  have hD3 : 1 ≤ X.D ^ 3 := one_le_pow₀ h.D1
  have f0 := h.f0
  have κ0 := h.κ0
  have γ0 := h.γ0
  have d0 := h.d0
  have hc0 := h.c0
  have mδ : 0 < m * δ₂ := mul_pos m0 δ₂0
  have ps1' : 4 * C * PP ^ 2 * X.D ^ 3 * k ≤ X.T * (m * δ₂) := by
    rw [div_le_iff₀ mδ] at ps1
    linarith
  have primePairSetFirst : 1 ≤ PP := by nlinarith
  have cubicPeriodConstant : 1 ≤ PP ^ 3 := one_le_pow₀ primePairSetFirst
  have hq : X.RR * PP ^ 3 * DF ^ 2 ≤ q := by
    have hR4 : X.RR ≤ X.RR ^ 4 := le_self_pow₀ one_le_radius_alt (by norm_num)
    calc X.RR * PP ^ 3 * DF ^ 2 = X.RR * (PP ^ 3 * DF ^ 2) := by ring
      _ ≤ X.RR ^ 4 * (PP ^ 3 * DF ^ 2) := mul_le_mul_of_nonneg_right hR4 (by positivity)
      _ = X.RR ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := qlow
  have hq3 : X.RR ^ 3 * PP ^ 3 * DF ^ 2 ≤ q := by
    have hR4 : X.RR ^ 3 ≤ X.RR ^ 4 := pow_le_pow_right₀ one_le_radius_alt (by norm_num)
    calc X.RR ^ 3 * PP ^ 3 * DF ^ 2 = X.RR ^ 3 * (PP ^ 3 * DF ^ 2) := by ring
      _ ≤ X.RR ^ 4 * (PP ^ 3 * DF ^ 2) := mul_le_mul_of_nonneg_right hR4 (by positivity)
      _ = X.RR ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := qlow
  have hc1 : PP ^ 2 * X.c ≤ 1 := by
    rw [cdef, show PP ^ 2 * (X.RR * PP * DF ^ 2 / q) = X.RR * PP ^ 3 * DF ^ 2 / q by ring,
      div_le_one q0]
    exact hq
  have hc2 : PP ^ 2 * (X.RR ^ 2 * X.c) ≤ 1 := by
    rw [cdef, show PP ^ 2 * (X.RR ^ 2 * (X.RR * PP * DF ^ 2 / q)) = X.RR ^ 3 * PP ^ 3 * DF ^ 2 / q by ring,
      div_le_one q0]
    exact hq3
  have hT1 : PP ^ 2 / X.T ≤ 1 := (div_le_one T0).mpr TPP
  have tA : PP ^ 2 * X.D ^ 3 * X.κ / X.T ≤ X.f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ T0]
    have e1 : PP ^ 2 * X.D ^ 3 * X.κ ≤ PP ^ 2 * X.D ^ 3 * (C * k * X.f * b) :=
      mul_le_mul_of_nonneg_left S1 (by positivity)
    have e2 : (4 * C * PP ^ 2 * X.D ^ 3 * k) * (X.f * b) ≤ (X.T * (m * δ₂)) * (X.f * b) :=
      mul_le_mul_of_nonneg_right ps1' (by positivity)
    linarith
  have tB : PP ^ 2 * (X.T * X.c) ≤ X.f * m * b * δ₂ / 4 := by
    have e : PP ^ 2 * (X.T * X.c) = X.T * (PP ^ 2 * X.c) := by ring
    have e2 : X.T * (PP ^ 2 * X.c) ≤ X.T := mul_le_of_le_one_right T0.le hc1
    have e3 : X.T ≤ PP ^ 3 * X.T := le_mul_of_one_le_left T0.le cubicPeriodConstant
    linarith
  have tC : PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) ≤ X.f * m * b * δ₂ / 4 := by
    have e1 : PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T) ≤ 2 := by
      have e : PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T) = PP ^ 2 * (X.RR ^ 2 * X.c) + PP ^ 2 / X.T := by ring
      linarith
    have e2 : X.κ / X.γ₀ ≤ X.κ / X.T := div_le_div_of_nonneg_left κ0 T0 Tγ
    have e3 : X.κ / X.T ≤ X.f * m * b * δ₂ / 8 := by
      rw [div_le_iff₀ T0]
      have hCk : 0 ≤ C * k := mul_nonneg C0 k0
      have a0 : 2 ≤ PP ^ 2 * X.D ^ 3 := by nlinarith
      have a1 : C * k * 2 ≤ C * k * (PP ^ 2 * X.D ^ 3) := mul_le_mul_of_nonneg_left a0 hCk
      have a2 : 8 * (C * k) * (X.f * b) ≤ X.T * (m * δ₂) * (X.f * b) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    calc PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀)
        = (PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T)) * (X.κ / X.γ₀) := by ring
      _ ≤ 2 * (X.κ / X.T) := mul_le_mul e1 e2 (by positivity) (by norm_num)
      _ ≤ X.f * m * b * δ₂ / 4 := by linarith
  have hsum : PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
      PP ^ 3 * X.T ≤ X.f * m * b * δ₂ := by
    have e : PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) =
        PP ^ 2 * X.D ^ 3 * X.κ / X.T + PP ^ 2 * (X.T * X.c) +
          PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) := by ring
    rw [e]
    linarith
  unfold SumDat.total
  calc X.d * PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
        X.d * PP ^ 3 * X.T
      = X.d * (PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
        PP ^ 3 * X.T) := by ring
    _ ≤ X.d * (X.f * m * b * δ₂) := mul_le_mul_of_nonneg_left hsum d0
    _ = X.d * X.f * m * b * δ₂ := by ring
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
