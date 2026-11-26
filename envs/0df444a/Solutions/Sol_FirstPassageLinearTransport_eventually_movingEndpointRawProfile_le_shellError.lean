-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_movingEndpointRawProfile_le_shellError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:43.468873+00:00
-- url     : https://prove2.me/submissions/a871be32-7a64-4079-9e87-51d219ce39f1

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_eventually_dyadic_rank_term_le_endpoint_entropy_term
import Theorems.Thm_FirstPassageLinearTransport_moving_entropy_term_le_buffer
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingExponent_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_quadratic_rpow_le_power
import Theorems.Thm_FirstPassageLinearTransport_exactSharpCriticalLowSeriesConstant_spec
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_quadraticWindowShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighDensityProfile_le_rpow
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H := (movingTimeSupportConstant P.run P.Cswitch + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      let b := firstPassageEndpointRate - D / (L : ℝ)
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant
            (firstPassageEndpointRate / 2) (C / 2) *
          (((L + 1 : ℕ) : ℝ) *
              Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L *
              Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
        movingEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by
  let pHi := min (P.Cswitch * Real.log 2)
    (maximalBarrierC0 * P.run.D ^ 2)
  let K := 1 + quadraticWindowShellConstant
  let T := movingTimeSupportConstant P.run P.Cswitch + 1
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let B := Real.sqrt (Amax / Real.log 2 + 1) *
    Real.exp (firstPassageEndpointRate + D)
  have hHighBase := eventually_sqrtSupport_mul_quadratic_rpow_le_power
    (p := pHi) (kappa := P.epsilon) (by
      simpa [pHi] using P.high_rate_margin)
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hDyadic := hTerminalT.eventually
    eventually_dyadic_rank_term_le_endpoint_entropy_term
  have hRank1 := (tendsto_atTop.1 hTerminalT) 1
  have hA0 := eventually_movingExponent_pos hbuffer
  filter_upwards [hHighBase, hDyadic, hRank1, hA0, hUpper]
    with M hHighBase hDyadic hRank1 hA0 hUpper
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    linarith [quadraticWindowShellConstant_pos]
  have hT0 : 0 ≤ T := by
    have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
    have hsqrtSq := Real.sq_sqrt hrHi0.le
    have hsqrt0 := Real.sqrt_nonneg (P.run.rHi : ℝ)
    have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
      nlinarith [P.run.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
    have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
      linarith [P.run.D_pos, P.run.pHi.eta_pos]
    have hfrac : 0 ≤
        (P.run.D + P.run.tau + 3) /
          (1 - Real.sqrt (P.run.rHi : ℝ)) :=
      div_nonneg hnum hden.le
    have hinner : 0 ≤
        (P.run.D + P.run.tau + 3) /
            (1 - Real.sqrt (P.run.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    dsimp [T, movingTimeSupportConstant]
    nlinarith [mul_nonneg hratio hinner]
  have hR0 : 0 ≤ R := by
    have hr : (0 : ℝ) < (P.run.rStar : ℝ) := by
      exact_mod_cast P.run.rStar_pos
    dsimp [R]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact (exactSharpCriticalLowSeriesConstant_spec
      (div_pos firstPassageEndpointRate_pos (by norm_num))
      (by positivity : 0 ≤ C / 2)).1.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdHi : dHi ≤ K * x ^ (-pHi) := by
    simpa [dHi, K, x, pHi] using
      shrinkingHighDensityProfile_le_rpow P.run P.Cswitch M
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant :=
      quadraticWindowShellConstant_pos.le
    positivity
  have hDirectPower : x ^ (-pHi) ≤ x ^ (-P.epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by
      have hmargin := P.high_rate_margin
      dsimp [pHi] at hmargin ⊢
      linarith)
  have hDirect : dHi ≤ K * x ^ (-P.epsilon) :=
    hdHi.trans (mul_le_mul_of_nonneg_left hDirectPower hK0)
  have hHighTerm :
      T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) ≤
        (T * R * K) * x ^ (-P.epsilon) := by
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * (K * x ^ (-pHi))) := by
        gcongr
      _ = T * R * K *
          (Real.sqrt (x * Real.log x) *
            (((M : ℝ) + 1) ^ 2 * x ^ (-pHi))) := by ring
      _ ≤ (T * R * K) * x ^ (-P.epsilon) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [x, pHi] using hHighBase)
          (mul_nonneg (mul_nonneg hT0 hR0) hK0)
  have hL1 : 1 ≤ L := by simpa [L] using hRank1
  have hLR : 0 < (L : ℝ) := by positivity
  have hEndpointToActual :
      Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) ≤
        Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    have hbLe : b ≤ firstPassageEndpointRate := by
      dsimp [b]
      have : 0 ≤ D / (L : ℝ) := div_nonneg hD.le hLR.le
      linarith
    have hshift0 : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by positivity
    gcongr
  have hDyadic' :
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L *
          Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
    simpa [L] using hDyadic
  have hDyadicActual :
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) :=
    hDyadic'.trans hEndpointToActual
  have hLowScalar := moving_entropy_term_le_buffer
    P.Amax_pos hD hA0.le hUpper hL1
  have hLowTerm :
      T * Real.sqrt (x * Real.log x) * R * Q *
          (((L + 1 : ℕ) : ℝ) *
              Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
        (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
    have hbracket :
        ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) ≤
          2 * (Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
      linarith
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R * Q *
          (2 * (Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ))))) := by
        gcongr
      _ = (2 * T * R * Q) *
          (Real.sqrt (x * Real.log x) * Real.sqrt L *
            Real.exp (-((firstPassageEndpointRate - D / (L : ℝ)) *
              ((L - 1 : ℕ) : ℝ)))) := by
        dsimp [b]
        ring
      _ ≤ (2 * T * R * Q) *
          (B * ((2 : ℝ) ^ (-(movingRankBuffer A M)))) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [x, L, B] using hLowScalar)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0) hR0) hQ0)
      _ = (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by ring
  dsimp only
  calc
    dHi + T * Real.sqrt (x * Real.log x) * R *
          ((M : ℝ) + 1) ^ 2 * dHi +
        T * Real.sqrt (x * Real.log x) * R * Q *
          (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
      K * x ^ (-P.epsilon) +
        (T * R * K) * x ^ (-P.epsilon) +
        (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) :=
      add_le_add (add_le_add hDirect
        (by simpa [mul_assoc] using hHighTerm)) hLowTerm
    _ ≤ (K + T * R * K + 2 * T * R * Q * B) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) + x ^ (-P.epsilon)) := by
      have hbuf0 : 0 ≤ (2 : ℝ) ^ (-(movingRankBuffer A M)) := by positivity
      have hxpow0 : 0 ≤ x ^ (-P.epsilon) := Real.rpow_nonneg hx0.le _
      have hTK0 : 0 ≤ T * R * K :=
        mul_nonneg (mul_nonneg hT0 hR0) hK0
      have hQB0 : 0 ≤ 2 * T * R * Q * B :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0)
          hR0) hQ0) hB0
      calc
        _ ≤ K * (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) +
            (T * R * K) *
              (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) +
            (2 * T * R * Q * B) *
              (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hbuf0) hK0)
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hbuf0) hTK0))
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hxpow0) hQB0)
        _ = _ := by ring
    _ = movingEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
      rfl
end FirstPassageLinearTransport
