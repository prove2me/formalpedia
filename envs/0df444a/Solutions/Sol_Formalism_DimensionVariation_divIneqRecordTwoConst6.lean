-- Prove2me | solution 1 for Formalism.DimensionVariation.divIneqRecordTwoConst6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:33:09.261316+00:00
-- url     : https://prove2.me/submissions/3e22d612-f841-48a6-8f86-3e44a081c8cc

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Theorems.Thm_Formalism_DimensionVariation_divIneqRecordFree6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution
    (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 Nc c m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (q1 : muC ≤ mu0 + Lpass)
    (q2 : mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (q6 : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (q7 : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ)
    (z1 : 1 ≤ x) (z2 : 0 < eps) (z3 : L = x ^ eps) (z4 : b = Real.exp L) (z5 : a = x * b)
    (z6 : 1 ≤ rd) (z7 : Real.log rd ≤ L) (z8 : Real.log x ≤ L) (z9 : La = Real.log (a * rd))
    (z10 : B0 = f * m * b * x ^ eps)
    (z13 : (Fintype.card J : ℝ) = m) (z14 : (Fintype.card Pl : ℝ) ≤ f) (z15 : 1 ≤ m) (z16 : 1 ≤ f)
    (z17 : 1 ≤ k) (z18 : 1 ≤ N) (z19 : 0 ≤ S) (z20 : 0 ≤ tt) (z21 : 0 ≤ η) (zb : 0 ≤ b')
    (z23 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b)
    (z24 : ∀ j, |pq j - k| ≤ m) (z25 : |logOm| ≤ La)
    (z26 : lam0 ≤ b) (z27 : N ^ 2 ≤ b) (z28 : m ^ 3 * N ^ 2 * L ≤ b) (z29 : m * η * N * L ≤ b)
    (z30 : k * N ≤ b) (z31 : k * S ≤ w'') (z32 : m * (tt + 1) * η ≤ w'') (z33 : N * w'' ≤ b)
    (z34 : b' * N ≤ a) (z35 : m * k * b' ≤ a)
    (hC : 0 ≤ C) (hCC : C ≤ C0) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : 0 ≤ L') (hCL : C * L' ≤ C0 * La)
    (y1 : Lpass ≤ 1 + C0 * lam0)
    (y5 : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La)
    (y6 : ∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0)))
    (z11 : 0 ≤ Nc) (y2 : Eb ≤ c * m * x ^ eps * (B0 + Nc)) :
    muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10 + c) * (m * (B0 + Nc) * x ^ eps) := by
  have key := divIneqRecordFree6 J Pl TT r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 m f k N nV
    S tt η w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z13 z14 z15 z16 z17 z18
    z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC hCC hnV hnVN hL' hCL y1 y5 y6
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hC0 : 0 ≤ C0 := le_trans hC hCC
  have h1 : 0 ≤ (50 * C0 + 10) * (m * Nc * x ^ eps) := by positivity
  nlinarith
end Formalism.DimensionVariation
