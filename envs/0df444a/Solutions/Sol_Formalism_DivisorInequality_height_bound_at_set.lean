-- Prove2me | solution 1 for Formalism.DivisorInequality.height_bound_at_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:28.314879+00:00
-- url     : https://prove2.me/submissions/24017d8f-b0ba-48aa-9d57-8c9086bcfb42

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_DivIneqTopAnchorU
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds
import Theorems.Thm_Formalism_DivisorInequality_UniformCovolumeTail_stepDiSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
set_option maxHeartbeats 800000
namespace Formalism.DivisorInequality
theorem _root_.solution : HeightS := by
  intro J Pl Emb _ _ _ _ TT _ nr hu hP mlam logT hK aT logH Ch nV L' ν x eps L b a rd La m f k N S η b'
    logOm g0 logK MainNotions logOmτ logth0 logh logh' v logg C2 Cth C4 c5 c6 CT C8 Ce ev bT nτ lam1 D0 D1
    logc logxi Cev hhu hL6 h32 hmean hOm hSK hth hh hh' hg0 h5 h6 hg p2 pth p4 p5 p6 p8 pe hPb hlogc
    hlogxi hnτ hlam hlam' hD0 hD1 hbT hT0 hT pT pb' hev pev hx heps hLdef hb ha hrd hLa hcard hm hf hk
    hkmN hS hη kC kA kB
  have hN : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Real.one_le_rpow hx heps.le
  have hL0 : 0 ≤ L := by linarith
  have hx0 : 0 < x := by linarith
  have hrd0 : 0 < rd := by linarith
  have hloga : Real.log a = Real.log x + L := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos L).ne', Real.log_exp]
  have ha0 : 0 < a := by
    rw [ha, hb]
    exact mul_pos hx0 (Real.exp_pos L)
  have hLa' : La = Real.log x + L + Real.log rd := by
    rw [hLa, Real.log_mul ha0.ne' hrd0.ne', hloga]
  have lx : 0 ≤ Real.log x := Real.log_nonneg hx
  have lrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hLLa : L ≤ La := by linarith
  have hLa1 : 1 ≤ La := by linarith
  have hLa0 : 0 ≤ La := by linarith
  have hl2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos two_pos
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h2a : Real.log (2 * a) = Real.log 2 + Real.log a := Real.log_mul two_ne_zero ha0.ne'
  have hℓ : Real.log (2 * a) ≤ 2 * La := by linarith
  have hℓ0 : 0 ≤ Real.log (2 * a) := by linarith
  have hmN : m ≤ N := by linarith
  have hTN : logT ≤ CT * N * La := by
    have q1 : m * L ≤ N * La := mul_le_mul hmN hLLa hL0 hN0
    have q2 := mul_le_mul_of_nonneg_left q1 pT
    linarith
  have hT0' : 0 ≤ CT * N * La := mul_nonneg (mul_nonneg pT hN0) hLa0
  have hmη0 : 0 ≤ m * η := mul_nonneg (by linarith) hη
  have hmη : η ≤ m * η := by
    have := mul_le_mul_of_nonneg_right hm hη
    linarith

  have hK' := UniformCovolumeTail.stepDiSharp J Pl Emb nr ν g0 logK MainNotions logOmτ logth0 logh logh' hK logOm v f m N L La
    logT logg C2 Cth C4 c5 c6 CT C8 Ce Ch h32 hmean hOm hSK hth hh hh' hcard hg0 hm hN hL0 hLLa hLa1
    h5 h6 hT hg p2 pth p4 p5 p6 pT p8 pe kA kB
  have hsK := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hK' j)

  have hTT : (Finset.univ.filter (· ∈ TT)) = TT := by
    ext τ
    simp
  have hite : ∀ g : Pl → ℝ, ∑ τ, (if τ ∈ TT then g τ else 0) = ∑ τ ∈ TT, g τ := by
    intro g
    rw [← Finset.sum_filter, hTT]
  have hτ : ∀ τ, -(nτ τ * logT) + (2 * logc τ + logxi τ) ≤
      ((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) + N ^ 2 * La +
        (if τ ∈ TT then 2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT else 0) := by
    intro τ
    have r1 := hlogxi τ
    have r2 : N * (N - 1) / 2 * Real.log (2 * a) ≤ N * (N - 1) / 2 * (2 * La) :=
      mul_le_mul_of_nonneg_left hℓ (div_nonneg (mul_nonneg hN0 (by linarith)) zero_le_two)
    have r3 : 0 ≤ N * La := mul_nonneg hN0 hLa0
    have r4 := hlogc τ
    have r5 := hD1 τ
    have r6 := hD0 τ
    have r7 := hnτ τ
    have hNl : 0 ≤ (N - 1) * Real.log (2 * a) := mul_nonneg (by linarith) hℓ0
    have hNl' : (N - 1) * Real.log (2 * a) ≤ N * (2 * La) := mul_le_mul (by linarith) hℓ hℓ0 hN0
    by_cases hτT : τ ∈ TT
    · rw [if_pos hτT] at r6
      rw [if_pos hτT]
      have r8 := hlam τ hτT
      have r9 := hbT τ hτT
      have s1 : D1 τ ≤ 4 * S + 4 * m * η + 6 * b' := by linarith
      have s2 : (N - 1) * Real.log (2 * a) * D1 τ ≤
          (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η + 6 * b') := mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η + 6 * b') ≤
          N * (2 * La) * (4 * S + 4 * m * η + 6 * b') := mul_le_mul_of_nonneg_right hNl' (by linarith)
      have u1 : (N - k) / 2 + D0 τ ≤ (N - 1) / 2 + S + m * η + 2 * b' := by linarith
      have u2 : ((N - k) / 2 + D0 τ) * logT ≤ ((N - 1) / 2 + S + m * η + 2 * b') * (CT * N * La) :=
        mul_le_mul u1 hTN hT0 (by linarith)
      rw [r7, r8]
      linarith
    · rw [if_neg hτT] at r6
      rw [if_neg hτT]
      have r8 := hlam' τ hτT
      have s1 : D1 τ ≤ 4 * S + 4 * m * η := by linarith
      have s2 : (N - 1) * Real.log (2 * a) * D1 τ ≤
          (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η) := mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η) ≤
          N * (2 * La) * (4 * S + 4 * m * η) := mul_le_mul_of_nonneg_right hNl' (by linarith)
      have u1 : -(lam1 τ - D0 τ) ≤ (N - 1) / 2 + m * η := by linarith
      have u2 : -(lam1 τ - D0 τ) * logT ≤ ((N - 1) / 2 + m * η) * logT := mul_le_mul_of_nonneg_right u1 hT0
      have u3 : ((N - 1) / 2 + m * η) * logT ≤ ((N - 1) / 2 + S + m * η) * (CT * N * La) :=
        mul_le_mul (by linarith) hTN hT0 (by linarith)
      rw [r7]
      linarith
  have hsumτ := Finset.sum_le_sum (fun τ (_ : τ ∈ (Finset.univ : Finset Pl)) => hτ τ)
  have hLτ : ∑ τ, (-(nτ τ * logT) + (2 * logc τ + logxi τ)) =
      -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hR : ∑ τ, (((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) +
        N ^ 2 * La + (if τ ∈ TT then 2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT else 0)) =
      (Fintype.card Pl : ℝ) * (((N - 1) / 2 + S + m * η) * (CT * N * La) +
        4 * N * La * (4 * S + 4 * m * η) + N ^ 2 * La) +
        ∑ τ ∈ TT, (2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hite]
  have hTTs : ∑ τ ∈ TT, (2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT) =
      (TT.card : ℝ) * (2 * b' * (CT * N * La) + 24 * N * La * b') - ∑ τ ∈ TT, aT τ * logT := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hW0 : 0 ≤ ((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) +
      N ^ 2 * La :=
    add_nonneg (add_nonneg (mul_nonneg (by linarith) hT0')
      (mul_nonneg (mul_nonneg (by linarith) hLa0) (by linarith))) (mul_nonneg (sq_nonneg N) hLa0)
  have hfW := mul_le_mul_of_nonneg_right hcard hW0

  have hJ : ∑ j, ((∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) + Ch * f * N ^ 2 * (La + m ^ 3 * L)) -
        (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L')) =
      ∑ j, (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) + Ch * f * N ^ 2 * (La + m ^ 3 * L)) -
        ∑ j, (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L') := Finset.sum_sub_distrib _ _

  have hX1 : 0 ≤ f * N ^ 2 * La := mul_nonneg (mul_nonneg hf0 (sq_nonneg N)) hLa0
  have hX2 : 0 ≤ f * (m * η + S) * N * La := mul_nonneg (mul_nonneg (mul_nonneg hf0 (by linarith)) hN0) hLa0
  have hX3 : 0 ≤ (TT.card : ℝ) * b' * N * La :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pb') hN0) hLa0
  have g1 : (CT / 2 + 1 + Cev) * (f * N ^ 2 * La) ≤ Ch * (f * N ^ 2 * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX1
  have g2 : (CT + 16) * (f * (m * η + S) * N * La) ≤ Ch * (f * (m * η + S) * N * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX2
  have g3 : (2 * CT + 24) * ((TT.card : ℝ) * b' * N * La) ≤ Ch * ((TT.card : ℝ) * b' * N * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX3
  have g4 : 0 ≤ CT * (f * N * La) := mul_nonneg pT (mul_nonneg (mul_nonneg hf0 hN0) hLa0)
  rw [hhu]
  linarith
end Formalism.DivisorInequality
