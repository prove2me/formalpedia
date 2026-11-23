-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.core_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:07.074476+00:00
-- url     : https://prove2.me/submissions/37eae89b-7a50-49e3-9310-720fe0ca7bf1

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp y yD yL K h g
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hy : 1 ≤ y) (hyD : 1 ≤ yD) (hyL : 1 ≤ yL)
    (hnT : 1 ≤ nT) (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (hM : 0 ≤ M) (hk : 0 < k) (hMk : M ≤ k)
    (hMb : M * b ≤ a) (hL0 : 0 ≤ L) (hL : L ≤ 2 * y) (hLa0 : 0 ≤ La) (hLa : La ≤ 2 * y)
    (hb' : 0 ≤ b') (hkb' : k * b' ≤ a) (hX0 : 0 ≤ Xpp) (hX : Xpp ≤ a)
    (hsA0 : 0 ≤ sA) (hsA : sA ≤ 2 * (nT * a)) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : lW ≤ a) (hlk0 : 0 ≤ lk) (hlk : lk ≤ g * y) (hlH0 : 0 ≤ lH) (hlH : lH ≤ h * y)
    (hdI0 : 0 ≤ dI) (hdI : dI ≤ 2) (het : et ≤ K * y * (nT * a))
    (c1 : 0 ≤ cDiv) (c1' : cDiv ≤ K) (c2 : 0 ≤ cE) (c2' : cE ≤ K) (c3 : 0 ≤ cH) (c3' : cH ≤ K)
    (c4 : 0 ≤ cCount) (c4' : cCount ≤ K) (c5 : 0 ≤ cSlope) (c5' : cSlope ≤ K)
    (c6 : 0 ≤ cSl1) (c6' : cSl1 ≤ K) (c7 : 0 ≤ cLoss) (c7' : cLoss ≤ K)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hbig : 200 * (1 + K) ^ 2 * h * g ≤ y) :
    sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et)
      ≤ yD * yL * y * y * y * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) := by
  have hK : 0 ≤ K := c1.trans c1'
  have hy0 : 0 ≤ y := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hnT0 : 0 ≤ nT := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = M ^ 2 / k := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = M / k := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact (div_le_one hk).2 hMk
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = nT * a := ⟨_, rfl⟩
  have hA1a : a ≤ A1 := by rw [hA1]; exact le_mul_of_one_le_left ha0 hnT
  have hA10 : 0 ≤ A1 := by linarith
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = M * B0 := ⟨_, rfl⟩
  have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = M * Nc := ⟨_, rfl⟩
  have hA40 : 0 ≤ A4 := by rw [hA4]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = A1 * (1 + r) + (A3 + A4) := ⟨_, rfl⟩
  have hA1r : 0 ≤ A1 * r := mul_nonneg hA10 hr0
  have orbitMap_conj_smul_one : A1 ≤ E := by rw [hE]; linarith only [hA1r, hA30, hA40]
  have eA1r : A1 * (1 + r) ≤ E := by rw [hE]; linarith only [hA30, hA40]
  have orbitMap_conj_smul_two : A1 * r ≤ E := by rw [hE]; linarith only [hA10, hA30, hA40]
  have selfLieBasisVector : A3 ≤ E := by rw [hE]; linarith only [hA10, hA1r, hA40]
  have eA34 : A3 + A4 ≤ E := by rw [hE]; linarith only [hA10, hA1r]
  have hE0 : 0 ≤ E := hA10.trans orbitMap_conj_smul_one
  have e1 : 1 ≤ E := by linarith only [ha1, hA1a, orbitMap_conj_smul_one]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = yD * yL * y := ⟨_, rfl⟩
  have hDL : 1 ≤ yD * yL := one_le_mul_of_one_le_of_one_le hyD hyL
  have yY : y ≤ Y := by rw [hY]; exact le_mul_of_one_le_left hy0 hDL
  have oneY : 1 ≤ Y := hy.trans yY
  have yDY : yD ≤ Y := by
    rw [hY, mul_assoc]
    exact le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le hyL hy)
  have yLY : yL ≤ Y := by
    have : yL ≤ yD * yL := le_mul_of_one_le_left (by linarith) hyD
    rw [hY]
    exact this.trans (le_mul_of_one_le_right (by linarith) hy)
  have hY0 : 0 ≤ Y := by linarith
  obtain ⟨P, hP⟩ : ∃ P, P = Y * E := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have EP : E ≤ P := by rw [hP]; exact le_mul_of_one_le_left hE0 oneY
  have hLaY : La ≤ 2 * Y := by linarith only [hLa, yY]
  have hLY : L ≤ 2 * Y := by linarith only [hL, yY]
  have hlkY : lk ≤ g * Y := hlk.trans (by gcongr)

  have T1 : sA * (cCount * (La + M ^ 2 * La / k)) ≤ 4 * K * P := by
    have e : sA * (cCount * (La + M ^ 2 * La / k)) = (sA * (1 + r)) * (cCount * La) := by
      rw [hr]; ring
    have s1 : sA * (1 + r) ≤ 2 * E := by
      have : sA * (1 + r) ≤ 2 * A1 * (1 + r) := by rw [hA1]; gcongr
      linarith only [this, eA1r]
    rw [e]
    calc (sA * (1 + r)) * (cCount * La) ≤ (2 * E) * (K * (2 * Y)) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T2a : cDiv * nT * a * La ≤ 2 * K * P := by
    calc cDiv * nT * a * La = cDiv * A1 * La := by rw [hA1]; ring
      _ ≤ K * E * (2 * Y) := by gcongr
      _ = 2 * K * P := by rw [hP]; ring
  have T2b : cDiv * M * (B0 + Nc) * yD ≤ K * P := by
    calc cDiv * M * (B0 + Nc) * yD = cDiv * (A3 + A4) * yD := by rw [hA3, hA4]; ring
      _ ≤ K * E * Y := by gcongr
      _ = K * P := by rw [hP]; ring
  have T3 : M * cE * B0 ≤ K * P := by
    calc M * cE * B0 = cE * A3 := by rw [hA3]; ring
      _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
  have T4 : cSlope * nT * a * La * (1 + M / k) ≤ 4 * K * P := by
    calc cSlope * nT * a * La * (1 + M / k) = cSlope * A1 * La * (1 + q) := by rw [hA1, hq]; ring
      _ ≤ K * E * (2 * Y) * (1 + 1) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T5 : lW ≤ P := by linarith only [hlW, hA1a, orbitMap_conj_smul_one, EP]
  have T60 : 0 ≤ cLoss * nT * M * b * yL := by positivity
  have FreeQuotientRank : cLoss * nT * M * b * yL ≤ K * P := by
    calc cLoss * nT * M * b * yL = cLoss * (nT * (M * b)) * yL := by ring
      _ ≤ K * (nT * a) * Y := by gcongr
      _ ≤ K * E * Y := by rw [← hA1]; gcongr
      _ = K * P := by rw [hP]; ring
  have Tmid : cSl1 * nT * M * (a / k + b') * (cCount * M * L) ≤ 4 * K ^ 2 * P := by
    have hb'k : b' ≤ a / k := by rw [le_div_iff₀ hk]; linarith
    have hQ : nT * M ^ 2 * (a / k + b') ≤ 2 * E := by
      calc nT * M ^ 2 * (a / k + b') ≤ nT * M ^ 2 * (a / k + a / k) := by gcongr
        _ = 2 * (A1 * r) := by rw [hA1, hr]; ring
        _ ≤ 2 * E := by linarith
    have hQ0 : 0 ≤ nT * M ^ 2 * (a / k + b') := by positivity
    calc cSl1 * nT * M * (a / k + b') * (cCount * M * L)
        = cSl1 * cCount * L * (nT * M ^ 2 * (a / k + b')) := by ring
      _ ≤ K * K * (2 * Y) * (2 * E) := by gcongr
      _ = 4 * K ^ 2 * P := by rw [hP]; ring
  have T7 : cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
      + cSl1 * Xpp + 1 ≤ (5 * K ^ 2 + K + 1) * P := by
    have s1 : cSl1 * (cLoss * nT * M * b * yL) ≤ K * (K * P) := by gcongr
    have s2 : cSl1 * Xpp ≤ K * P := by gcongr; linarith only [hX, hA1a, orbitMap_conj_smul_one, EP]
    have s3 : 1 ≤ P := e1.trans EP
    linarith only [s1, s2, s3, Tmid]
  have TU : cSlope * nT * a * La * (2 + M / k)
      + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
      + cSl1 * M * B0
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1) + b ≤ (5 * K ^ 2 + 13 * K + 2 * K * g + 2) * P := by
    have s1 : cSlope * nT * a * La * (2 + M / k) ≤ 6 * K * P := by
      calc cSlope * nT * a * La * (2 + M / k) = cSlope * A1 * La * (2 + q) := by rw [hA1, hq]; ring
        _ ≤ K * E * (2 * Y) * (2 + 1) := by gcongr
        _ = 6 * K * P := by rw [hP]; ring
    have s2 : cH * (nT * a * La + M * B0) ≤ 3 * K * P := by
      calc cH * (nT * a * La + M * B0) = cH * (A1 * La + A3) := by rw [hA1, hA3]
        _ ≤ K * (E * (2 * Y) + P) := by gcongr; exact selfLieBasisVector.trans EP
        _ = 3 * K * P := by rw [hP]; ring
    have s3 : sA * (cCount * lk) ≤ 2 * K * g * P := by
      calc sA * (cCount * lk) ≤ (2 * E) * (K * (g * Y)) := by
            gcongr
            rw [← hA1] at hsA; linarith
        _ = 2 * K * g * P := by rw [hP]; ring
    have s4 : cSl1 * M * B0 ≤ K * P := by
      calc cSl1 * M * B0 = cSl1 * A3 := by rw [hA3]; ring
        _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
    have s5 : b ≤ P := by linarith only [hba, hA1a, orbitMap_conj_smul_one, EP]
    linarith only [s1, s2, s3, s4, s5, T3, T7]
  have Tet : et ≤ K * P := by
    calc et ≤ K * y * A1 := by rw [hA1]; exact het
      _ ≤ K * Y * E := by gcongr
      _ = K * P := by rw [hP]; ring
  obtain ⟨u, hu⟩ : ∃ u, u = 5 * K ^ 2 + 13 * K + 2 * K * g + 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  rw [← hu] at TU
  have T8 : dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et) ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by
    have s1 : 4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) ≤ 4 * (h * y) * (u * P) := by
      calc _ ≤ 4 * lH * (u * P) := by gcongr
        _ ≤ 4 * (h * y) * (u * P) := by gcongr
    have s2 : 0 ≤ 4 * (h * y) * (u * P) + K * P := by positivity
    calc _ ≤ dI * (4 * (h * y) * (u * P) + K * P) := by gcongr
      _ ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by gcongr

  have hyP : P ≤ y * P := le_mul_of_one_le_left hP0 hy
  have hyP0 : 0 ≤ y * P := by positivity
  have hsum : (5 * K ^ 2 + 16 * K + 2) + 8 * h * u ≤ 200 * (1 + K) ^ 2 * h * g := by
    rw [hu]
    have hhg : 1 ≤ h * g := one_le_mul_of_one_le_of_one_le hh hg
    have a1 : (5 * K ^ 2 + 16 * K + 2) ≤ (5 * K ^ 2 + 16 * K + 2) * (h * g) :=
      le_mul_of_one_le_right (by positivity) hhg
    have a2 : 8 * h * (5 * K ^ 2 + 13 * K + 2 * K * g + 2)
        ≤ 8 * h * ((5 * K ^ 2 + 15 * K + 2) * g) := by
      gcongr
      have := mul_nonneg (by positivity : 0 ≤ 5 * K ^ 2 + 13 * K + 2) (by linarith only [hg] : 0 ≤ g - 1)
      linarith only [this]
    have a3 : (5 * K ^ 2 + 16 * K + 2) * (h * g) + 8 * h * ((5 * K ^ 2 + 15 * K + 2) * g)
        ≤ 200 * (1 + K) ^ 2 * h * g := by
      have : 0 ≤ (155 * K ^ 2 + 264 * K + 182) * (h * g) := by positivity
      linarith only [this]
    linarith only [a1, a2, a3]
  have hfin : (5 * K ^ 2 + 14 * K + 2) * P + 2 * (4 * (h * y) * (u * P) + K * P)
      ≤ y * (y * P) := by
    have b1 : (5 * K ^ 2 + 16 * K + 2) * P ≤ (5 * K ^ 2 + 16 * K + 2) * (y * P) := by gcongr
    have b2 : ((5 * K ^ 2 + 16 * K + 2) + 8 * h * u) * (y * P) ≤ y * (y * P) := by
      gcongr
      exact hsum.trans hbig
    linarith only [b1, b2]
  have hR : yD * yL * y * y * y * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) = y * (y * P) := by
    rw [hP, hY, hE, hA1, hA3, hA4, hr]; ring
  rw [hR]
  linarith only [T1, T2a, T2b, T3, T4, T5, FreeQuotientRank, T7, T8, hfin]
end Formalism.LFunctionChainParameters.LErr
