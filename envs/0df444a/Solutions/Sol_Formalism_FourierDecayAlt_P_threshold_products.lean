-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_products
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:36.774134+00:00
-- url     : https://prove2.me/submissions/4968a035-dfb4-46e9-96a7-dfb03bf23590

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_prodBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ThresholdProducts := by
  intro ι _ t B1 B k C A0 Ct ka N I g Del TT i s hC hA0 hCt hka hkapi hN hI hg hDel hTT hCN ht htp hB1 hB hi
  have hC0 : 0 ≤ C := by linarith
  have hg0 : 0 < g := by linarith
  have hq0 : 0 ≤ C * Real.pi * N / I := by positivity
  have hbase0 : 0 ≤ C * ka * N / (g * I) := by positivity
  have hbase : C * ka * N / (g * I) ≤ C * Real.pi * N / I := by
    rw [div_le_div_iff₀ (by positivity) hI]
    have h1 : C * ka * N ≤ C * Real.pi * N := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkapi hC0) hN.le
    have h2 : C * Real.pi * N ≤ C * Real.pi * N * g := le_mul_of_one_le_right (by positivity) hg
    have h3 : C * ka * N * I ≤ C * Real.pi * N * g * I :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) hI.le
    linarith
  have hbase1 : C * ka * N / (g * I) ≤ 1 := le_trans hbase hCN
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hCB : ∀ w, C * B w ≤ C * A0 * Real.sqrt k * t w := fun w => by
    have := mul_le_mul_of_nonneg_left (hB w).2 hC0
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : ∀ b, xHat 1 C ka N I g b = C * b := fun b => by simp [xHat]
    have hs : Real.sqrt (k * N ^ 3 / Del) = Real.sqrt k * Real.sqrt (N ^ 3 / Del) := by
      rw [mul_div_assoc, Real.sqrt_mul (Nat.cast_nonneg k)]
    have := Sz8.prodBound (fun w => xHat 1 C ka N I g (B1 w)) t
      (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Ct (by positivity) (fun w => by
        simp only [e]
        refine ⟨mul_nonneg hC0 (hB1 w).1, ?_⟩
        have := mul_le_mul_of_nonneg_left (hB1 w).2 hC0
        rw [hs]; linarith) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow, mul_assoc]
  · intro hi2
    have hex : 2 ≤ 2 * i - 2 := by omega
    have := Sz8.prodBound (fun w => xHat i C ka N I g (B w)) t
      (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Ct (by positivity) (fun w => by
        simp only [xHat]
        have hp1 : (C * ka * N / (g * I)) ^ (2 * i - 2) ≤ (C * ka * N / (g * I)) ^ 2 :=
          pow_le_pow_of_le_one hbase0 hbase1 hex
        have hp2 : (C * ka * N / (g * I)) ^ 2 ≤ (C * Real.pi * N / I) ^ 2 :=
          pow_le_pow_left₀ hbase0 hbase 2
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        refine ⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩
        calc C * B w * (C * ka * N / (g * I)) ^ (2 * i - 2)
            ≤ (C * A0 * Real.sqrt k * t w) * (C * Real.pi * N / I) ^ 2 :=
              mul_le_mul (hCB w) (le_trans hp1 hp2) (pow_nonneg hbase0 _) (by nlinarith [hCB w])
          _ = _ := by ring) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  · intro hs2
    have hex : 1 ≤ 2 * (i - 1) + s - 1 := by omega
    have := Sz8.prodBound (fun w => lamHat i s C ka N I g (B w)) t
      (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Ct (by positivity) (fun w => by
        simp only [lamHat]
        have hp1 : (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1) ≤ (C * ka * N / (g * I)) ^ 1 :=
          pow_le_pow_of_le_one hbase0 hbase1 hex
        rw [pow_one] at hp1
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        refine ⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩
        calc C * B w * (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1)
            ≤ (C * A0 * Real.sqrt k * t w) * (C * Real.pi * N / I) :=
              mul_le_mul (hCB w) (le_trans hp1 hbase) (pow_nonneg hbase0 _) (by nlinarith [hCB w])
          _ = _ := by ring) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow]; ring
  · have hsT : 0 < Real.sqrt TT := Real.sqrt_pos.mpr hTT
    have hst : ∏ w, Real.sqrt (t w) ≤ Real.sqrt Ct := by
      apply Real.le_sqrt_of_sq_le
      rw [← Finset.prod_pow]
      have e : ∀ w, Real.sqrt (t w) ^ 2 = t w := fun w => Real.sq_sqrt (ht w)
      simp only [e]; exact htp
    have hQ : 0 ≤ Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT := by positivity
    have := Sz8.prodBound (fun w => lamPrimeHat i C ka N I g (B w) TT) (fun w => Real.sqrt (t w))
      (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) (Real.sqrt Ct) (Real.sqrt_nonneg _)
      (fun w => by
        simp only [lamPrimeHat]
        refine ⟨Real.sqrt_nonneg _, ?_⟩
        rw [← Real.sqrt_mul hQ]
        apply Real.sqrt_le_sqrt
        have e : C * B w * (g ^ (2 * i - 2))⁻¹ * ka * (C * ka * N / I) ^ (2 * (i - 1)) * (Real.sqrt TT)⁻¹
            = (C * B w * ka * (Real.sqrt TT)⁻¹) * (C * ka * N / (g * I)) ^ (2 * (i - 1)) := by
          rw [show 2 * i - 2 = 2 * (i - 1) by omega, div_pow, div_pow, mul_pow]; ring
        rw [e]
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        have hX0 : 0 ≤ C * B w * ka * (Real.sqrt TT)⁻¹ := by positivity
        have hp : (C * ka * N / (g * I)) ^ (2 * (i - 1)) ≤ 1 := pow_le_one₀ hbase0 hbase1
        have h1 : C * B w * ka * (Real.sqrt TT)⁻¹ ≤ (C * A0 * Real.sqrt k * t w) * Real.pi * (Real.sqrt TT)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hsT.le)
          exact mul_le_mul (hCB w) hkapi hka.le (by nlinarith [hCB w])
        calc (C * B w * ka * (Real.sqrt TT)⁻¹) * (C * ka * N / (g * I)) ^ (2 * (i - 1))
            ≤ (C * B w * ka * (Real.sqrt TT)⁻¹) * 1 := mul_le_mul_of_nonneg_left hp hX0
          _ ≤ (C * A0 * Real.sqrt k * t w) * Real.pi * (Real.sqrt TT)⁻¹ := by rw [mul_one]; exact h1
          _ = _ := by ring) hst
    exact this
end Formalism.FourierDecayAlt.P
