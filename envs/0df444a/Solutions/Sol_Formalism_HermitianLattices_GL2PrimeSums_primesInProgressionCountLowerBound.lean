-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.primesInProgressionCountLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:40.481951+00:00
-- url     : https://prove2.me/submissions/79b2c73d-b549-4005-abbd-4011d6b67243

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.GL2PrimeSums
private lemma gl2a4_rpow_le {b y p q : ℝ} (hb : 0 < b) (hy : 0 < y)
    (h : p * Real.log b ≤ q * Real.log y) : b ^ p ≤ y ^ q := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.mpr
  linarith
private lemma gl2a4_exp_small {C c s : ℝ} (hc : 0 < c) (hs : 200 * C / c ≤ s) :
    C * Real.exp (-(c * s)) ≤ 1 / 200 := by
  have h1 : 200 * C ≤ s * c := (div_le_iff₀ hc).1 hs
  have h2 := Real.add_one_le_exp (c * s)
  have h3 : Real.exp (-(c * s)) * Real.exp (c * s) = 1 := by
    rw [← Real.exp_add]
    simp
  have h4 : 0 < Real.exp (-(c * s)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h1 h4.le, mul_le_mul_of_nonneg_left h2 h4.le]
private lemma gl2a4_log_le_exp {c L : ℝ} (hc : 0 < c) (hLc : 1600 / c ≤ L) (hL0 : 0 ≤ L) :
    L ≤ c * Real.exp (L / 20) / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ L / 20)
  have h2 : 1600 ≤ L * c := (div_le_iff₀ hc).1 hLc
  have h3 : c * (1 + L / 20 + (L / 20) ^ 2 / 2) ≤ c * Real.exp (L / 20) :=
    mul_le_mul_of_nonneg_left h1 hc.le
  have e : c * (1 + L / 20 + (L / 20) ^ 2 / 2) = c + c * L / 20 + c * L ^ 2 / 800 := by ring
  rw [e] at h3
  have h4 : L * 1600 ≤ L * (L * c) := mul_le_mul_of_nonneg_left h2 hL0
  have h5 : 0 ≤ c * L := mul_nonneg hc.le hL0
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith
set_option maxHeartbeats 800000 in
private lemma gl2a4_count_core {C₀ Cr cr c : ℝ} (hC₀ : 0 < C₀) (hCr : 0 < Cr) (hcr : 0 < cr) (hc : 0 < c)
    (hP : PrimesAPInterval C₀ Cr cr c) :
    ∃ K₀ L₀ : ℝ, 0 ≤ K₀ ∧ ∀ (m a : ℕ), 3 ≤ m → Nat.Coprime a m → ∀ X : ℝ, 0 < X →
      L₀ ≤ Real.log X → K₀ * Real.log (4 * (m : ℝ)) ≤ Real.log X →
      X ^ ((9 : ℝ) / 10) ≤ ((PP m a X).card : ℝ) := by
  obtain ⟨K, hK1, hK2, hK3⟩ : ∃ K : ℝ, 2 * C₀ ≤ K ∧ 400 * Cr / cr ≤ K ∧ 120 ≤ K :=
    ⟨max (max (2 * C₀) (400 * Cr / cr)) 120, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨L, hL1, hL2, hL3⟩ : ∃ L : ℝ, 3 ≤ L ∧ 2 * (200 * Cr / cr) ^ 2 ≤ L ∧ 1600 / c ≤ L :=
    ⟨max (max 3 (2 * (200 * Cr / cr) ^ 2)) (1600 / c), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  refine ⟨K, L, by linarith, ?_⟩
  intro m a hm ha X hX hLX hKX
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hB0 : (0:ℝ) < 4 * (m:ℝ) := by linarith
  have hlB : 0 < Real.log (4 * (m:ℝ)) := Real.log_pos (by linarith)
  have hlX : 3 ≤ Real.log X := le_trans hL1 hLX
  have hX4 : 4 ≤ X := by
    have h1 := Real.add_one_le_exp (Real.log X)
    rw [Real.exp_log hX] at h1
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hY0 : 0 < X / 2 := by linarith
  have hlogY : Real.log (X / 2) = Real.log X - Real.log 2 := Real.log_div (by linarith) (by norm_num)
  have hlY1 : Real.log X / 2 ≤ Real.log (X / 2) := by rw [hlogY]; linarith
  have hlY2 : Real.log (X / 2) ≤ Real.log X := by rw [hlogY]; linarith
  have hlYpos : 0 < Real.log (X / 2) := by linarith
  have hK1' := mul_le_mul_of_nonneg_right hK1 hlB.le
  have hK3' := mul_le_mul_of_nonneg_right hK3 hlB.le
  have hA : (4 * (m:ℝ)) ^ C₀ ≤ X / 2 := by
    have := gl2a4_rpow_le (p := C₀) (q := 1) hB0 hY0 (by linarith)
    rwa [Real.rpow_one] at this
  have hR1 : Cr * Real.exp (-cr * Real.log (X / 2) / Real.log (4 * (m:ℝ))) ≤ 1 / 200 := by
    have hs : 200 * Cr / cr ≤ Real.log (X / 2) / Real.log (4 * (m:ℝ)) := by
      rw [le_div_iff₀ hlB]
      have e : 400 * Cr / cr = 2 * (200 * Cr / cr) := by ring
      have h1 := mul_le_mul_of_nonneg_right hK2 hlB.le
      rw [e] at h1
      linarith
    have e2 : -cr * Real.log (X / 2) / Real.log (4 * (m:ℝ)) =
        -(cr * (Real.log (X / 2) / Real.log (4 * (m:ℝ)))) := by ring
    rw [e2]
    exact gl2a4_exp_small hcr hs
  have hR2 : Cr * Real.exp (-cr * Real.sqrt (Real.log (X / 2))) ≤ 1 / 200 := by
    have h0 : 0 ≤ 200 * Cr / cr := by positivity
    have hs : 200 * Cr / cr ≤ Real.sqrt (Real.log (X / 2)) := by
      rw [Real.le_sqrt h0 hlYpos.le]
      linarith
    have e2 : -cr * Real.sqrt (Real.log (X / 2)) = -(cr * Real.sqrt (Real.log (X / 2))) := by ring
    rw [e2]
    exact gl2a4_exp_small hcr hs
  have hR : rhoErr Cr cr (4 * (m:ℝ)) (X / 2) ≤ 1 / 100 := by
    unfold rhoErr
    linarith
  have hD : (4 * (m:ℝ)) ^ (7:ℝ) ≤ 1 * (X / 2) ^ ((1:ℝ) / 3) := by
    rw [one_mul]
    exact gl2a4_rpow_le hB0 hY0 (by linarith)
  have hcount := hP m a hm ha (X / 2) 1 hA le_rfl hR hD
  have hsq : Real.sqrt X ≤ X / 2 := by
    rw [Real.sqrt_le_left hY0.le]
    nlinarith only [hX4]
  have hE : (4 * (m:ℝ)) ^ (6:ℝ) ≤ X ^ ((1:ℝ) / 20) :=
    gl2a4_rpow_le hB0 hX (by linarith)
  have hP6 : (4 * (m:ℝ)) ^ (-6:ℝ) * (4 * (m:ℝ)) ^ (6:ℝ) = 1 := by
    rw [Real.rpow_neg hB0.le]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hB0 _).ne'
  have hP6pos : 0 < (4 * (m:ℝ)) ^ (-6:ℝ) := Real.rpow_pos_of_pos hB0 _
  have hEpos : 0 < X ^ ((1:ℝ) / 20) := Real.rpow_pos_of_pos hX _
  have hFpos : 0 < X ^ ((9:ℝ) / 10) := Real.rpow_pos_of_pos hX _
  have hFEE : X ^ ((9:ℝ) / 10) * X ^ ((1:ℝ) / 20) * X ^ ((1:ℝ) / 20) = X := by
    rw [← Real.rpow_add hX, ← Real.rpow_add hX]
    norm_num
  have hLexp : Real.log X ≤ c * X ^ ((1:ℝ) / 20) / 2 := by
    have h1 := gl2a4_log_le_exp hc (le_trans hL3 hLX) (by linarith)
    have h2 : X ^ ((1:ℝ) / 20) = Real.exp (Real.log X / 20) := by
      rw [Real.rpow_def_of_pos hX]
      congr 1
      ring
    rw [h2]
    exact h1
  have hPE : 1 ≤ (4 * (m:ℝ)) ^ (-6:ℝ) * X ^ ((1:ℝ) / 20) := by
    have := mul_le_mul_of_nonneg_left hE hP6pos.le
    linarith
  refine le_trans ?_ (le_trans hcount (Nat.cast_le.mpr (Finset.card_le_card ?_)))
  · rw [le_div_iff₀ hlYpos]
    have f1 := mul_le_mul_of_nonneg_left hlY2 hFpos.le
    have f2 := mul_le_mul_of_nonneg_left hLexp hFpos.le
    have f4 := mul_le_mul_of_nonneg_left hPE
      (by positivity : (0:ℝ) ≤ c * X ^ ((9:ℝ) / 10) * X ^ ((1:ℝ) / 20))
    have f5 : c * (4 * (m:ℝ)) ^ (-6:ℝ) * (X ^ ((9:ℝ) / 10) * X ^ ((1:ℝ) / 20) * X ^ ((1:ℝ) / 20)) =
        c * (4 * (m:ℝ)) ^ (-6:ℝ) * X := by rw [hFEE]
    linarith
  · intro p hp
    unfold PP
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨lt_of_le_of_lt (Nat.floor_mono hsq) hp.1.1,
      le_trans hp.1.2 (Nat.floor_mono (le_of_eq (by ring)))⟩, hp.2⟩
end Formalism.HermitianLattices.GL2PrimeSums
end
end

set_option autoImplicit false
open Finset Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution : PrimesInProgressionCountLowerBound := by
  intro C₀ Cr cr c hC₀ hCr hcr hc hP ε hε hε1
  obtain ⟨K₀, L₀, hK₀, hmain⟩ := gl2a4_count_core hC₀ hCr hcr hc hP
  refine ⟨Real.exp (max (12 * K₀ + 1) (6 * L₀ / ε)), ?_⟩
  intro x hx m₀ a₀ hm₀ ha₀ X hX hlog1 hlog2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : max (12 * K₀ + 1) (6 * L₀ / ε) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hT1 : 12 * K₀ + 1 ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hT2 : 6 * L₀ / ε ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  apply hmain m₀ a₀ hm₀ ha₀ X hX
  · have h1 : x ^ (ε / 6) = Real.exp (Real.log x * (ε / 6)) := Real.rpow_def_of_pos hx0 _
    have h2 := Real.add_one_le_exp (Real.log x * (ε / 6))
    have h3 : 6 * L₀ ≤ Real.log x * ε := (div_le_iff₀ hε).1 hT2
    have h4 : L₀ ≤ Real.log x * (ε / 6) := by linarith
    linarith
  · have hm3 : (3:ℝ) ≤ (m₀:ℝ) := by exact_mod_cast hm₀
    have hlogm : 0 ≤ Real.log (m₀:ℝ) := Real.log_nonneg (by linarith)
    have h4 : Real.log (4 * (m₀:ℝ)) ≤ 3 * Real.log (m₀:ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith))]
      have h5 : Real.log 4 ≤ Real.log ((m₀:ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
      rw [Real.log_pow] at h5
      push_cast at h5
      linarith
    have h6 : 12 * K₀ ≤ Real.log x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log x - 1) (by linarith : (0:ℝ) ≤ Real.log x)]
    have h7 := mul_le_mul_of_nonneg_right h6 hlogm
    have h8 := mul_le_mul_of_nonneg_left h4 hK₀
    linarith
end Formalism.HermitianLattices.GL2PrimeSums
