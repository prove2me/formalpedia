-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.log_ratio_upper_bound_of_upper_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:58.546033+00:00
-- url     : https://prove2.me/submissions/8005417f-e079-4adf-aba6-f08efb87b645

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioUpperBoundOfUpperPlace
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_log_zetaR_le
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_log_fact_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
set_option maxHeartbeats 800000
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hU : UpperPlace) : LogRatioUpperBound := by
  intro ε C₀ C₃ hε hε52 hC₀ hC₃
  refine ⟨30 + 7 * C₀ / ε + 3 * C₀ + Real.log C₃, ?_⟩
  intro x hx
  dsimp only
  intro f m k vE Δ g₁ g₂ u v b w Dstar dstar massk massr Isig Ipi Lval dsig hf hm2 hmeven hk2 hmL hkx
    hπ hlogvE hΔ hg₁ hg₂ hlg₁ hlg₂ hplace hmk0 hmr0 hIs hIp hL hmass hidx hD h3 hd

  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hLpos : 0 < x ^ ε := by linarith
  have hlogx : Real.log x ≤ x ^ ε / ε := by
    have h1 : Real.log (x ^ ε) = ε * Real.log x := Real.log_rpow hx0 ε
    have h2 : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos hLpos
    rw [le_div_iff₀ hε]; linarith
  have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hlogk : Real.log k ≤ C₀ * (x ^ ε / ε) := by
    have h1 := Real.log_le_log hk0 hkx
    rw [Real.log_rpow hx0] at h1
    linarith [mul_le_mul_of_nonneg_left hlogx hC₀]
  have hlog2k : Real.log (2 * k) ≤ 1 + C₀ * (x ^ ε / ε) := by
    rw [Real.log_mul (by norm_num) hk0.ne']
    have := Real.log_two_lt_d9
    linarith
  have hlog2k0 : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith)
  have hmkR : (m : ℝ) ≤ k := by
    have h1 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * x ^ ε := le_mul_of_one_le_right (by positivity) hL1
    have h2 : (m : ℝ) * 1 ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_left (by linarith) hm0
    nlinarith
  have hmkN : m ≤ k := by exact_mod_cast hmkR
  have hpl : ∀ ρ, ρ < f → 0 < dimVN (u ρ) k ∧ 0 < dTau k m (rowPar k (v ρ) (b ρ)) ∧
      Real.log (4 * dTau k m (rowPar k (v ρ) (b ρ)) *
        (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
          (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) - Real.log (dimVN (u ρ) k)
        ≤ (k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10) :=
    fun ρ hρ => hU ε x hε hx k m Δ C₃ (u ρ) (v ρ) (b ρ) (w ρ) hm2 hmeven hk2 hmkR hΔ hC₃
      (hplace ρ hρ).1 (hplace ρ hρ).2

  have hvEpos : 0 < vE := lt_of_lt_of_le Real.pi_pos hπ
  have hq1 : 1 ≤ vE / Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith
  have hlq0 : 0 ≤ Real.log (vE / Real.pi) := Real.log_nonneg hq1
  have hlqL : Real.log (vE / Real.pi) ≤ x ^ ε := by
    rw [Real.log_div hvEpos.ne' Real.pi_pos.ne']
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hsq1 : 1 ≤ Real.sqrt ((2 * vE) ^ f) :=
    Real.one_le_sqrt.mpr (one_le_pow₀ (by linarith [Real.pi_gt_three]))
  have hterm : ∀ M ∈ Ico (k + 1) (k - 1 + m + 1),
      0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M ∧
      Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f /
          Real.sqrt ((2 * vE) ^ f) * Lval M) ≤ f * (2 * k * Real.log (2 * k) + 2 * k * x ^ ε + 2) := by
    intro M hM
    obtain ⟨hLv, habs⟩ := hL M hM
    have hM' := Finset.mem_Ico.1 hM
    have hMk : M ≤ 2 * k := by omega
    have hfp : (0 : ℝ) < ((M - 1).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
    have hqp : (0 : ℝ) < (vE / Real.pi) ^ M := pow_pos (by linarith) _
    have hX : 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M := mul_pos hfp hqp
    have hs : 0 < Real.sqrt ((2 * vE) ^ f) := by linarith
    refine ⟨mul_pos (div_pos (pow_pos hX _) hs) hLv, ?_⟩
    rw [Real.log_mul (div_pos (pow_pos hX _) hs).ne' hLv.ne', Real.log_div (pow_pos hX _).ne' hs.ne',
      Real.log_pow, Real.log_mul hfp.ne' hqp.ne', Real.log_pow]
    have hfact := log_fact_le (M := M) (k := k) (by omega) (by omega)
    have hls : 0 ≤ Real.log (Real.sqrt ((2 * vE) ^ f)) := Real.log_nonneg hsq1
    have hlv : Real.log (Lval M) ≤ f * 2 :=
      (le_abs_self _).trans (habs.trans (mul_le_mul_of_nonneg_left (log_zetaR_le (by omega)) hf0))
    have hMR : (M : ℝ) ≤ 2 * k := by exact_mod_cast hMk
    have hML : (M : ℝ) * Real.log (vE / Real.pi) ≤ 2 * k * x ^ ε := by
      calc (M : ℝ) * Real.log (vE / Real.pi) ≤ 2 * k * Real.log (vE / Real.pi) :=
            mul_le_mul_of_nonneg_right hMR hlq0
        _ ≤ 2 * k * x ^ ε := mul_le_mul_of_nonneg_left hlqL (by positivity)
    linarith [mul_le_mul_of_nonneg_left (add_le_add hfact hML) hf0]
  have hA : Real.log massr - Real.log massk ≤ (f : ℝ) * k * m * (2 * Real.log (2 * k) + 2 * x ^ ε + 2) := by
    have hP : 0 < ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
        ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M :=
      prod_pos (fun M hM => (hterm M hM).1)
    rw [hmass, Real.log_mul hmk0.ne' hP.ne', Real.log_prod (fun M hM => (hterm M hM).1.ne')]
    have hsum := Finset.sum_le_card_nsmul (Ico (k + 1) (k - 1 + m + 1))
      (fun M => Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f /
          Real.sqrt ((2 * vE) ^ f) * Lval M)) _ (fun M hM => (hterm M hM).2)
    rw [Nat.card_Ico, nsmul_eq_mul] at hsum
    have hcard : ((k - 1 + m + 1 - (k + 1) : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (by omega : k - 1 + m + 1 - (k + 1) ≤ m)
    have hb0 : 0 ≤ (f : ℝ) * (2 * k * Real.log (2 * k) + 2 * k * x ^ ε + 2) :=
      mul_nonneg hf0 (by
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk0.le) hlog2k0
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk0.le) hLpos.le
        linarith)
    have h1 := mul_le_mul_of_nonneg_right hcard hb0
    have h2 : (f : ℝ) * m * 1 ≤ f * m * k := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hf0 hm0)
    linarith

  have hB : Real.log Isig - Real.log Ipi ≤ (f : ℝ) * k * m * (2 + 3 * C₀ * x ^ ε) := by
    rw [← Real.log_div hIs.ne' hIp.ne']
    have hg : 0 < g₁ * g₂ := mul_pos (by linarith) (by linarith)
    have h2 : (0 : ℝ) < 2 ^ (2 * f) := by positivity
    have hr : 0 < (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) := Real.rpow_pos_of_pos hg _
    have hmain := Real.log_le_log (div_pos hIs hIp) hidx
    rw [Real.log_mul h2.ne' hr.ne', Real.log_pow, Real.log_rpow hg,
      Real.log_mul (by linarith) (by linarith)] at hmain
    push_cast at hmain
    have hE0 : 0 ≤ (f : ℝ) * m * (2 * k + m - 1) / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hf0 hm0) (by linarith)) (by norm_num)
    have hE1 : (f : ℝ) * m * (2 * k + m - 1) / 2 ≤ 3 / 2 * f * m * k := by
      have := mul_le_mul_of_nonneg_left (show (m : ℝ) - 1 ≤ k by linarith) (mul_nonneg hf0 hm0)
      linarith
    have hlg : Real.log g₁ + Real.log g₂ ≤ 2 * C₀ * x ^ ε := by linarith
    have hCL : 0 ≤ C₀ * x ^ ε := mul_nonneg hC₀ hLpos.le
    have h1 := mul_le_mul_of_nonneg_left hlg hE0
    have h1' := mul_le_mul_of_nonneg_right hE1 (show 0 ≤ 2 * C₀ * x ^ ε by linarith)
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : (f : ℝ) * Real.log 2 ≤ f * 1 := mul_le_mul_of_nonneg_left hl2 hf0
    have hkm1 : (1 : ℝ) ≤ k * m := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hfkm : (f : ℝ) * 1 ≤ f * (k * m) := mul_le_mul_of_nonneg_left hkm1 hf0
    linarith

  have hC : ∑ ρ ∈ range f, (Real.log (dsig ρ) - Real.log (dimVN (u ρ) k)) ≤
      (f : ℝ) * ((k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10)) := by
    have hle := Finset.sum_le_sum (s := range f)
      (f := fun ρ => Real.log (dsig ρ) - Real.log (dimVN (u ρ) k))
      (g := fun _ => (k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10))
      (fun ρ hρ => by
        have hρ' := mem_range.1 hρ
        obtain ⟨_, _, hup⟩ := hpl ρ hρ'
        have h3ρ := h3 ρ hρ'
        have := Real.log_le_log h3ρ.1 h3ρ.2
        linarith)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hle

  have hprodsig : 0 < ∏ ρ ∈ range f, dsig ρ := prod_pos (fun ρ hρ => (h3 ρ (mem_range.1 hρ)).1)
  have hproddim : 0 < ∏ ρ ∈ range f, dimVN (u ρ) k :=
    prod_pos (fun ρ hρ => (hpl ρ (mem_range.1 hρ)).1)
  have hDpos : 0 < Dstar := by rw [hD]; exact mul_pos (mul_pos hmr0 hIs) hprodsig
  have hdpos : 0 < dstar := by rw [hd]; exact mul_pos (mul_pos hmk0 hIp) hproddim
  have e1 : Real.log Dstar = Real.log massr + Real.log Isig + ∑ ρ ∈ range f, Real.log (dsig ρ) := by
    rw [hD, Real.log_mul (mul_pos hmr0 hIs).ne' hprodsig.ne', Real.log_mul hmr0.ne' hIs.ne',
      Real.log_prod (fun ρ hρ => (h3 ρ (mem_range.1 hρ)).1.ne')]
  have e2 : Real.log dstar = Real.log massk + Real.log Ipi + ∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) := by
    rw [hd, Real.log_mul (mul_pos hmk0 hIp).ne' hproddim.ne', Real.log_mul hmk0.ne' hIp.ne',
      Real.log_prod (fun ρ hρ => (hpl ρ (mem_range.1 hρ)).1.ne')]
  have hsplit : Real.log (Dstar / dstar) = (Real.log massr - Real.log massk) +
      (Real.log Isig - Real.log Ipi) + ∑ ρ ∈ range f, (Real.log (dsig ρ) - Real.log (dimVN (u ρ) k)) := by
    rw [Real.log_div hDpos.ne' hdpos.ne', e1, e2, Finset.sum_sub_distrib]; ring
  have hQ : 7 * Real.log (2 * k) + 7 * x ^ ε + 14 + 3 * C₀ * x ^ ε + Real.log C₃ ≤
      (30 + 7 * C₀ / ε + 3 * C₀ + Real.log C₃) * x ^ ε := by
    have hexp : (30 + 7 * C₀ / ε + 3 * C₀ + Real.log C₃) * x ^ ε =
        30 * x ^ ε + 7 * (C₀ * (x ^ ε / ε)) + 3 * C₀ * x ^ ε + Real.log C₃ * x ^ ε := by ring
    have hlc : 0 ≤ Real.log C₃ := Real.log_nonneg hC₃
    have : Real.log C₃ ≤ Real.log C₃ * x ^ ε := le_mul_of_one_le_right hlc hL1
    rw [hexp]; linarith
  have hfk : (0 : ℝ) < f * k := by positivity
  have hfkm0 : 0 ≤ (f : ℝ) * k * m := by positivity
  have hkey : Real.log (Dstar / dstar) ≤
      ((f : ℝ) * k) * ((30 + 7 * C₀ / ε + 3 * C₀ + Real.log C₃) * m * x ^ ε) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hQ hfkm0
    linarith
  rw [one_div, inv_mul_le_iff₀ hfk]
  exact hkey
end Formalism.LogVandermondeBounds.StandardLattice
