-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.lseries_taylor_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:28:47.903628+00:00
-- url     : https://prove2.me/submissions/9d3fb058-6ff4-4d96-ad82-10ff5214903a

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_lseries_at_two
import Theorems.Thm_Formalism_ZeroFreeDirichlet_iteratedDeriv_lseries_alternating_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_iteratedDeriv_lseries_at_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {F G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries a s) (hFG : ∀ s : ℂ, s ≠ 1 → F s = G s + lam / (s - 1))
    {B : ℝ} (hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ B) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ)
    (hσ2 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖lam‖ * (2 - σ) ^ M / (1 - σ) - 4 * B * (3 / 4) ^ M ≤ (F σ).re := by
  set x : ℝ := 2 - σ with hxdef
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hx2 : x ≤ 9 / 8 := by rw [hxdef]; linarith
  have hFG' : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹ := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs
    rw [← hF s hs, hFG s hs1, div_eq_mul_inv]
  have hcoef := iteratedDeriv_lseries_at_two hG hFG'

  have hB0 : 0 ≤ B := by
    have hmem : (2 : ℂ) + ((3 / 2 : ℝ) : ℂ) ∈ Metric.sphere (2 : ℂ) (3 / 2) := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real]
      norm_num
    exact (norm_nonneg _).trans (hB _ hmem)

  set t : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n G 2 with htdef
  have hT : HasSum t (G σ) := Complex.hasSum_taylorSeries_of_entire hG 2 (σ : ℂ)
  have hsplit := hT.summable.sum_add_tsum_nat_add M
  rw [hT.tsum_eq] at hsplit
  set β : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries a) 2) with hβdef
  have hβ0 : ∀ n, 0 ≤ β n := by
    intro n
    refine mul_nonneg ?_ (iteratedDeriv_lseries_alternating_nonneg ha0 habs n)
    have : (0 : ℂ) ≤ (n ! : ℂ) := by exact_mod_cast (Nat.zero_le _)
    exact inv_nonneg.mpr this
  have hσx : (σ : ℂ) - 2 = -(x : ℂ) := by rw [hxdef]; push_cast; ring
  have ht : ∀ n, t n = (x : ℂ) ^ n * β n - lam * (x : ℂ) ^ n := by
    intro n
    have hg : iteratedDeriv n G 2 = iteratedDeriv n (LSeries a) 2 - lam * ((-1) ^ n * (n ! : ℂ)) := by
      rw [hcoef n]; ring
    have hpow : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; simp
    have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [htdef, hβdef, smul_eq_mul, hσx, hg, neg_pow (x : ℂ) n]
    have hQ : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hfac
    linear_combination (-(lam * (x : ℂ) ^ n * ((n ! : ℂ)⁻¹ * (n ! : ℂ)))) * hpow + (-(lam * (x : ℂ) ^ n)) * hQ

  have hfin : ∑ i ∈ Finset.range M, t i =
      ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i - lam * (((x : ℂ) ^ M - 1) / ((x : ℂ) - 1)) := by
    rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_sub_distrib, ← Finset.mul_sum, geom_sum_eq]
    intro h
    have : x = 1 := by exact_mod_cast h
    linarith
  have hpos : 1 ≤ ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i := by
    have hnn : ∀ i ∈ Finset.range M, 0 ≤ (x : ℂ) ^ i * β i := by
      intro i _
      refine mul_nonneg ?_ (hβ0 i)
      have : (0 : ℂ) ≤ (x : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ x)
      exact pow_nonneg this i
    have h0 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 0 < M))
    have hb0 : (x : ℂ) ^ 0 * β 0 = LSeries a 2 := by simp [hβdef]
    rw [hb0] at h0
    exact (one_le_lseries_at_two ha0 ha1 habs).trans h0

  have htail : ‖∑' i, t (i + M)‖ ≤ 4 * B * (3 / 4) ^ M := by
    have hg : HasSum (fun i : ℕ => B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i) (B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := tsum_of_norm_bounded hg (f := fun i => t (i + M)) (by
      intro i
      have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (i + M)
        (by norm_num : (0 : ℝ) < 3 / 2) hG.diffContOnCl hB
      have hnorm : ‖t (i + M)‖ = ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖ := by
        simp only [htdef, smul_eq_mul, norm_mul, norm_inv, norm_pow, hσx, norm_neg, Complex.norm_real,
          Complex.norm_natCast]
        rw [Real.norm_of_nonneg (by linarith)]
        ring
      rw [hnorm]
      have hfac : (0 : ℝ) < ((i + M) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hxp : 0 ≤ x ^ (i + M) := pow_nonneg (by linarith) _
      calc ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖
          ≤ ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * (((i + M) ! : ℝ) * B / (3 / 2) ^ (i + M)) := by
            gcongr
        _ = B * (x ^ (i + M) / (3 / 2) ^ (i + M)) := by field_simp
        _ = B * (x / (3 / 2)) ^ (i + M) := by rw [div_pow x (3 / 2 : ℝ)]
        _ ≤ B * (3 / 4) ^ (i + M) := by
            have hq : x / (3 / 2) ≤ 3 / 4 := by rw [div_le_iff₀ (by norm_num)]; linarith
            have hq0 : 0 ≤ x / (3 / 2) := by positivity
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) hB0
        _ = B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i := by rw [pow_add]; ring)
    calc ‖∑' i, t (i + M)‖ ≤ B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹ := hle
      _ = 4 * B * (3 / 4) ^ M := by norm_num; ring

  have hσ1' : (σ : ℂ) ≠ 1 := by
    intro h; have : σ = 1 := by exact_mod_cast h
    linarith
  have hkey : F σ = ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i
      - lam * (((x ^ M / (x - 1) : ℝ)) : ℂ) + ∑' i, t (i + M) := by
    rw [hFG σ hσ1', ← hsplit, hfin]
    have hx1' : (x : ℂ) - 1 ≠ 0 := by
      intro h; have : x = 1 := by
        have h' : ((x - 1 : ℝ) : ℂ) = 0 := by push_cast; exact h
        have := Complex.ofReal_eq_zero.mp h'; linarith
      linarith
    have hσc : (σ : ℂ) - 1 = -((x : ℂ) - 1) := by rw [hxdef]; push_cast; ring
    rw [hσc]
    push_cast
    field_simp
    ring
  have hre := congrArg Complex.re hkey
  rw [Complex.add_re, Complex.sub_re] at hre
  have h1 : 1 ≤ (∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i).re := by
    have := (Complex.le_def.mp hpos).1
    simpa using this
  have h2 : (lam * (((x ^ M / (x - 1) : ℝ)) : ℂ)).re ≤ ‖lam‖ * x ^ M / (x - 1) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
    · ring_nf; rfl
    · exact div_nonneg (pow_nonneg (by linarith) _) (by linarith)
  have h3 : -(4 * B * (3 / 4) ^ M) ≤ (∑' i, t (i + M)).re := by
    have := Complex.abs_re_le_norm (∑' i, t (i + M))
    have := neg_abs_le (∑' i, t (i + M)).re
    linarith
  have hx1s : x - 1 = 1 - σ := by rw [hxdef]; ring
  rw [hx1s] at h2 hre
  rw [hre]
  linarith
end Formalism.ZeroFreeDirichlet
