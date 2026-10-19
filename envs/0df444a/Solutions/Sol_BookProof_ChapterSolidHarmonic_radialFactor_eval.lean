-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.radialFactor_eval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:59.662849+00:00
-- url     : https://prove2.me/submissions/31587c55-c19f-427e-98d9-1ad3f0710270

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.radialFactor_eval
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_deriv_coeff_eq_zero
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_deriv_coeff_parity
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) :
    radialFactor e l μ x
      = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖) := by

  classical
  set n := l - μ with hn
  set r := ‖x‖ with hr
  have hr0 : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hx
  set Y : ℝ[X] := derivative^[μ] (legendre l) with hY
  have hdeg : Y.natDegree < n + 1 := by
    by_contra hcon
    push_neg at hcon
    have hzero : Y.coeff Y.natDegree = 0 := by
      apply legendre_deriv_coeff_eq_zero
      omega
    have : Y = 0 := by
      by_contra hne
      exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hzero
    simp [this] at hcon
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
  set T : Finset ℕ := (Finset.range (n / 2 + 1)).image (fun m => n - 2 * m) with hT
  have hTsub : T ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [hT, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    exact Finset.mem_range.mpr (by omega)
  have hvanish : ∀ k ∈ Finset.range (n + 1), k ∉ T →
      r ^ n * (Y.coeff k * (⟪e, x⟫_ℝ / r) ^ k) = 0 := by
    intro k hk hkT
    have hpar : k % 2 ≠ n % 2 := by
      intro hcon
      apply hkT
      rw [hT, Finset.mem_image]
      refine ⟨(n - k) / 2, Finset.mem_range.mpr ?_, ?_⟩
      · have := Finset.mem_range.mp hk
        omega
      · have := Finset.mem_range.mp hk
        omega
    rw [legendre_deriv_coeff_parity l μ hμ k hpar]
    ring
  have hinj : Set.InjOn (fun m => n - 2 * m) ↑(Finset.range (n / 2 + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_subset hTsub hvanish, hT, Finset.sum_image hinj]
  rw [radialFactor]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm2 : 2 * m ≤ n := by
    have := Finset.mem_range.mp hm
    omega
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 * m := ⟨n - 2 * m, by omega⟩
  have hk' : n - 2 * m = k := by omega
  have hpow : r ^ n * ((⟪e, x⟫_ℝ / r) ^ (n - 2 * m))
      = (⟪e, x⟫_ℝ) ^ (n - 2 * m) * (r ^ 2) ^ m := by
    rw [hk', hk, div_pow, pow_add, pow_mul]
    field_simp
  rw [← hpow]
  ring
