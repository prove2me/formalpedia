-- Prove2me | solution 1 for FD1D.finite_time_hazard_drift_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:56.438412+00:00
-- url     : https://prove2.me/submissions/2a2a69fe-abdc-40de-83c5-a334794d152c

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_finite_time_drift_telescope
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {T : ℕ} {a L c B : ℝ} (Phi D R H : ℕ → ℝ)
    (hT : 0 < T)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t)
    (hD : ∀ t < T, a * (H t / 100 - c) ≤ D t)
    (hR : ∀ t < T, R t ≤ L * H t)
    (hPhi0 : 0 ≤ Phi 0) (hPhiT : Phi T ≤ B) :
    (a / 100 - L) *
        ((∑ t ∈ Finset.range T, H t) / T) ≤
      a * c + B / T := by
  have htel := finite_time_drift_telescope T Phi D R hdrift
  have hDsum :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) ≤
        ∑ t ∈ Finset.range T, D t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hD t (Finset.mem_range.mp ht)
  have hRsum :
      ∑ t ∈ Finset.range T, R t ≤
        ∑ t ∈ Finset.range T, L * H t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hR t (Finset.mem_range.mp ht)
  have hraw :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) ≤
        ∑ t ∈ Finset.range T, L * H t + B := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hexpand :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) =
        a / 100 * (∑ t ∈ Finset.range T, H t) -
          (T : ℝ) * (a * c) := by
    have hterm : ∀ t, a * (H t / 100 - c) =
        a / 100 * H t - a * c := by
      intro t
      ring
    simp_rw [hterm, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp
  have hLexpand :
      ∑ t ∈ Finset.range T, L * H t =
        L * ∑ t ∈ Finset.range T, H t := by
    rw [Finset.mul_sum]
  rw [hexpand, hLexpand] at hraw
  have htarget :
      (a / 100 - L) * (∑ t ∈ Finset.range T, H t) ≤
        (T : ℝ) * (a * c) + B := by
    nlinarith
  calc
    (a / 100 - L) * ((∑ t ∈ Finset.range T, H t) / T) =
        ((a / 100 - L) * (∑ t ∈ Finset.range T, H t)) / T := by ring
    _ ≤ ((T : ℝ) * (a * c) + B) / T :=
      div_le_div_of_nonneg_right htarget hTreal.le
    _ = a * c + B / T := by
      field_simp
end FD1D
