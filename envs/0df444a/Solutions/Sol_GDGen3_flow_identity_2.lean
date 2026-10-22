-- Prove2me | solution 2 for GDGen3.flow_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:36:54.340315+00:00
-- url     : https://prove2.me/submissions/029fc03f-416f-4fc3-b750-abb9db957db1

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_prefix_telescope
import Theorems.Thm_GDGen3_Abar_ne_zero
import Theorems.Thm_GDGen3_eta_recur_holds
import Theorems.Thm_GDGen3_suffix_telescope
import Theorems.Thm_GDGen3_flow_prefix_split
import Theorems.Thm_GDGen3_cross_inner
import Theorems.Thm_GDGen3_cross_outer

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) (i : ℕ) (hi : i + 1 ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => d r ξ N k) = M r N * (i + 1) := by
  have hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0 := fun i hi => ne_of_gt (hpos i hi)
  have hrec := eta_recur_holds r N hN ξ hr hr1 hpos h0 hquad hquad7
  have hAiD : Abar ξ i * D r ξ N (i + 1) = pj r (i + 1) := by
    have h1 : ¬ (i + 1 = 0 ∨ N < i + 1) := by omega
    rw [D, if_neg h1, Am, if_neg (by omega : ¬ i + 1 = 0)]
    have h2 : i + 1 - 1 = i := by omega
    have hAne : Abar ξ i ≠ 0 := Abar_ne_zero ξ h0 hpos i
    rw [h2]
    field_simp
  have hsum : Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j)
      = eta r N ξ i * D r ξ N (i + 1) :=
    suffix_telescope r N hN ξ hr hr1 hpos h0
      (fun k hk => by simpa only [eta, add_assoc] using hquad k hk) hrec hpin i hi
  have hPref : Finset.sum (Finset.range i) (fun k => Abar ξ k) = ξ i * Abar ξ i :=
    prefix_telescope ξ h0 hne i
  rw [flow_prefix_split r ξ N i (le_of_lt hi)]
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.Icc (i + 1) N,
      Finset.sum (Finset.range (i + 1)) (fun k => ell r ξ N k j - ell r ξ N j k)
        = (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact cross_inner r ξ N i j h0 hne (by omega) hj.2
  rw [Finset.sum_congr rfl hinner, cross_outer r ξ N i hi h0 hne, hPref, hsum, hAiD]
  have hpne : pj r (i + 1) ≠ 0 := by
    have hlt : r ^ (2 * (i + 1)) < 1 := by
      have hN0 : 2 * (i + 1) ≠ 0 := by omega
      exact pow_lt_one₀ (le_of_lt hr) hr1 hN0
    rw [pj]
    exact div_ne_zero (by linarith) (by positivity)
  rw [eta, C]
  field_simp [hpne]
  rw [hAiD]
  ring

/-! ## Section 5 assembly: the certificate sum and (20) for arbitrary N -/
