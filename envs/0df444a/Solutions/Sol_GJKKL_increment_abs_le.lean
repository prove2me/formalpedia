-- Prove2me | solution 1 for GJKKL.increment_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:56.69325+00:00
-- url     : https://prove2.me/submissions/851f30ad-cf93-496a-a7a2-21b758edb832

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_card_loss_le
public import Theorems.Thm_GJKKL_frozen_cons_of_covered
public import Theorems.Thm_GJKKL_frozen_cons_of_mem
public import Theorems.Thm_GJKKL_frozen_cons_of_not_mem
public import Theorems.Thm_GJKKL_frozen_of_uncovered


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) {v : V} {h : List (Finset V)} {a : Finset V}
    (ha : a ∈ avail H h) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ) :
    |frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h| ≤
      k * c + |φ (h.length + 1) - φ h.length| := by
  by_cases hv : v ∈ covered h
  · rw [frozen_cons_of_covered H _ a hv, sub_self, abs_zero]; positivity
  by_cases hva : v ∈ a
  · rw [frozen_cons_of_mem H _ h hva, sub_self, abs_zero]; positivity
  rw [frozen_cons_of_not_mem H _ hv hva, frozen_of_uncovered H _ v hv]
  have hloss := card_loss_le H h hva hc
  rw [hk a (avail_subset H h ha)] at hloss
  have hlossR : (((Dv H h v).filter (fun f => ¬ Disjoint f a)).card : ℝ) ≤ k * c := by
    exact_mod_cast hloss
  have : σ * ((dv H h v : ℝ) - ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card) +
      φ (h.length + 1) - (σ * (dv H h v : ℝ) + φ h.length) =
      -σ * (((Dv H h v).filter (fun f => ¬ Disjoint f a)).card : ℝ) +
        (φ (h.length + 1) - φ h.length) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_neg, hσ, one_mul, Nat.abs_cast]
  linarith
end GJKKL
