-- Prove2me | solution 1 for ConformalCovariateShift.perm_weight_cov_shift
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:02:11.40942+00:00
-- url     : https://prove2.me/submissions/1eb67fd3-1c1b-4d50-9c54-32cbf0167688

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory
namespace ConformalCovariateShift

lemma pw_card {n : ℕ} (i : Fin (n + 1)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = i)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = Fin.last n)).card := by
  apply Finset.card_bij' (fun σ _ => Equiv.swap i (Fin.last n) * σ)
    (fun σ _ => Equiv.swap i (Fin.last n) * σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_right]
  · intro σ _; simp [Equiv.swap_mul_self_mul]
  · intro σ _; simp [Equiv.swap_mul_self_mul]

lemma pw_main {E : Type*} {n : ℕ} (f : E → ℝ) (z : Fin (n + 1) → E) (i : Fin (n + 1)) :
    permWeight (fun j (p : E) => if j = Fin.last n then f p else 1) z i =
      f (z i) / ∑ k, f (z k) := by
  unfold permWeight
  set c := (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = Fin.last n)).card
  have hc : (c : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin (n + 1))) ∈
        Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = Fin.last n) := by simp
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  have hprod : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∏ j, (if j = Fin.last n then f (z (σ j)) else 1) = f (z (σ (Fin.last n))) := by
    intro σ; rw [Finset.prod_ite_eq']; simp
  simp_rw [hprod]
  have hnum : ∀ k, ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = k),
      f (z (σ (Fin.last n))) = c * f (z k) := by
    intro k
    rw [Finset.sum_congr rfl (g := fun _ => f (z k)) (fun σ hσ => by
      simp only [Finset.mem_filter] at hσ; rw [hσ.2]), Finset.sum_const, pw_card, nsmul_eq_mul]
  rw [hnum, ← Finset.sum_fiberwise (g := fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n))]
  simp_rw [hnum]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc]

theorem perm_weight_cov_shift {d n : ℕ} (w : (Fin d → ℝ) → ℝ) (data : Fin n → DataPt d)
    (x : Fin d → ℝ) (y : ℝ) :
    permWeight (fun j (z : DataPt d) => if j = Fin.last n then w z.1 else 1)
        (withTest data (x, y)) =
      covShiftWeights w (fun i => (data i).1) x  := by
  rw [show (fun j (z : DataPt d) => if j = Fin.last n then w z.1 else 1) =
      (fun j (p : DataPt d) => if j = Fin.last n then (fun q : DataPt d => w q.1) p else 1) from rfl]
  funext i
  rw [pw_main]
  have hs : ∀ k, (withTest data (x, y) k).1 = withTest (fun i => (data i).1) x k := by
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [withTest]
    · simp [withTest]
  unfold covShiftWeights
  simp only [hs]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [withTest]

end ConformalCovariateShift
open ConformalCovariateShift in
theorem solution {d n : ℕ} (w : (Fin d → ℝ) → ℝ) (data : Fin n → DataPt d)
    (x : Fin d → ℝ) (y : ℝ) :
    permWeight (fun j (z : DataPt d) => if j = Fin.last n then w z.1 else 1)
        (withTest data (x, y)) =
      covShiftWeights w (fun i => (data i).1) x :=
  perm_weight_cov_shift w data x y
