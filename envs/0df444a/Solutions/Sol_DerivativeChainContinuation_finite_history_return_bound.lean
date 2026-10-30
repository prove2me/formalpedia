-- Prove2me | solution 1 for DerivativeChainContinuation.finite_history_return_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:18:07.272689+00:00
-- url     : https://prove2.me/submissions/f308d86d-7103-4342-9b50-42b8d668a96a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_finite_return_cost_bound
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators









theorem compressed_prefix_cauchy (h : ℕ) (r : ℝ) (l : ℕ → ℝ) :
    (r+∑ j ∈ Finset.range h, l j)^2 ≤
      (h+1 : ℝ)*(r^2+∑ j ∈ Finset.range h, (l j)^2) := by
  let f : Fin (h+1) → ℝ := Fin.cases r (fun j => l j)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (h+1) => (1:ℝ)) f
  have he : (∑ j : Fin h, (l j)^2) = ∑ j ∈ Finset.range h, (l j)^2 :=
    Fin.sum_univ_eq_sum_range (fun j => (l j)^2) h
  simpa [f,Fin.sum_univ_succ,Fin.sum_univ_eq_sum_range,he] using hh



end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℕ → ℂ) (h d : ℕ) (ρ D : ℝ) (u a : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hd : d=h+1 ∨ (d=h ∧ ρ=0))
    (hm : ∑ i, (w i:ℂ)*z i h=u)
    (hb : ∀ i, ‖z i h-a‖ ≤ D)
    (he : (∑ i, w i*historyEnergy h (z i))=(∑ i, w i*‖z i h-u‖^2)-ρ^2) :
    ∃ i, ρ+(∑ k ∈ Finset.range h, ‖z i (k+1)-z i k‖)+‖z i h-u‖ ≤
      (1+Real.sqrt d)*Real.sqrt (D^2-‖u-a‖^2) := by
  let f : ι → ℝ := fun i => ρ+∑ k ∈ Finset.range h, ‖z i (k+1)-z i k‖
  let g : ι → ℝ := fun i => ‖z i h-u‖
  have hf (i : ι) : 0 ≤ f i := by dsimp [f]; positivity
  have hg (i : ι) : 0 ≤ g i := norm_nonneg _
  have hpoint (i : ι) : (f i)^2 ≤ (d:ℝ)*(ρ^2+historyEnergy h (z i)) := by
    rcases hd with hd|⟨hd,hzero⟩
    · subst d
      simpa only [f,historyEnergy,Nat.cast_add,Nat.cast_one] using
        compressed_prefix_cauchy h ρ (fun k => ‖z i (k+1)-z i k‖)
    · subst d
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range h) (fun _ => (1:ℝ))
        (fun k => ‖z i (k+1)-z i k‖)
      simpa [f,hzero,historyEnergy] using hh
  have hfg : (∑ i, w i*(f i)^2) ≤ (d:ℝ)*(∑ i, w i*(g i)^2) := by
    calc
      _ ≤ ∑ i, w i*((d:ℝ)*(ρ^2+historyEnergy h (z i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i)
      _ = (d:ℝ)*(ρ^2+(∑ i, w i*historyEnergy h (z i))) := by
        have hx (i : ι) : w i*((d:ℝ)*(ρ^2+historyEnergy h (z i))) =
            ((d:ℝ)*ρ^2)*w i+(d:ℝ)*(w i*historyEnergy h (z i)) := by ring
        simp only [hx,Finset.sum_add_distrib,← Finset.mul_sum,hs,mul_one]
        ring
      _ = _ := by rw [he]; dsimp [g]; ring
  have hvar := finite_weighted_variance w (fun i => z i h) u a hs hm
  have hbd : (∑ i, w i*‖z i h-a‖^2) ≤ D^2 := by
    calc
      _ ≤ ∑ i, w i*D^2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr (hb i)) (hw i)
      _ = _ := by rw [← Finset.sum_mul,hs,one_mul]
  have hV : (∑ i, w i*(g i)^2) ≤ D^2-‖u-a‖^2 := by dsimp [g]; linarith
  exact finite_return_cost_bound w f g d _ hw hs hf hg hfg hV
