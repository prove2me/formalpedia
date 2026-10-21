-- Prove2me | solution 1 for DynFairDiv.Uniform.eq_E_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:07:05.05968+00:00
-- url     : https://prove2.me/submissions/3eb6ec84-1fc3-4139-ad07-c0175d9076e0

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model
import Theorems.Thm_DynFairDiv_Uniform_lemma_E_1

open DynFairDiv.Uniform Filter Topology

private lemma sum_flatMap_range (ℓ : ℕ) (f : ℕ → List ℝ) :
    ((List.range ℓ).flatMap f).sum = ∑ k ∈ Finset.range ℓ, (f k).sum := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [List.range_succ, List.flatMap_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

private lemma harm_diff (a b : ℕ) :
    ∑ k ∈ Finset.range b, (1 : ℝ) / ((a + k + 1 : ℕ) : ℝ) =
      (harmonic (a + b) : ℝ) - (harmonic a : ℝ) := by
  simp only [harmonic, Finset.sum_range_add]
  push_cast
  ring_nf

theorem solution (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) :
    Filter.Tendsto (fun ℓ : ℕ => ffaTotal (uniformCV d) σ (ℓ * (d + 1))) Filter.atTop
      (nhds (σ * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d))) := by
  have hform : ∀ ℓ : ℕ, ffaTotal (uniformCV d) σ (ℓ * (d + 1)) =
      σ * ((d : ℝ) + 1) * ((harmonic (ℓ * d + ℓ) : ℝ) - (harmonic (ℓ * d) : ℝ)) := by
    intro ℓ
    unfold ffaTotal
    have := lemma_E_1 d hd σ ℓ 0 (Nat.zero_le _)
    rw [Nat.add_zero] at this
    rw [this, List.replicate_zero, List.nil_append, sum_flatMap_range, ← harm_diff,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [List.sum_replicate, nsmul_eq_mul]
    push_cast
    ring
  simp_rw [hform]
  apply Tendsto.const_mul
  -- harmonic(ℓ(d+1)) - harmonic(ℓ d) → log((d+1)/d)
  have hA := Real.tendsto_harmonic_sub_log.comp
    (tendsto_id.atTop_mul_const' (show 0 < d + 1 by omega) |>.mono_right le_rfl)
  have hB := Real.tendsto_harmonic_sub_log.comp
    (tendsto_id.atTop_mul_const' (show 0 < d by omega) |>.mono_right le_rfl)
  have := hA.sub hB
  rw [sub_self] at this
  have h2 := this.add_const (Real.log (((d : ℝ) + 1) / d))
  rw [zero_add] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  simp only [Function.comp, id]
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : ((ℓ * (d + 1) : ℕ) : ℝ) = ((ℓ * d : ℕ) : ℝ) * (((d : ℝ) + 1) / d) := by
    push_cast; field_simp
  rw [e, Real.log_mul (by positivity) (by positivity), show ℓ * d + ℓ = ℓ * (d + 1) by ring]
  ring
