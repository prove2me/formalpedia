-- Prove2me | solution 2 for Erdos142.leng_sah_sawhney
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T08:52:10.067861+00:00
-- url     : https://prove2.me/submissions/7338a7d5-7f4f-4577-bc5a-695f0c740306
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_OAI_Erdos3_manuscriptQuantitativeDensityTheorem
import Theorems.Thm_Erdos142_apFree_iff

open Filter

namespace Erdos142LSS

/-- For `k ≥ 2`, `r k N` is at most OpenAI's `extremalNumber k N`. -/
theorem r_le_extremalNumber (k N : ℕ) (hk : 2 ≤ k) :
    Erdos142.r k N ≤ OAI.Erdos3.extremalNumber k N := by
  classical
  unfold Erdos142.r
  refine csSup_le ⟨0, ∅, by simp,
    by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) k, rfl⟩ ?_
  rintro m ⟨S, hS, hfree, rfl⟩
  have hap : Erdos142.APFree k S := (Erdos142.apFree_iff k hk S).2 hfree
  unfold OAI.Erdos3.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS, fun h => hap h⟩

/-- `L - c L^(1+η) → -∞`. -/
theorem tendsto_sub_rpow (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun L : ℝ => L - c * L ^ (1 + η)) atTop atBot := by
  have h1 : Tendsto (fun L : ℝ => c * L ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).const_mul_atTop hc
  have hev : ∀ᶠ L : ℝ in atTop, L - c * L ^ (1 + η) ≤ -L := by
    filter_upwards [h1.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)] with L h2 hL
    rw [Real.rpow_add hL, Real.rpow_one]
    nlinarith
  exact tendsto_atBot_mono' atTop hev tendsto_neg_atTop_atBot

end Erdos142LSS

namespace Erdos142

open Erdos142LSS in
theorem leng_sah_sawhney_aux (k : ℕ) (hk : 5 ≤ k) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop, (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log (Real.log N)) ^ c) := by
  obtain ⟨C, c, η, hC, hc, hη, hbound⟩ :=
    OAI.Erdos3.manuscriptQuantitativeDensityTheorem k (by omega)
  refine ⟨1, one_pos, ?_⟩
  have hL : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev := ((tendsto_sub_rpow c η hc hη).comp hL).eventually_le_atBot (-Real.log C)
  filter_upwards [eventually_ge_atTop 3, hev] with N hN hle
  simp only [Function.comp] at hle
  set L := Real.log (Real.log N)
  have h1 := hbound N hN
  have h2 : (r k N : ℝ) ≤ OAI.Erdos3.extremalNumber k N := by
    exact_mod_cast r_le_extremalNumber k N (by omega)
  have h3 : C * Real.exp (-c * L ^ (1 + η)) ≤ Real.exp (-L) := by
    rw [← Real.exp_log hC, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  rw [Real.rpow_one]
  have hN0 : (0 : ℝ) ≤ N := by positivity
  calc (r k N : ℝ) ≤ C * N * Real.exp (-c * L ^ (1 + η)) := h2.trans h1
    _ = N * (C * Real.exp (-c * L ^ (1 + η))) := by ring
    _ ≤ N * Real.exp (-L) := mul_le_mul_of_nonneg_left h3 hN0

end Erdos142

open Erdos142 in
theorem solution (k : ℕ) (hk : 5 ≤ k) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop, (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log (Real.log N)) ^ c) :=
  Erdos142.leng_sah_sawhney_aux k hk
