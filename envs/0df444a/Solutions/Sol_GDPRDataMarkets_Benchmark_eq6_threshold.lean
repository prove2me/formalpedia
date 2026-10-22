-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.eq6_threshold
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:23:08.436098+00:00
-- url     : https://prove2.me/submissions/25fcfd0d-9b96-4cb2-b573-f0a0f17e2ad3

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) :
    (∀ (σ : Profile) (p1 v : ℝ), 0 ≤ v →
        σ.r v = (1 + P.mu - P.sigma) * v → σ.p2 p1 + P.c ≤ v →
        (U1wait P σ p1 v ≤ U1buy P σ p1 v ↔
          (p1 + P.c - P.d * σ.p2 p1) / (1 - P.d + P.d * P.sigma) ≤ v)) ∧
    (∀ p1 w q : ℝ, w = (p1 + P.c - P.d * q) / (1 - P.d + P.d * P.sigma) →
        q = (w - P.c) / 2 → w = vB P p1 ∧ q = qB P p1) := by
  obtain ⟨hL, hLH, hd0, hd1, hc0⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  have hμσ : P.sigma < P.mu := by unfold Params.mu Params.sigma; linarith
  have hmusig : P.mu - P.sigma = P.kL := by unfold Params.mu Params.sigma; ring
  have hkk : P.kH - P.kL = 2 * P.sigma := by unfold Params.sigma; ring
  have hden : 0 < 1 - P.d + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hD1 : 0 < 2 - P.d + 2 * P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  refine ⟨?_, ?_⟩
  · intro σ p1 v hv hr hw
    have hU : U1buy P σ p1 v = (1 + P.d * P.sigma) * v - p1 - (1 + P.d) * P.c := by
      unfold U1buy u2B
      rw [hr]
      have e0 : 1 + P.mu - P.sigma = 1 + P.kL := by linarith
      have e1 : (1 + P.kL) * v - (1 + P.mu - P.sigma) * v - P.c = -P.c := by
        rw [e0]; ring
      have e2 : (1 + P.kH) * v - (1 + P.mu - P.sigma) * v - P.c = 2 * P.sigma * v - P.c := by
        rw [e0]; nlinarith
      rw [e1, e2, max_self, max_eq_left (by nlinarith)]
      ring
    have hW : U1wait P σ p1 v = P.d * (v - σ.p2 p1 - P.c) := by
      unfold U1wait
      rw [max_eq_left (by linarith)]
    rw [hU, hW, div_le_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  · intro p1 w q hw hq
    have hw' : w * (1 - P.d + P.d * P.sigma) = p1 + P.c - P.d * q := by
      rw [hw]; field_simp
    constructor
    · unfold vB
      rw [eq_div_iff hD1.ne']
      rw [hq] at hw'
      nlinarith
    · unfold qB
      rw [eq_div_iff hD1.ne']
      rw [hq] at hw' ⊢
      nlinarith
