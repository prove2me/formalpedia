-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:39:16.58199+00:00
-- url     : https://prove2.me/submissions/01315411-1d2e-48ee-8e89-daed14a7a8a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_4_compl

open MeasureTheory Filter Topology
open ForkJoinCtrl.Tracking

theorem solution {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T)
    (C5 C6 C7 : ℝ) (hC5 : 0 < C5) (hC6 : 0 < C6) (hC7 : 0 < C7)
    (h37a : max (4 * N.lamBar) (2 * N.muBar) < C5)
    (h37b : (3 + 2 * ((N.J : ℝ) - 1) * (N.muBar / N.muMin)) * C6 < C7)
    (h37c : C7 < 0.5 * N.lamMin)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (i : Fin N.I) :
    Tendsto (fun r : ℕ => P (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n))
      atTop (𝓝 1) := by
  haveI := M.isProb
  have h := ForkJoinCtrl.Tracking.lemma_4_compl M hA1 hA2 run T hT C5 C6 C7 hC5 hC6 hC7
    h37a h37b h37c ε₂ hε₂ i
  set S : ℕ → Set Ω := fun r => ⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n
  -- `1 - P (S r)ᶜ ≤ P (S r) ≤ 1` by subadditivity of the outer measure
  have hlow : ∀ r, 1 - P (S r)ᶜ ≤ P (S r) := by
    intro r
    have : (1 : ENNReal) ≤ P (S r) + P (S r)ᶜ := by
      rw [← measure_univ (μ := P)]
      calc P Set.univ = P (S r ∪ (S r)ᶜ) := by rw [Set.union_compl_self]
        _ ≤ P (S r) + P (S r)ᶜ := measure_union_le _ _
    exact tsub_le_iff_right.2 this
  have hup : ∀ r, P (S r) ≤ 1 := fun r => prob_le_one
  have hl : Tendsto (fun r => 1 - P (S r)ᶜ) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) h
      (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
