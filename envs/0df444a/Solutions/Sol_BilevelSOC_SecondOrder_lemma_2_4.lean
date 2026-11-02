-- Prove2me | solution 1 for BilevelSOC.SecondOrder.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:34:21.235384+00:00
-- url     : https://prove2.me/submissions/b84b801b-c01c-40ec-85c0-4226556603b4

import Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_2
open scoped Topology
open BilevelSOC.SecondOrder Filter Set

theorem solution {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [Nonempty ι]
    (θ : ι → V → ℝ) (θ' : ι → V → ℝ) (θ'' : ι → V → V → ℝ)
    (x : V) (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : ∀ i, LipschitzOnWith L (θ i) U)
    (hDiff : ∀ i, SecondOrderDirDiff (θ i) x (θ' i) (θ'' i))
    (hEpi : ∀ i, SecondOrderEpiRegular (θ i) x (θ' i) (θ'' i)) :
    ∀ (Θ' : V → ℝ) (Θ'' : V → V → ℝ),
      SecondOrderDirDiff (maxFn θ) x Θ' Θ'' →
      SecondOrderEpiRegular (maxFn θ) x Θ' Θ'' := by
  intro Θ' Θ'' hΘ
  obtain ⟨Θ'₀, Θ''₀, h0, _, hG''⟩ := lemma_2_2 θ θ' θ'' x U hU L hLip hDiff
  have e1 : ∀ d, Θ' d = Θ'₀ d := fun d => tendsto_nhds_unique (hΘ d).1 (h0 d).1
  have e2 : ∀ d v, Θ'' d v = Θ''₀ d v := fun d v => by
    have h1 := (hΘ d).2 v
    have h2 := (h0 d).2 v
    rw [e1 d] at h1
    exact tendsto_nhds_unique h1 h2
  intro d w hw ε hε
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i,
      θ i x + t * θ' i d + (t ^ 2 / 2) * θ'' i d (w t) - ε * t ^ 2 ≤
        θ i (x + t • d + (t ^ 2 / 2) • w t) :=
    Filter.eventually_all.2 fun i => hEpi i d w hw ε hε
  filter_upwards [hall] with t ht
  obtain ⟨i, hix, hid, hiv⟩ := (hG'' d (w t)).1
  rw [e1 d, e2 d (w t), ← hix, ← hid, hiv]
  exact (ht i).trans (Finset.le_sup' (fun j => θ j (x + t • d + (t ^ 2 / 2) • w t))
    (Finset.mem_univ i))
