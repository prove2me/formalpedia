-- Prove2me | solution 1 for FairSelling.lemma11_utility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:55.321097+00:00
-- url     : https://prove2.me/submissions/47f6e16d-fc69-418b-9993-5c84e8a59e74

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_exists_limit_of_valid_seq
import Theorems.Thm_FairSelling_epsSEFXu_of_epsSEFX


set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXu v p o := by
  classical
  -- the `ε = 1/(k+1)` witnesses
  choose ω hval hshare henvy using fun k : ℕ => H (1 / (k + 1)) (by positivity)
  have hepspos : ∀ k : ℕ, (0:ℝ) ≤ 1 / (k + 1) := fun k => by positivity
  -- pass to the utility form of the envy condition
  have henvyu : ∀ k : ℕ, epsSEFXu v p (1 / (k + 1)) (ω k) := fun k =>
    epsSEFXu_of_epsSEFX (hepspos k) (hval k) (henvy k)
  obtain ⟨S, A, P, φ, hφ, hS, hA, htend⟩ := exists_limit_of_valid_seq (p := p) ω hval
  set q : ℕ → Fin n → ℝ := fun k => (ω (φ k)).money with hq
  have hqj : ∀ j, Tendsto (fun k => q k j) atTop (𝓝 (P j)) := fun j =>
    (tendsto_pi_nhds.1 htend) j
  set e : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with he
  have hetend : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  refine ⟨⟨S, A, P⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- sold goods are not kept
    intro j
    have := (hval (φ 0)).1 j
    rwa [hS 0, hA 0] at this
  · -- kept bundles are pairwise disjoint
    intro j k hjk
    have := (hval (φ 0)).2.1 j k hjk
    rwa [hA 0] at this
  · -- money is non-negative
    intro j
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hqj j)
      (fun k => (hval (φ k)).2.2.1 j)
  · -- the distributed money does not exceed the proceeds
    have hsum : Tendsto (fun k => ∑ j, q k j) atTop (𝓝 (∑ j, P j)) :=
      tendsto_finset_sum _ fun j _ => hqj j
    refine le_of_tendsto_of_tendsto' hsum tendsto_const_nhds fun k => ?_
    have := (hval (φ k)).2.2.2
    rwa [hS k] at this
  · -- the share guarantee, in the limit
    intro i
    have hlhs : Tendsto (fun k => (rho - e k) * s i) atTop (𝓝 (rho * s i)) := by
      have : Tendsto (fun k => rho - e k) atTop (𝓝 rho) := by
        simpa using tendsto_const_nhds.sub hetend
      simpa using this.mul_const (s i)
    have hrhs : Tendsto (fun k => (∑ g ∈ A i, v i g) + q k i) atTop
        (𝓝 ((∑ g ∈ A i, v i g) + P i)) := tendsto_const_nhds.add (hqj i)
    refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
    have := hshare (φ k) i
    rw [util, hA k] at this
    exact this
  · -- the envy condition, in the limit
    intro i j
    constructor
    · -- the envied agent holds money: plain envy-freeness
      intro hPj
      have hev : ∀ᶠ k in atTop, 0 < q k j := (hqj j).eventually_const_lt hPj
      have key : ∀ᶠ k in atTop,
          vbarSum (v i) p (A j) + q k j ≤ vbarSum (v i) p (A i) + q k i + e k := by
        filter_upwards [hev] with k hk
        have := (henvyu (φ k) i j).1 (by simpa [hq, hA k] using hk)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j) + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j) + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto hL hR key
      simpa using this
    · -- the up-to-any-good condition, in the limit
      intro g hg
      have key : ∀ k,
          vbarSum (v i) p (A j \ {g}) + p g + q k j
            ≤ vbarSum (v i) p (A i) + q k i + e k := by
        intro k
        have := (henvyu (φ k) i j).2 g (by simpa [hA k] using hg)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j \ {g}) + p g + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j \ {g}) + p g + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto' hL hR key
      simpa using this
end FairSelling
