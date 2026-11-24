-- Prove2me | solution 1 for FairSelling.ZeroPrice.exists_TPS_SEFX_of_prices_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:43.613877+00:00
-- url     : https://prove2.me/submissions/60d90af6-ea08-44c5-9cc4-5fc6205c8e23

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
import Theorems.Thm_FairSelling_ZeroPrice_GoodSt_empty
import Theorems.Thm_FairSelling_ZeroPrice_vbarSum_eq_bval
import Theorems.Thm_FairSelling_ZeroPrice_exists_better

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp0 : ∀ g, p g = 0) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  -- the legitimate states form a nonempty finite set
  set S : Finset (St G n) := Finset.univ.filter (fun s => GoodSt v p s) with hSdef
  have hSne : S.Nonempty :=
    ⟨((∅ : Finset (Fin n)), fun _ => (∅ : Finset G)), by
      simp [hSdef, GoodSt_empty v p]⟩
  -- first maximize the number of served agents
  obtain ⟨s₁, hs₁S, hmax₁⟩ := S.exists_max_image (fun s => s.1.card) hSne
  set S₂ : Finset (St G n) := S.filter (fun s => s.1.card = s₁.1.card) with hS₂def
  have hS₂ne : S₂.Nonempty := ⟨s₁, by simp [hS₂def, hs₁S]⟩
  -- then the total value
  obtain ⟨s, hsS₂, hmax₂⟩ :=
    S₂.exists_max_image (fun s => ∑ i, bval (v i) (s.2 i)) hS₂ne
  have hsS : s ∈ S := (Finset.mem_filter.mp hsS₂).1
  have hscard : s.1.card = s₁.1.card := (Finset.mem_filter.mp hsS₂).2
  have hsgood : GoodSt v p s := (Finset.mem_filter.mp hsS).2
  -- every agent is served
  have hfull : s.1 = Finset.univ := by
    by_contra hne
    obtain ⟨s', hgood', hbetter⟩ := exists_better v p hp0 hv hn s hsgood hne
    have hs'S : s' ∈ S := by simp [hSdef, hgood']
    rcases hbetter with hcard | ⟨hcard, hval⟩
    · have := hmax₁ s' hs'S
      omega
    · have hs'S₂ : s' ∈ S₂ := by
        simp only [hS₂def, Finset.mem_filter]
        exact ⟨hs'S, by omega⟩
      exact absurd (hmax₂ s' hs'S₂) (not_le.mpr hval)
  -- the outcome
  refine ⟨⟨∅, s.2, fun _ => 0⟩, ⟨fun j => by simp, fun j k hjk => hsgood.2.1 j k hjk,
    fun j => le_rfl, by simp⟩, ?_, ?_⟩
  · intro i
    have hi : i ∈ s.1 := by rw [hfull]; exact Finset.mem_univ i
    have := hsgood.2.2.1 i hi
    simpa [util, thr, bval] using this
  · intro i j
    refine ⟨fun h => absurd h (by simp), fun _ => Or.inr (fun g hg => ?_)⟩
    have hj : j ∈ s.1 := by rw [hfull]; exact Finset.mem_univ j
    have hsafe := hsgood.2.2.2 j hj i g hg
    have hi : i ∈ s.1 := by rw [hfull]; exact Finset.mem_univ i
    have htheta : theta v p s i = bval (v i) (s.2 i) := by simp [theta, hi]
    rw [htheta] at hsafe
    have h1 : vbarSum (v i) p (s.2 i) = bval (v i) (s.2 i) :=
      vbarSum_eq_bval (v i) p hp0 (hv i) _
    have h2 : vbarSum (v i) p ((s.2 j) \ {g}) = bval (v i) ((s.2 j).erase g) := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact vbarSum_eq_bval (v i) p hp0 (hv i) _
    show vbarSum (v i) p (s.2 i) + 0 ≥ vbarSum (v i) p ((s.2 j) \ {g}) + p g
    rw [h1, h2, hp0 g]
    linarith
end FairSelling.ZeroPrice
