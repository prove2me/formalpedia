-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:58:41.126269+00:00
-- url     : https://prove2.me/submissions/369b40c0-a80f-404e-93d5-ea87e88ef918

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- Two subsets of `W` with the same cardinality are related by a permutation fixing every point
outside `W`. -/
theorem solution {W s t : Finset Ω} (hs : s ⊆ W) (ht : t ⊆ W)
    (hst : s.card = t.card) : ∃ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, s.image σ = t := by
    classical
    have hcard : (W \ s).card = (W \ t).card := by
      rw [card_sdiff_of_subset hs, card_sdiff_of_subset ht, hst]
    let e₁ : {x // x ∈ s} ≃ {x // x ∈ t} :=
      Fintype.equivOfCardEq (by
        simpa only [Fintype.card_coe] using hst)
    let e₂ : {x // x ∈ W \ s} ≃ {x // x ∈ W \ t} :=
      Fintype.equivOfCardEq (by
        simpa only [Fintype.card_coe] using hcard)
    let f : Ω → Ω := fun x =>
      if hx : x ∈ s then
        (e₁ ⟨x, hx⟩ : Ω)
      else if hx : x ∈ W \ s then
        (e₂ ⟨x, hx⟩ : Ω)
      else x
    let g : Ω → Ω := fun x =>
      if hx : x ∈ t then
        (e₁.symm ⟨x, hx⟩ : Ω)
      else if hx : x ∈ W \ t then
        (e₂.symm ⟨x, hx⟩ : Ω)
      else x
    have hf_s : ∀ (x : Ω) (hx : x ∈ s),
        f x = (e₁ ⟨x, hx⟩ : Ω) := by
      intro x hx
      simp only [f, dif_pos hx]
    have hf_ws : ∀ (x : Ω) (hx : x ∈ W \ s),
        f x = (e₂ ⟨x, hx⟩ : Ω) := by
      intro x hx
      have hxs : x ∉ s := (Finset.mem_sdiff.mp hx).2
      simp only [f, dif_neg hxs, dif_pos hx]
    have hf_out : ∀ (x : Ω) (hx : x ∉ W), f x = x := by
      intro x hx
      have hxs : x ∉ s := fun h => hx (hs h)
      have hws : x ∉ W \ s := by
        intro h
        exact hx (Finset.mem_sdiff.mp h).1
      simp only [f, dif_neg hxs, dif_neg hws]
    have hg_t : ∀ (x : Ω) (hx : x ∈ t),
        g x = (e₁.symm ⟨x, hx⟩ : Ω) := by
      intro x hx
      simp only [g, dif_pos hx]
    have hg_wt : ∀ (x : Ω) (hx : x ∈ W \ t),
        g x = (e₂.symm ⟨x, hx⟩ : Ω) := by
      intro x hx
      have hxt : x ∉ t := (Finset.mem_sdiff.mp hx).2
      simp only [g, dif_neg hxt, dif_pos hx]
    have hg_out : ∀ (x : Ω) (hx : x ∉ W), g x = x := by
      intro x hx
      have hxt : x ∉ t := fun h => hx (ht h)
      have hwt : x ∉ W \ t := by
        intro h
        exact hx (Finset.mem_sdiff.mp h).1
      simp only [g, dif_neg hxt, dif_neg hwt]
    have hfg : ∀ x, g (f x) = x := by
      intro x
      by_cases hxs : x ∈ s
      · have hfx : f x = (e₁ ⟨x, hxs⟩ : Ω) := hf_s x hxs
        have he : (e₁ ⟨x, hxs⟩ : Ω) ∈ t :=
          (e₁ ⟨x, hxs⟩).property
        calc
          g (f x) = g (e₁ ⟨x, hxs⟩ : Ω) := congrArg g hfx
          _ = (e₁.symm (e₁ ⟨x, hxs⟩) : Ω) := by
            simpa using hg_t (e₁ ⟨x, hxs⟩ : Ω) he
          _ = x := by
            simp
      · by_cases hws : x ∈ W \ s
        · have hfx : f x = (e₂ ⟨x, hws⟩ : Ω) := hf_ws x hws
          have he : (e₂ ⟨x, hws⟩ : Ω) ∈ W \ t :=
            (e₂ ⟨x, hws⟩).property
          calc
            g (f x) = g (e₂ ⟨x, hws⟩ : Ω) := congrArg g hfx
            _ = (e₂.symm (e₂ ⟨x, hws⟩) : Ω) := by
              simpa using hg_wt (e₂ ⟨x, hws⟩ : Ω) he
            _ = x := by
              simp
        · have hxW : x ∉ W := by
            intro hx
            exact hws (Finset.mem_sdiff.mpr ⟨hx, hxs⟩)
          calc
            g (f x) = g x := congrArg g (hf_out x hxW)
            _ = x := hg_out x hxW
    have hgf : ∀ x, f (g x) = x := by
      intro x
      by_cases hxt : x ∈ t
      · have hgx : g x = (e₁.symm ⟨x, hxt⟩ : Ω) := hg_t x hxt
        have he : (e₁.symm ⟨x, hxt⟩ : Ω) ∈ s :=
          (e₁.symm ⟨x, hxt⟩).property
        calc
          f (g x) = f (e₁.symm ⟨x, hxt⟩ : Ω) := congrArg f hgx
          _ = (e₁ (e₁.symm ⟨x, hxt⟩) : Ω) := by
            simpa using hf_s (e₁.symm ⟨x, hxt⟩ : Ω) he
          _ = x := by
            simp
      · by_cases hwt : x ∈ W \ t
        · have hgx : g x = (e₂.symm ⟨x, hwt⟩ : Ω) := hg_wt x hwt
          have he : (e₂.symm ⟨x, hwt⟩ : Ω) ∈ W \ s :=
            (e₂.symm ⟨x, hwt⟩).property
          calc
            f (g x) = f (e₂.symm ⟨x, hwt⟩ : Ω) := congrArg f hgx
            _ = (e₂ (e₂.symm ⟨x, hwt⟩) : Ω) := by
              simpa using hf_ws (e₂.symm ⟨x, hwt⟩ : Ω) he
            _ = x := by
              simp
        · have hxW : x ∉ W := by
            intro hx
            exact hwt (Finset.mem_sdiff.mpr ⟨hx, hxt⟩)
          calc
            f (g x) = f x := congrArg f (hg_out x hxW)
            _ = x := hf_out x hxW
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        calc
          x = g (f x) := (hfg x).symm
          _ = g (f y) := congrArg g hxy
          _ = y := hfg y
      · intro y
        exact ⟨g y, hgf y⟩
    let σ : Equiv.Perm Ω := Equiv.ofBijective f hf
    refine ⟨σ, ?_, ?_⟩
    · simp only [FunctionalInequalities.Analysis.Tensor.fixingOutside, mem_filter, mem_univ, true_and]
      intro x hx
      change f x = x
      exact hf_out x hx
    · have hsub : s.image σ ⊆ t := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        change f y ∈ t
        rw [hf_s y hy]
        exact (e₁ ⟨y, hy⟩).property
      have hcard_image : (s.image σ).card = s.card := by
        rw [Finset.card_image_iff]
        intro a ha b hb hab
        exact σ.injective hab
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard_image, hst]
