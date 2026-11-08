-- Prove2me | solution 1 for DupacovaWets.Consistency.epiConverges_inf_argmin
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:14:50.070939+00:00
-- url     : https://prove2.me/submissions/00ce6e82-17c1-42ad-918f-9c49cb12fcdd

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
open Filter Topology
open DupacovaWets.Consistency

theorem solution {n : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin n) → EReal)
    (g₀ : EuclideanSpace ℝ (Fin n) → EReal) (hg : EpiConverges g g₀) :
    limsup (fun k => ⨅ x, g k x) atTop ≤ ⨅ x, g₀ x ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n))
        (x : EuclideanSpace ℝ (Fin n)), (∀ k, xs k ∈ argminSet (g (φ k))) →
        Tendsto xs atTop (𝓝 x) →
        x ∈ argminSet g₀ ∧ Tendsto (fun k => ⨅ y, g (φ k) y) atTop (𝓝 (⨅ y, g₀ y))) ∧
    (∀ D : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded D → ∀ φ : ℕ → ℕ, StrictMono φ →
        (∀ k, (argminSet (g (φ k)) ∩ D).Nonempty) → ∃ x ∈ closure D, x ∈ argminSet g₀) := by
  classical
  -- part 1
  have h1 : limsup (fun k => ⨅ x, g k x) atTop ≤ ⨅ x, g₀ x := by
    refine le_iInf fun x => ?_
    obtain ⟨u, -, hu⟩ := (hg x).2
    refine le_trans ?_ hu
    exact limsup_le_limsup (Eventually.of_forall fun k => iInf_le _ _)
  -- part 2
  have h2 : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n))
        (x : EuclideanSpace ℝ (Fin n)), (∀ k, xs k ∈ argminSet (g (φ k))) →
        Tendsto xs atTop (𝓝 x) →
        x ∈ argminSet g₀ ∧ Tendsto (fun k => ⨅ y, g (φ k) y) atTop (𝓝 (⨅ y, g₀ y)) := by
    intro φ hφ xs x hxs hlim
    let u : ℕ → EuclideanSpace ℝ (Fin n) := fun j =>
      if h : ∃ k, φ k = j then xs h.choose else x
    have hu_phi : ∀ k, u (φ k) = xs k := by
      intro k
      have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
      simp only [u, dif_pos h]
      rw [hφ.injective h.choose_spec]
    have hu : Tendsto u atTop (𝓝 x) := by
      rw [tendsto_atTop_nhds] at hlim ⊢
      intro U hxU hU
      obtain ⟨N, hN⟩ := hlim U hxU hU
      refine ⟨φ N, fun j hj => ?_⟩
      by_cases h : ∃ k, φ k = j
      · simp only [u, dif_pos h]
        apply hN
        have := h.choose_spec
        by_contra hlt
        push_neg at hlt
        have : φ h.choose < φ N := hφ hlt
        omega
      · simp only [u, dif_neg h]; exact hxU
    have hmap : map φ atTop ≤ atTop := hφ.tendsto_atTop
    have hA : g₀ x ≤ liminf (fun k => ⨅ y, g (φ k) y) atTop := by
      refine le_trans ((hg x).1 u hu) ?_
      have e : (fun k => ⨅ y, g (φ k) y) = (fun j => g j (u j)) ∘ φ := by
        funext k; simp only [Function.comp, hu_phi]; exact (hxs k).symm
      rw [e]
      exact hφ.tendsto_atTop.liminf_le_liminf_comp
    have hB : limsup (fun k => ⨅ y, g (φ k) y) atTop ≤ ⨅ y, g₀ y := by
      refine le_trans ?_ h1
      exact hφ.tendsto_atTop.limsup_comp_le_limsup (u := fun k => ⨅ y, g k y)
    have hC : liminf (fun k => ⨅ y, g (φ k) y) atTop ≤ limsup (fun k => ⨅ y, g (φ k) y) atTop :=
      liminf_le_limsup
    have hD : (⨅ y, g₀ y) ≤ g₀ x := iInf_le _ _
    have heq1 : g₀ x = ⨅ y, g₀ y := le_antisymm (hA.trans (hC.trans hB)) hD
    refine ⟨heq1, ?_⟩
    apply tendsto_of_liminf_eq_limsup
    · exact le_antisymm (hC.trans hB) (heq1 ▸ hA)
    · exact le_antisymm hB (heq1 ▸ (hA.trans hC))
    · isBoundedDefault
    · isBoundedDefault
  refine ⟨h1, h2, ?_⟩
  intro D hD φ hφ hne
  choose xs hxs using hne
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded hD.closure
    (fun k => subset_closure (hxs k).2)
  refine ⟨x, closure_closure (s := D) ▸ hx, ?_⟩
  exact (h2 (φ ∘ ψ) (hφ.comp hψ) (xs ∘ ψ) x (fun k => (hxs (ψ k)).1) hlim).1
