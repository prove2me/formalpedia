-- Prove2me | solution 2 for EthierKurtz.oblique_dense_range
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T06:38:26.605948+00:00
-- url     : https://prove2.me/submissions/ed38becd-7256-4a20-8cd2-2acb61035ca6

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_oblique_dense_range_lt_one
import Theorems.Thm_EthierKurtz_oblique_graph_exponent_closure

/-! R0 reduction: EthierKurtz.oblique_dense_range from the exponent-below-one case
EthierKurtz.oblique_dense_range_lt_one (applied at exponent μ/2) and the graph inclusion
EthierKurtz.oblique_graph_exponent_closure (graph at μ/2 lies in the closure of the graph at μ).
All Hoelder hypotheses are monotone in the exponent (radii are capped at 1). -/

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace P50R0

open EthierKurtz

lemma compHolder_mono {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ μ' : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (h : ComponentHolder Ω μ f) (hle : μ' ≤ μ) :
    ComponentHolder Ω μ' f := by
  obtain ⟨hc, ρ₀, M, hρ₀, hM, hb⟩ := h
  refine ⟨hc, min ρ₀ 1, M, lt_min hρ₀ one_pos, hM, ?_⟩
  intro ρ hρ hρle x z hz y hy w hw
  have h1 := hb ρ hρ (hρle.trans (min_le_left _ _)) x z hz y hy w hw
  have h2 : ρ ^ μ ≤ ρ ^ μ' :=
    Real.rpow_le_rpow_of_exponent_ge hρ (hρle.trans (min_le_right _ _)) hle
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hM)

lemma ctwice_mono {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ μ' : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (h : CTwiceHolder Ω μ f) (hle : μ' ≤ μ) :
    CTwiceHolder Ω μ' f :=
  ⟨h.1, fun i j => compHolder_mono (h.2 i j) hle⟩

lemma conce_mono {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ μ' : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (h : COnceHolder Ω μ f) (hle : μ' ≤ μ) :
    COnceHolder Ω μ' f :=
  ⟨h.1, fun i => compHolder_mono (h.2 i) hle⟩

lemma bdry2_mono {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {μ μ' : ℝ}
    (h : BoundaryCTwiceHolder Ω μ) (hle : μ' ≤ μ) : BoundaryCTwiceHolder Ω μ' := by
  obtain ⟨ρ, hρ, hx⟩ := h
  refine ⟨ρ, hρ, fun x₀ hx₀ => ?_⟩
  obtain ⟨U, D, u, h1, h2, h3, h4⟩ := hx x₀ hx₀
  exact ⟨U, D, u, h1, h2, ctwice_mono h3 hle, h4⟩

lemma bdry1_mono {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {μ μ' : ℝ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (h : BoundaryCOnceHolder Ω μ φ) (hle : μ' ≤ μ) : BoundaryCOnceHolder Ω μ' φ := by
  intro x₀ hx₀
  obtain ⟨ρ, hρ, U, D, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h x₀ hx₀
  exact ⟨ρ, hρ, U, D, u, h1, h2, ctwice_mono h3 hle, h4, h5, h6, h7, conce_mono h8 hle⟩

end P50R0

open EthierKurtz P50R0 in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by
  have hμ2 : 0 < μ / 2 ∧ μ / 2 < 1 := ⟨by linarith [hμ.1], by linarith [hμ.2]⟩
  have hle : μ / 2 ≤ μ := by linarith [hμ.1]
  obtain ⟨lam₀, hlam, hden⟩ := EthierKurtz.oblique_dense_range_lt_one n hd Ω hbounded hconnected
    hopen (μ / 2) hμ2 (bdry2_mono hboundary hle) a b c normal ha
    (fun i j => compHolder_mono (haHolder i j) hle) (fun i => compHolder_mono (hbHolder i) hle)
    helliptic (fun i => bdry1_mono (hc i) hle) hnormal hoblique
  have hsub : closure (obliqueDiffusionGraph Ω (μ / 2) a b c) ⊆
      closure (obliqueDiffusionGraph Ω μ a b c) :=
    closure_minimal (EthierKurtz.oblique_graph_exponent_closure n Ω hbounded hopen μ hμ hboundary
      a b c normal haHolder hbHolder hc hnormal hoblique (μ / 2) ⟨hμ2.1, hle⟩) isClosed_closure
  refine ⟨lam₀, hlam, fun h delta hdelta => ?_⟩
  obtain ⟨fg, hfg, hlt⟩ := hden h delta hdelta
  exact ⟨fg, hsub hfg, hlt⟩
