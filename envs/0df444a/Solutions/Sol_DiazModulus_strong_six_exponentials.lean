-- Prove2me | solution 1 for DiazModulus.strong_six_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:08:23.821994+00:00
-- url     : https://prove2.me/submissions/c0ebddb1-4d13-408e-b5f8-04981ca7d407

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_exists_sse_lifts
import Theorems.Thm_DiazModulus_sse_setup
import Theorems.Thm_DiazModulus_sse_tangent_count
import Theorems.Thm_DiazModulus_sse_relRank_generic
import Theorems.Thm_DiazModulus_sse_relRank_rational
import Theorems.Thm_DiazModulus_linear_subgroup_transcendence

open Complex ComplexConjugate

/-! # Roy's strong six exponentials theorem, from the multiplicity estimate `hME`
Suppose `x_i y_j ∈ ℒ̃` for all `i, j`. `exists_sse_lifts` gives `m ≥ 1`, a ℚ-free algebraic `ω` and
lifts `η_{aj} ∈ Q̄² × ℒ^{2m}` with `Υ(η_{aj}) = ω_a y_j x`, where `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}`.
Apply `linear_subgroup_transcendence` (DALAG Th. 11.21) in `G = 𝔾ₐ² × 𝔾ₘ^{2m}` with
`V = Υ⁻¹(ℂx)` (dimension `2m+1` by `sse_setup`, so `d − n = 1`), the algebraic spanning family
`(−ω_k e_i, e_{(k,i)})` of `W = ker Υ` (`sse_setup`) and the lifts `η`. It returns `(V', φ, L₁, ℓ)`
with `ℓ < d′` and `(3m − ρ + d₁′)·1 ≤ 2m·(d′ − ℓ)`, `ρ` the relation rank. By `sse_tangent_count`,
`d′ − ℓ = δ = 2 − dim T` for `T = Υ(V' × L₁)`, so `δ ≥ 1`. If `T ≤ ℂx`, `sse_relRank_rational`
gives `L₁ = 0` and `ρ = 0`, so `5m ≤ 2mδ ≤ 4m`. Otherwise `T ≠ 0`, so `dim T = 1` and
`T ∩ ℂx = 0`; `sse_relRank_generic` gives `ρ ≤ 2m − dim L₁`, so `3m ≤ 2m`. Both contradict `m ≥ 1`. -/

namespace C14_S9
open DiazModulus

noncomputable def Ups (m : ℕ) (ω : Fin m → ℂ) :
    ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)

end C14_S9

open DiazModulus C14_S9 in
theorem solution (hME : DiazModulus.MultiplicityEstimateElem) :
    ∀ x : Fin 2 → ℂ, ∀ y : Fin 3 → ℂ, LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ LogAlgTilde := by
  intro x y hx hy hxy
  obtain ⟨m, ω, η, hm, hωQ, hωalg, hηalg, hηΥ⟩ := DiazModulus.exists_sse_lifts x y hxy
  have hx0 : x ≠ 0 := by
    intro h; exact hx.ne_zero 0 (by simp [h])
  obtain ⟨hdimV, hspan⟩ : Module.finrank ℂ ↥((ℂ ∙ x).comap (Ups m ω)) = 2 * m + 1 ∧
      Submodule.span ℂ (Set.range (fun p : Fin m × Fin 2 => ((fun i => if i = p.2 then -ω p.1 else 0),
        (fun q => if q = p then (1 : ℂ) else 0)))) = LinearMap.ker (Ups m ω) :=
    DiazModulus.sse_setup m ω x hx0
  have hηΥ' : ∀ p, Ups m ω (η p) = (ω p.1 * y p.2) • x := hηΥ
  have hcard2 : Fintype.card (Fin m × Fin 2) = 2 * m := by simp [Fintype.card_prod]; ring
  have hcard3 : Fintype.card (Fin m × Fin 3) = 3 * m := by simp [Fintype.card_prod]; ring
  have hc2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  obtain ⟨V', q, φ, L₁, ℓ, hL₁, hℓ, hℓlt, hineq⟩ :=
    DiazModulus.linear_subgroup_transcendence hME (κ₀ := Fin m × Fin 2) (κ₁ := Fin m × Fin 3)
      ((ℂ ∙ x).comap (Ups m ω)) (by rw [hdimV]; omega) (by rw [hdimV, hc2, hcard2]; omega)
      (by rw [hdimV, hc2]; omega)
      (fun p : Fin m × Fin 2 => ((fun i => if i = p.2 then -ω p.1 else 0),
        (fun q => if q = p then (1 : ℂ) else 0)))
      (fun k => by
        rw [Submodule.mem_comap]
        have hk : Ups m ω ((fun i => if i = k.2 then -ω k.1 else 0),
            (fun q => if q = k then (1 : ℂ) else 0)) = 0 := by
          rw [← LinearMap.mem_ker, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩
        rw [hk]; exact zero_mem _)
      (fun k => ⟨fun h => by dsimp only; split_ifs <;> simp [hωalg, zero_mem],
        fun i => by dsimp only; split_ifs <;> simp [one_mem, zero_mem]⟩)
      η (fun j => by
        rw [Submodule.mem_comap]
        exact (hηΥ' j).symm ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
      hηalg
  rw [hspan] at hℓ
  obtain ⟨_, hid, hVT⟩ := DiazModulus.sse_tangent_count m ω V' L₁ ℓ hℓ
  rw [hc2, hcard2, hcard3, hdimV] at hineq
  rw [hc2, hcard2] at hℓlt
  have hid' : ℓ + (2 - Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)))
      = (2 - Module.finrank ℂ ↥V') + (2 * m - Module.finrank ℂ ↥L₁) := hid
  have hT2 : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) ≤ 2 := by
    simpa using Submodule.finrank_le ((V'.prod L₁).map (Ups m ω))
  have hfac : 2 + 2 * m - (2 * m + 1) = 1 := by omega
  have hδ : 2 - Module.finrank ℂ ↥V' + (2 * m - Module.finrank ℂ ↥L₁) - ℓ
      = 2 - Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) := by omega
  rw [hfac, mul_one, hδ] at hineq
  have hTlt : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) < 2 := by omega
  by_cases hTx : (V'.prod L₁).map (Ups m ω) ≤ ℂ ∙ x
  · obtain ⟨hL0, hρ0⟩ := DiazModulus.sse_relRank_rational m ω hωQ hωalg x y hx hy η hηΥ
      (fun p i => (hηalg p).1 i) V' φ L₁ hL₁ hTx
    rw [hρ0] at hineq
    have hL0' : Module.finrank ℂ ↥L₁ = 0 := by rw [hL0, finrank_bot]
    rw [hL0'] at hineq
    have : 2 * m * (2 - Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω))) ≤ 2 * m * 2 :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  · have hT0 : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) ≠ 0 := fun h =>
      hTx (by rw [Submodule.finrank_eq_zero.mp h]; exact bot_le)
    have hT1 : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω)) = 1 := by omega
    have hgen : (V'.prod L₁).map (Ups m ω) ⊓ (ℂ ∙ x) = ⊥ := by
      by_contra hne
      apply hTx
      have h1 : Module.finrank ℂ ↥((V'.prod L₁).map (Ups m ω) ⊓ (ℂ ∙ x)) ≠ 0 := fun h =>
        hne (Submodule.finrank_eq_zero.mp h)
      have h2 := Submodule.finrank_mono (inf_le_left : (V'.prod L₁).map (Ups m ω) ⊓ (ℂ ∙ x) ≤ _)
      have h3 : (V'.prod L₁).map (Ups m ω) ⊓ (ℂ ∙ x) = (V'.prod L₁).map (Ups m ω) :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
      rw [← h3]; exact inf_le_right
    have hρ := DiazModulus.sse_relRank_generic m ω hωQ hωalg x y hx hy η hηΥ V' φ L₁ hL₁ hgen
    rw [hT1] at hineq
    omega
