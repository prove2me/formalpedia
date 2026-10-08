-- Prove2me | solution 1 for ConjugateConvex.Involution.biconjFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:31:29.667781+00:00
-- url     : https://prove2.me/submissions/06e7773e-551a-414b-ba09-4b97762a2bc8

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

set_option autoImplicit false

namespace EE7CAE6F

open ConjugateConvex.Involution

lemma linrep {n : ℕ} (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) (y : Fin n → ℝ) (t : ℝ) :
    L (y, t) = (∑ i, y i * L ((fun j => if i = j then (1:ℝ) else 0), 0)) + t * L (0, 1) := by
  have h1 : (y, t) = (y, (0:ℝ)) + t • ((0 : Fin n → ℝ), (1:ℝ)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h1, L.map_add, L.map_smul, smul_eq_mul]
  congr 1
  have := LinearMap.pi_apply_eq_sum_univ
    ((L.toLinearMap).comp (LinearMap.inl ℝ (Fin n → ℝ) ℝ)) y
  simpa [smul_eq_mul] using this

lemma key {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (hfl : LowerSemicontinuousOn f G) (x : Fin n → ℝ) (hx : x ∈ G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ξ ∈ conjDomain G f, f x - ε < ξ ⬝ᵥ x - conjFun G f ξ := by
  let S : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ G ∧ f p.1 ≤ p.2}
  have hSc : Convex ℝ S := hf.convex_epigraph
  have hp : ((x, f x - ε) : (Fin n → ℝ) × ℝ) ∉ closure S := by
    rw [mem_closure_iff_nhds]
    push Not
    have h1 := hfl x hx (f x - ε / 2) (by linarith)
    rw [Filter.Eventually, mem_nhdsWithin] at h1
    obtain ⟨U, hUo, hxU, hU⟩ := h1
    refine ⟨U ×ˢ Set.Iio (f x - ε / 2), ?_, ?_⟩
    · exact (hUo.prod isOpen_Iio).mem_nhds ⟨hxU, by simp only [Set.mem_Iio]; linarith⟩
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨y, t⟩ ⟨⟨hyU, hyt⟩, hyG, hft⟩
      have := hU ⟨hyU, hyG⟩
      simp only [Set.mem_Iio, Set.mem_ofPred_eq] at hyt this hft
      linarith
  obtain ⟨L, u, hLs, hLp⟩ := geometric_hahn_banach_closed_point hSc.closure isClosed_closure hp
  have hrep : ∀ y t, L (y, t) = y ⬝ᵥ (fun i => L ((fun j => if i = j then (1:ℝ) else 0), 0))
      + t * L ((0 : Fin n → ℝ), (1:ℝ)) := by
    intro y t; rw [linrep]; rfl
  set α := L ((0 : Fin n → ℝ), (1:ℝ)) with hα
  set c : Fin n → ℝ := fun i => L ((fun j => if i = j then (1:ℝ) else 0), 0) with hc
  have hxS : ((x, f x) : (Fin n → ℝ) × ℝ) ∈ closure S := subset_closure ⟨hx, le_rfl⟩
  have h1 := hLs _ hxS
  rw [hrep] at h1 hLp
  have hαneg : α < 0 := by nlinarith
  have hβ : 0 < -α := by linarith
  have hb : ∀ y ∈ G, y ⬝ᵥ ((1 / -α) • c) - f y ≤ u / -α := by
    intro y hy
    have h2 := hLs (y, f y) (subset_closure ⟨hy, le_rfl⟩)
    rw [hrep] at h2
    rw [dotProduct_smul, smul_eq_mul, le_div_iff₀ hβ]
    have : (1 / -α * (y ⬝ᵥ c) - f y) * -α = y ⬝ᵥ c + f y * α := by
      have hα0 : -α ≠ 0 := hβ.ne'
      rw [sub_mul, mul_comm (1 / -α), mul_assoc, one_div, inv_mul_cancel₀ hα0]
      ring
    rw [this]; exact h2.le
  have hdom : (1 / -α) • c ∈ conjDomain G f := by
    refine ⟨u / -α, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hb y hy
  have hphi : conjFun G f ((1 / -α) • c) ≤ u / -α :=
    csSup_le ⟨_, x, hx, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hb y hy)
  refine ⟨(1 / -α) • c, hdom, ?_⟩
  have h3 : f x - ε < x ⬝ᵥ ((1 / -α) • c) - u / -α := by
    rw [dotProduct_smul, smul_eq_mul]
    have : 1 / -α * (x ⬝ᵥ c) - u / -α = (x ⬝ᵥ c - u) / -α := by ring
    rw [this, lt_div_iff₀ hβ]
    nlinarith
  rw [dotProduct_comm]
  linarith

end EE7CAE6F

open ConjugateConvex.Involution in
theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) (hfl : LowerSemicontinuousOn f G) :
    ∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x := by
  intro x hx
  have hub : ∀ ξ ∈ conjDomain G f, ξ ⬝ᵥ x - conjFun G f ξ ≤ f x := by
    intro ξ hξ
    have : x ⬝ᵥ ξ - f x ≤ conjFun G f ξ := le_csSup hξ ⟨x, hx, rfl⟩
    rw [dotProduct_comm]; linarith
  have hbdd : BddAbove ((fun ξ => ξ ⬝ᵥ x - conjFun G f ξ) '' conjDomain G f) :=
    ⟨f x, by rintro _ ⟨ξ, hξ, rfl⟩; exact hub ξ hξ⟩
  obtain ⟨ξ0, hξ0, -⟩ := EE7CAE6F.key G f hf hfl x hx 1 one_pos
  change sSup ((fun ξ => ξ ⬝ᵥ x - conjFun G f ξ) '' conjDomain G f) = f x
  apply le_antisymm
  · exact csSup_le ⟨_, ξ0, hξ0, rfl⟩ (by rintro _ ⟨ξ, hξ, rfl⟩; exact hub ξ hξ)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨ξ, hξ, h⟩ := EE7CAE6F.key G f hf hfl x hx ε hε
    have := le_csSup hbdd ⟨ξ, hξ, rfl⟩
    simp only at this
    linarith
