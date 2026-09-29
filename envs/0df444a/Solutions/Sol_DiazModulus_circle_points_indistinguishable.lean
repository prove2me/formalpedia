-- Prove2me | solution 1 for DiazModulus.circle_points_indistinguishable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T04:58:29.579429+00:00
-- url     : https://prove2.me/submissions/ffb688bd-58e3-4391-9812-91cb907d2f02

import Mathlib
import Definitions.Def_Diaz_Closure
import Theorems.Thm_Diaz_exists_ringHom_of_transcendental

open ComplexConjugate

namespace P14Indist

/-- Two ring homomorphisms that agree on `K` and at `u` agree on `hull K u`
(the proof of the platform node `Diaz.eqOn_hull`). -/
theorem eqOn_hull {K : Subfield ℂ} {u : ℂ} (f g : ℂ →+* ℂ) (hK : ∀ z ∈ K, f z = g z)
    (hu : f u = g u) : ∀ z ∈ Diaz.hull K u, f z = g z := by
  intro z hz
  induction hz using Subfield.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact hK x hx
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hu
  | one => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | neg x _ hx => rw [map_neg, map_neg, hx]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem self_mem_hull (K : Subfield ℂ) (x : ℂ) : x ∈ Diaz.hull K x :=
  Subfield.subset_closure (Set.mem_union_right _ rfl)

theorem base_mem_hull (K : Subfield ℂ) (x : ℂ) {a : ℂ} (ha : a ∈ K) : a ∈ Diaz.hull K x :=
  Subfield.subset_closure (Set.mem_union_left _ ha)

/-- A transcendental element is nonzero. -/
theorem ne_zero_of_transcendental {K : Subfield ℂ} {u : ℂ} (hu : Transcendental (↥K) u) :
    u ≠ 0 := by
  rintro rfl
  exact hu isAlgebraic_zero

/-- A ring homomorphism fixing `K` and sending `u` to `t` maps `hull K u` into `hull K t`. -/
theorem map_mem_hull {K : Subfield ℂ} {u t : ℂ} (Φ : ℂ →+* ℂ) (hfix : ∀ a ∈ K, Φ a = a)
    (hΦu : Φ u = t) : ∀ z ∈ Diaz.hull K u, Φ z ∈ Diaz.hull K t := by
  have hle : Diaz.hull K u ≤ Subfield.comap Φ (Diaz.hull K t) := by
    show Subfield.closure ((K : Set ℂ) ∪ {u}) ≤ _
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · show Φ x ∈ Diaz.hull K t
      rw [hfix x hx]
      exact base_mem_hull K t hx
    · show Φ x ∈ Diaz.hull K t
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hΦu]
      exact self_mem_hull K t
  exact fun z hz => hle hz

/-- Matrix-coefficient transfer: a ring homomorphism fixing `K` pointwise commutes with
`wᵀ M v` for coefficient vectors over `K`, and detects its vanishing (it is injective). -/
theorem coeff_transfer_iff {K : Subfield ℂ} {m n : Type*} [Fintype m] [Fintype n]
    (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by
  have key : Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hK _ (hw i), hK _ (hv j)]
  constructor
  · intro h0
    rw [← key, h0, map_zero]
  · intro h0
    refine Φ.injective ?_
    rw [key, h0, map_zero]

end P14Indist

open P14Indist in
theorem solution (K : Subfield ℂ) (hKc : ∀ z ∈ K, conj z ∈ K)
    {u t : ℂ} (hρ : u * conj u ∈ K) (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t)
    (hut : t * conj t = u * conj u) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t ∧
      (∀ z ∈ Diaz.hull K u, Φ (conj z) = conj (Φ z)) ∧
      (∀ z ∈ Diaz.hull K u, Φ z ∈ Diaz.hull K t) ∧
      ∀ (p q : ℕ) (N : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
        (∀ i j, N i j ∈ Diaz.hull K u) → (∀ i, w i ∈ K) → (∀ j, v j ∈ K) →
          ((∑ i, ∑ j, w i * N i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (N i j) * v j) = 0) := by
  obtain ⟨Φ, hfix, hΦu⟩ := Diaz.exists_ringHom_of_transcendental hu ht
  have ht0 : t ≠ 0 := ne_zero_of_transcendental ht
  -- `Φ (conj u) = conj t`: apply `Φ` to `u * conj u ∈ K` and cancel `t`.
  have hconj_u : Φ (conj u) = conj t := by
    have h1 : Φ u * Φ (conj u) = u * conj u := by rw [← map_mul, hfix _ hρ]
    rw [hΦu, ← hut] at h1
    exact mul_left_cancel₀ ht0 h1
  -- `Φ ∘ conj` and `conj ∘ Φ` agree on `K` and at `u`, hence on `hull K u`.
  have hconj : ∀ z ∈ Diaz.hull K u, Φ (conj z) = conj (Φ z) := by
    have hK' : ∀ a ∈ K, (Φ.comp (starRingEnd ℂ)) a = ((starRingEnd ℂ).comp Φ) a := by
      intro a ha
      simp only [RingHom.comp_apply]
      rw [hfix _ (hKc a ha), hfix _ ha]
    have hu' : (Φ.comp (starRingEnd ℂ)) u = ((starRingEnd ℂ).comp Φ) u := by
      simp only [RingHom.comp_apply]
      rw [hconj_u, hΦu]
    intro z hz
    exact eqOn_hull _ _ hK' hu' z hz
  refine ⟨Φ, hfix, hΦu, hconj, map_mem_hull Φ hfix hΦu, ?_⟩
  intro p q N w v _ hw hv
  exact coeff_transfer_iff Φ hfix N w v hw hv

#print axioms solution
