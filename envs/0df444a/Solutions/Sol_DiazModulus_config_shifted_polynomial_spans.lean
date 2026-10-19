-- Prove2me | solution 1 for DiazModulus.config_shifted_polynomial_spans
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:04:49.017965+00:00
-- url     : https://prove2.me/submissions/67eb9ac2-08b0-49c0-9dcd-1023f68df3b4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A configuration gives two polynomial spans with products in a shifted hull

Let `u ∉ Q̄`, `Hull` a `Q̄`-subspace of `Q̄[X]`, and `x ⊗ y` a `2 × 3` configuration with
`uᴺ xᵢ yⱼ = Qᵢⱼ(u)` for some `Qᵢⱼ ∈ Hull`. Take `aᵢ = Qᵢ₀`, `bⱼ = Q₀ⱼ` and `P₀ = Q₀₀`.

As `u` is transcendental over `Q̄`, evaluation at `u` is injective on `Q̄[X]`.
* `P₀ ≠ 0`: its value `uᴺ x₀ y₀` is non-zero, since `u ≠ 0` and free families have no zero entry.
* `a` is free: `aᵢ(u) = (uᴺ y₀) xᵢ`, a non-zero multiple of the free family `x`; likewise `b`.
* For `f = Σ cᵢ aᵢ` and `g = Σ dⱼ bⱼ` put `h = Σ cᵢ dⱼ Qᵢⱼ ∈ Hull`. At `u` both `f g` and `P₀ h`
  equal `u²ᴺ x₀ y₀ (Σ cᵢ xᵢ)(Σ dⱼ yⱼ)`, so `f g = P₀ h`.
-/

namespace R16_shiftedSpans

open DiazModulus Polynomial

/-- `u ∉ Q̄` is transcendental over `Q̄`. -/
theorem transcendental {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem li_congr {ι : Type*} {v w : ι → ℂ} (h : LinearIndependent (↥Qbar) v)
    (e : ∀ i, v i = w i) : LinearIndependent (↥Qbar) w := by
  rwa [funext e] at h

/-- A family of polynomials whose values at `u` are a non-zero multiple of a free family. -/
theorem li_of_eval {u : ℂ} {ι : Type*} {v : ι → ℂ} {F : ι → (↥Qbar)[X]}
    (hv : LinearIndependent (↥Qbar) v) {m : ℂ} (hm : m ≠ 0) (hF : ∀ i, aeval u (F i) = m * v i) :
    LinearIndependent (↥Qbar) F := by
  have h := hv.map' (LinearMap.mulLeft (↥Qbar) m)
    (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hm))
  refine LinearIndependent.of_comp (aeval u).toLinearMap (li_congr h fun i => ?_)
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hF, LinearMap.mulLeft_apply]

end R16_shiftedSpans

open DiazModulus R16_shiftedSpans Polynomial in
theorem solution {u : ℂ} (hu : u ∉ Qbar)
    (Hull : Submodule (↥Qbar) (↥Qbar)[X]) (N : ℕ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, ∃ Q ∈ Hull, aeval u Q = u ^ N * (x i * y j)) :
    ∃ (a : Fin 2 → (↥Qbar)[X]) (b : Fin 3 → (↥Qbar)[X]) (P₀ : (↥Qbar)[X]),
      LinearIndependent (↥Qbar) a ∧ LinearIndependent (↥Qbar) b ∧ P₀ ≠ 0 ∧
      ∀ f ∈ Submodule.span (↥Qbar) (Set.range a), ∀ g ∈ Submodule.span (↥Qbar) (Set.range b),
        ∃ h ∈ Hull, f * g = P₀ * h := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hinj : Function.Injective (aeval (R := ↥Qbar) u) :=
    transcendental_iff_injective.1 (transcendental hu)
  choose Q hQ hQe using hxy
  refine ⟨fun i => Q i 0, fun j => Q 0 j, Q 0 0, ?_, ?_, ?_, ?_⟩
  · exact li_of_eval hx (mul_ne_zero (pow_ne_zero _ hu0) (hy.ne_zero 0)) fun i => by
      rw [hQe]; ring
  · exact li_of_eval hy (mul_ne_zero (pow_ne_zero _ hu0) (hx.ne_zero 0)) fun j => by
      rw [hQe]; ring
  · intro h0
    have := hQe 0 0
    rw [h0, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hu0) (mul_ne_zero (hx.ne_zero 0) (hy.ne_zero 0)) this.symm
  · intro f hf g hg
    obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun (↥Qbar) |>.1 hf
    obtain ⟨d, rfl⟩ := Submodule.mem_span_range_iff_exists_fun (↥Qbar) |>.1 hg
    refine ⟨∑ i, ∑ j, (c i * d j) • Q i j,
      Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hQ i j),
      hinj ?_⟩
    simp only [map_mul, map_sum, map_smul, hQe]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Subfield.smul_def, Subfield.coe_mul]
    ring
