-- Prove2me | solution 1 for DiazModulus.intMatrix_ker_facts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:35.097983+00:00
-- url     : https://prove2.me/submissions/32caa554-524b-49f1-b5f4-2a9444bf1972

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # An integer matrix without rational kernel

Let `φ` be a `q × ι` integer matrix whose only rational kernel vector is `0`. The ℚ-linear map
`v ↦ φ v` from `ℚ^ι` to `ℚ^q` is injective, so it has a ℚ-linear left inverse `g`
(`LinearMap.exists_leftInverse_of_injective`). Its matrix `B` (with `B i k = g (e_k) i`) satisfies
`Σ_k B i k φ k j = δ_ij`, an identity between rationals that survives the cast to `ℂ`.
Hence for every complex `w`, `w i = Σ_k B i k (φ w)_k`. If `φ w = 0` this gives `w = 0`;
if `φ z = 2πi e` with `e` integral, it gives `z i = 2πi · Σ_k B i k e_k`, and
`v i = Σ_k B i k e_k` is rational. -/

namespace C14_S3
open DiazModulus

theorem exists_leftInv {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ)
    (hφ : ∀ v : ι → ℚ, (∀ k, ∑ i, (φ k i : ℚ) * v i = 0) → v = 0) :
    ∃ B : ι → Fin q → ℚ, ∀ w : ι → ℂ, ∀ i, ∑ k, (B i k : ℂ) * ∑ j, (φ k j : ℂ) * w j = w i := by
  classical
  let f : (ι → ℚ) →ₗ[ℚ] (Fin q → ℚ) :=
    { toFun := fun v k => ∑ i, (φ k i : ℚ) * v i
      map_add' := by intro v w; funext k; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v; funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl (fun _ _ => by ring) }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hφ v (fun k => congrFun hv k)
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hker
  refine ⟨fun i k => g (Pi.single k 1) i, ?_⟩
  have hδ : ∀ i j, ∑ k, g (Pi.single k 1) i * (φ k j : ℚ) = (Pi.single j (1 : ℚ) : ι → ℚ) i := by
    intro i j
    have h1 : g (f (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
    have h2 : f (Pi.single j 1) = ∑ k, (φ k j : ℚ) • (Pi.single k (1 : ℚ) : Fin q → ℚ) := by
      funext k'
      simp [f, Finset.sum_apply, Pi.single_apply]
    rw [← h1, h2, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  intro w i
  calc ∑ k, (g (Pi.single k 1) i : ℂ) * ∑ j, (φ k j : ℂ) * w j
      = ∑ j, ((∑ k, g (Pi.single k 1) i * (φ k j : ℚ) : ℚ) : ℂ) * w j := by
        simp only [Finset.mul_sum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    _ = w i := by
        simp only [hδ]
        simp [Pi.single_apply, apply_ite]

end C14_S3

open DiazModulus C14_S3 in
theorem solution {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ)
    (hφ : ∀ v : ι → ℚ, (∀ k, ∑ i, (φ k i : ℚ) * v i = 0) → v = 0) :
    (∀ v : ι → ℂ, (∀ k, ∑ i, (φ k i : ℂ) * v i = 0) → v = 0) ∧
    ∀ z : ι → ℂ, (∀ k, ∃ e : ℤ, ∑ i, (φ k i : ℂ) * z i = 2 * Real.pi * Complex.I * e) →
      ∃ v : ι → ℚ, ∀ i, z i = 2 * Real.pi * Complex.I * v i := by
  obtain ⟨B, hB⟩ := exists_leftInv φ hφ
  refine ⟨fun v hv => ?_, fun z hz => ?_⟩
  · funext i
    rw [← hB v i]
    simp [hv]
  · choose e he using hz
    refine ⟨fun i => ∑ k, B i k * e k, fun i => ?_⟩
    rw [← hB z i]
    simp only [he, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
