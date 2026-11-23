-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:29.834437+00:00
-- url     : https://prove2.me/submissions/828c7ed6-fa89-42ac-b547-1cb8eb07458e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_herm_of_pos
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_aniso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open ConjugateWeightGram
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef)
    (Z : Submodule K (Fin n → K)) :
    ∃ e : Matrix (Fin n) (Fin n) K, e * e = e ∧ eᴴ * H = H * e ∧ (∀ x, e *ᵥ x ∈ Z) ∧
      ∀ z ∈ Z, e *ᵥ z = z := by
  have hHh : Hᴴ = H := herm_of_pos hv0 hpos
  obtain ⟨d, ⟨b⟩⟩ : ∃ d, Nonempty (Basis (Fin d) K Z) := ⟨_, ⟨Module.finBasis K Z⟩⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin d) K,
      ∀ c, B *ᵥ c = ∑ a, c a • (b a : Fin n → K) :=
    ⟨Matrix.of fun i a => (b a : Fin n → K) i, fun c => by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _⟩
  have hBZ : ∀ c, B *ᵥ c ∈ Z := fun c => by
    rw [hB]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (b a).2
  have hZB : ∀ z ∈ Z, ∃ c, B *ᵥ c = z := fun z hz => ⟨b.repr ⟨z, hz⟩, by
    rw [hB]
    calc ∑ a, b.repr ⟨z, hz⟩ a • (b a : Fin n → K)
        = ((∑ a, b.repr ⟨z, hz⟩ a • b a : Z) : Fin n → K) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = z := by rw [b.sum_repr]⟩
  have hli : LinearIndependent K (fun a => (b a : Fin n → K)) :=
    b.linearIndependent.map' Z.subtype (Submodule.ker_subtype Z)
  have hinj : ∀ c, B *ᵥ c = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.mp hli c (by rw [← hB]; exact hc))
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d) K, G = Bᴴ * H * B := ⟨_, rfl⟩
  have hquad : ∀ c, star c ⬝ᵥ G *ᵥ c = star (B *ᵥ c) ⬝ᵥ H *ᵥ (B *ᵥ c) := fun c => by
    rw [hG]
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hGdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    apply hinj
    apply aniso hv0 hpos
    rw [← hquad, hc]
    simp
  have hGi1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGdet
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  have R1 : ∀ X : Matrix (Fin d) (Fin n) K, Bᴴ * (H * (B * X)) = G * X := fun X => by
    rw [hG]
    simp only [Matrix.mul_assoc]
  have R0 : Bᴴ * (H * B) = G := by rw [hG, Matrix.mul_assoc]
  have R2 : ∀ X : Matrix (Fin d) (Fin n) K, G⁻¹ * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hGi1, Matrix.one_mul]
  refine ⟨B * (G⁻¹ * (Bᴴ * H)), ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, R1, R2]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, hGih,
      Matrix.mul_assoc]
  · intro x
    rw [← Matrix.mulVec_mulVec]
    exact hBZ _
  · intro z hz
    obtain ⟨c, rfl⟩ := hZB z hz
    rw [Matrix.mulVec_mulVec,
      show B * (G⁻¹ * (Bᴴ * H)) * B = B by simp only [Matrix.mul_assoc, R0, hGi1, Matrix.mul_one]]
end Formalism.DivisionValues.FinitelyNonzeroLinear
