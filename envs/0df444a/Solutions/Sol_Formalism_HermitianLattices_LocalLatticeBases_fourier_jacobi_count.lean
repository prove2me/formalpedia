-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.fourier_jacobi_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.972802+00:00
-- url     : https://prove2.me/submissions/eac2053e-373b-4960-ac01-bc5b821d886d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
section Count
variable {F : Type} [Field F]
private lemma dot_product_dual_apply (m : ℕ) (a b : Fin m → F) : dotProductDual m a b = a ⬝ᵥ b := rfl
variable [Fintype F]
end Count
section FJ
variable {F : Type} [Field F] [Fintype F]
private lemma sum_char_linear_functional {M : Type} [AddCommGroup M] [Module F M] [Fintype M]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (L : M →ₗ[F] F) [Decidable (L = 0)] :
    ∑ x, ψ (L x) = if L = 0 then (Fintype.card M : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp
  · obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ
    obtain ⟨y, hy⟩ := LinearMap.surjective h a
    refine eq_zero_of_mul_eq_self_left ha ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => ?_)
    simp [hy, AddChar.map_add_eq_mul]
end FJ
section Onto
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
section FFOnto
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
end FFOnto
end Onto
end Formalism.HermitianLattices.LocalLatticeBases
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : CharacterSumCancellation := by
  classical
  intro F _ _ _ n g hg fL e he x' ψ hψ
  set q : ℂ := (Fintype.card F : ℂ) with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef]; exact_mod_cast Fintype.card_ne_zero

  let A : (Fin (n + g) → F) → Prop := fun fW =>
    (∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧ fW ⬝ᵥ x' (e, 0) = 1

  let Lf : (Fin (n + g) → F) → ((Fin n → F) →ₗ[F] F) := fun fW =>
    fL - (dotProductDual (n + g) fW) ∘ₗ x' ∘ₗ LinearMap.inl F (Fin n → F) F
  have hLf : ∀ fW e', Lf fW e' = fL e' - fW ⬝ᵥ x' (e', 0) := fun fW e' => rfl
  have hA : ∀ fW, Lf fW = 0 ↔ A fW := by
    intro fW
    constructor
    · intro h
      have h' : ∀ e', fW ⬝ᵥ x' (e', 0) = fL e' := fun e' => by
        have := LinearMap.congr_fun h e'
        rw [hLf] at this
        exact (sub_eq_zero.1 this).symm
      exact ⟨fun l hl => by rw [h']; exact hl, by rw [h', he]⟩
    · rintro ⟨h1, h2⟩
      apply LinearMap.ext
      intro v
      have hk : v - fL v • e ∈ LinearMap.ker fL := by simp [LinearMap.mem_ker, he]
      have h3 := h1 _ hk
      have hd : ((v, 0) : (Fin n → F) × F) = (v - fL v • e, 0) + fL v • (e, (0 : F)) := by
        ext <;> simp
      rw [hLf, hd, map_add, map_smul, dotProduct_add, dotProduct_smul, h3, h2]
      simp
  have hL : ∑ c : F, ψ c * (fjCount fL e x' c : ℂ) =
      ∑ fW : Fin (n + g) → F, if A fW then ψ (fW ⬝ᵥ x' (0, 1)) else 0 := by
    have hc : ∀ c : F, (fjCount fL e x' c : ℂ) =
        ∑ fW : Fin (n + g) → F, if A fW ∧ fW ⬝ᵥ x' (0, 1) = c then (1 : ℂ) else 0 := by
      intro c
      unfold fjCount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
      congr 2
      ext fW
      simp [A, and_assoc]
    simp only [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun fW _ => ?_)
    by_cases h : A fW
    · simp [h]
    · simp [h]
  have hind : ∀ y : Fin (n + g) → F,
      ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ y) = if y = 0 then q ^ (n + g) else 0 := by
    intro y
    have := sum_char_linear_functional ψ hψ ((dotProductDual (F := F) (n + g)).flip y)
    have h0 : (dotProductDual (F := F) (n + g)).flip y = 0 ↔ y = 0 := by
      constructor
      · intro h
        funext i
        have := LinearMap.congr_fun h (Pi.single i 1)
        simpa [dot_product_dual_apply] using this
      · rintro rfl; simp
    simp only [LinearMap.flip_apply, dot_product_dual_apply, h0] at this
    rw [this]
    simp [hqdef]
  have hinner : ∀ fW : Fin (n + g) → F,
      ∑ e' : Fin n → F, ψ (Lf fW e') = if A fW then q ^ n else 0 := by
    intro fW
    rw [sum_char_linear_functional ψ hψ (Lf fW)]
    simp [hA, hqdef]
  apply mul_left_cancel₀ (pow_ne_zero n hq0)
  rw [hL]
  calc q ^ n * ∑ fW : Fin (n + g) → F, (if A fW then ψ (fW ⬝ᵥ x' (0, 1)) else 0)
      = ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ x' (0, 1)) * ∑ e' : Fin n → F, ψ (Lf fW e') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun fW _ => ?_)
        rw [hinner]
        by_cases h : A fW
        · simp [h, mul_comm]
        · simp [h]
    _ = ∑ e' : Fin n → F, ψ (fL e') * ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ x' (-e', 1)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e' _ => Finset.sum_congr rfl (fun fW _ => ?_))
        have hd : ((-e', 1) : (Fin n → F) × F) = (0, 1) - (e', 0) := by
          ext <;> simp
        rw [hLf, hd, LinearMap.map_sub x', dotProduct_sub, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = q ^ n * (q ^ g * ∑ e' : Fin n → F, ψ (fL e') * (if x' (-e', 1) = 0 then 1 else 0)) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e' _ => ?_)
        rw [← Finset.mul_sum, hind]
        by_cases h : x' (-e', 1) = 0
        · simp [h, pow_add]; ring
        · simp [h]
end Formalism.HermitianLattices.LocalLatticeBases
