-- Prove2me | solution 1 for DiazModulus.fischler_prop_3_1_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:00:16.28628+00:00
-- url     : https://prove2.me/submissions/e7c34a02-db42-4b27-b06c-d89d796c67ac

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_theorem_2_1
import Theorems.Thm_DiazModulus_rational_common_kernel

open Complex ComplexConjugate

/-! # Fischler 2001, Proposition 3.1 in pencil form

Let `F₁, …, F_l` be algebraic `d × d` matrices, `Q̄`-free, with no non-zero algebraic `φ` such that `φᵀF_a = 0`
for all `a`, and let `x ∈ ℒ̃ᵈ` lie in no hyperplane defined over `Q̄`. The `d × l` matrix `M_x` with columns
`F_a x` has entries in `ℒ̃`, and `M_x b = (Σ_a b_a F_a) x`. If `b` is algebraic and `M_x b = 0`, each row of
`Σ_a b_a F_a` is an algebraic form vanishing at `x`, hence zero, so `Σ_a b_a F_a = 0` and `b = 0` by freeness.
If `φ` is algebraic and `φᵀM_x = 0`, the algebraic forms `φᵀF_a` vanish at `x`, hence are zero, so `φ = 0`.
Fischler's Theorem 2.1 then gives subspaces `S`, `T` defined over `Q̄`, of codimensions at least `1`, with
`M_x(S) ⊂ T`, and the integer `r₁` with the two inequalities. Write `T` as the common kernel of algebraic forms
`ψ_k`. For algebraic `s ∈ S`, `(Σ_a s_a F_a) x ∈ T`, so each algebraic form `ψ_kᵀ(Σ_a s_a F_a)` vanishes at `x`,
hence is zero: the whole image of `Σ_a s_a F_a` lies in `T`. Since `S` is spanned by its algebraic vectors and
`s ↦ Σ_a s_a F_a` is linear, this holds for every `s ∈ S`. -/

namespace RC10_G4
open DiazModulus

/-- The columns of `M_x` are the vectors `F a x`, so `M_x b = (Σ_a b_a F_a) x`. -/
theorem mulVec_eq {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (b : Fin l → ℂ) :
    (Matrix.of fun i a => ((F a).mulVec x) i).mulVec b = (∑ a, b a • F a).mulVec x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring

/-- An algebraic combination of algebraic matrices is algebraic. -/
theorem pencil_alg {d l : ℕ} {F : Fin l → Matrix (Fin d) (Fin d) ℂ} (hF : ∀ a i j, F a i j ∈ Qbar)
    {b : Fin l → ℂ} (hb : ∀ a, b a ∈ Qbar) (i j : Fin d) : (∑ a, b a • F a) i j ∈ Qbar := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Qbar.sum_mem fun a _ => Qbar.mul_mem (hb a) (hF a i j)

/-- `φᵀA` is algebraic for algebraic `φ` and `A`. -/
theorem vecMul_alg {d : ℕ} {φ : Fin d → ℂ} (hφ : ∀ i, φ i ∈ Qbar) {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i j, A i j ∈ Qbar) (j : Fin d) : Matrix.vecMul φ A j ∈ Qbar := by
  simp only [Matrix.vecMul, dotProduct]
  exact Qbar.sum_mem fun i _ => Qbar.mul_mem (hφ i) (hA i j)

/-- If `T` is the common kernel of algebraic forms, `x` lies in no hyperplane defined over `Q̄`, and an
algebraic matrix `A` sends `x` into `T`, then `A` sends every vector into `T`. -/
theorem image_le {d : ℕ} {x : Fin d → ℂ}
    (hhyp : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → φ ⬝ᵥ x = 0 → φ = 0)
    {ψ : Fin d → Fin d → ℂ} (hψ : ∀ i j, ψ i j ∈ Qbar) {T : Submodule ℂ (Fin d → ℂ)}
    (hT : ∀ v, v ∈ T ↔ ∀ i, ψ i ⬝ᵥ v = 0) {A : Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, A i j ∈ Qbar)
    (hAx : A.mulVec x ∈ T) (α : Fin d → ℂ) : A.mulVec α ∈ T := by
  rw [hT] at hAx ⊢
  intro k
  have h0 : Matrix.vecMul (ψ k) A = 0 :=
    hhyp _ (vecMul_alg (hψ k) hA) (by rw [← Matrix.dotProduct_mulVec]; exact hAx k)
  rw [Matrix.dotProduct_mulVec, h0, zero_dotProduct]

end RC10_G4

open DiazModulus RC10_G4 in
theorem solution {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (hinj : LinearIndependent (↥Qbar) F)
    (hfix : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → (∀ a, Matrix.vecMul φ (F a) = 0) → φ = 0)
    (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hhyp : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → φ ⬝ᵥ x = 0 → φ = 0)
    (hr : (d + l) * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d * l) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)) (r₁ : ℕ),
      1 ≤ l - Module.finrank ℂ ↥S ∧ 1 ≤ d - Module.finrank ℂ ↥T ∧
      (∀ s ∈ S, ∀ α : Fin d → ℂ, (∑ a, s a • F a).mulVec α ∈ T) ∧ 1 ≤ r₁ ∧
      r₁ * d < (Matrix.of fun i a => ((F a).mulVec x) i).rank * (d - Module.finrank ℂ ↥T) ∧
      (l - Module.finrank ℂ ↥S) * (d - Module.finrank ℂ ↥T) ≤
        r₁ * ((l - Module.finrank ℂ ↥S) + (d - Module.finrank ℂ ↥T)) := by
  have hM : ∀ i a, (Matrix.of fun i a => ((F a).mulVec x) i) i a ∈ LogAlgTilde := by
    intro i a
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := LogAlgTilde.smul_mem (⟨F a i j, hF a i j⟩ : ↥Qbar) (hx j)
    rwa [Subfield.smul_def, smul_eq_mul] at this
  have hker : ∀ b : Fin l → ℂ, (∀ j, b j ∈ Qbar) →
      (Matrix.of fun i a => ((F a).mulVec x) i).mulVec b = 0 → b = 0 := by
    intro b hb hMb
    rw [mulVec_eq] at hMb
    have hN : ∑ a, b a • F a = 0 := by
      ext i j
      exact congrFun (hhyp (fun j => (∑ a, b a • F a) i j) (pencil_alg hF hb i) (congrFun hMb i)) j
    have h0 := Fintype.linearIndependent_iff.1 hinj (fun a => ⟨b a, hb a⟩) (by
      rw [← hN]
      exact Finset.sum_congr rfl fun a _ => rfl)
    funext a
    exact congrArg Subtype.val (h0 a)
  have him : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) →
      Matrix.vecMul φ (Matrix.of fun i a => ((F a).mulVec x) i) = 0 → φ = 0 := by
    intro φ hφ hφM
    refine hfix φ hφ fun a => hhyp _ (vecMul_alg hφ (hF a)) ?_
    rw [← Matrix.dotProduct_mulVec]
    exact congrFun hφM a
  obtain ⟨S, T, r₁, hS, hT, hl, hd, hST, hr₁, h1, h2⟩ :=
    DiazModulus.fischler_theorem_2_1 _ hM hker him hr
  obtain ⟨ψ, hψ, hTψ⟩ := DiazModulus.rational_common_kernel T hT
  refine ⟨S, T, r₁, hl, hd, ?_, hr₁, h1, h2⟩
  intro s hs α
  rw [← hS] at hs
  induction hs using Submodule.span_induction generalizing α with
  | mem v hv =>
    have hv' := hST v hv.1
    rw [mulVec_eq] at hv'
    exact image_le hhyp hψ hTψ (pencil_alg hF hv.2) hv' α
  | zero => simp
  | add u v _ _ hu hv =>
    simpa only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Matrix.add_mulVec] using
      T.add_mem (hu α) (hv α)
  | smul c u _ hu =>
    have hc : ∑ a, (c • u) a • F a = c • ∑ a, u a • F a := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hc, Matrix.smul_mulVec]
    exact T.smul_mem c (hu α)
