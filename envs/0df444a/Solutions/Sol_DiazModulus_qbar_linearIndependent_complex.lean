-- Prove2me | solution 1 for DiazModulus.qbar_linearIndependent_complex
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:44.042075+00:00
-- url     : https://prove2.me/submissions/cb3b45b1-0945-47b0-8967-a0bf6ce899ba

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Q̄-free algebraic vectors are ℂ-free

Let `w₁, …, w_n` be vectors with algebraic coordinates, free over `Q̄`, and suppose `Σⱼ aⱼwⱼ = 0` with complex
`aⱼ` and some `aᵢ ≠ 0`. As `ℂ` is a free `Q̄`-vector space, there is a `Q̄`-linear form `φ : ℂ → Q̄` with
`φ(aᵢ) ≠ 0`. For each coordinate `l`, the numbers `w_{j,l}` are algebraic, so `φ` commutes with multiplication by
them: `Σⱼ φ(aⱼ)w_{j,l} = φ(Σⱼ aⱼw_{j,l}) = φ(0) = 0`. Hence `Σⱼ φ(aⱼ)wⱼ = 0` is a `Q̄`-relation among the `wⱼ`,
so every `φ(aⱼ)` vanishes, in particular `φ(aᵢ) = 0`: contradiction. -/

open DiazModulus in
theorem solution {n m : ℕ} (w : Fin n → Fin m → ℂ)
    (hw : ∀ a i, w a i ∈ Qbar) (hind : LinearIndependent (↥Qbar) w) :
    LinearIndependent ℂ w := by
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro a ha i
  by_contra hai
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (↥Qbar) hai
  refine hφ (hind (fun j => φ (a j)) ?_ i)
  funext l
  have hl := congr_fun ha l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl ⊢
  have key : ∀ j, (φ (a j) • w j l : ℂ) = ((φ ((⟨w j l, hw j l⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) := by
    intro j
    rw [map_smul, smul_eq_mul, Subfield.coe_mul, Subfield.smul_def, smul_eq_mul, mul_comm]
  simp only [key]
  have hsum : ∑ j, ((φ ((⟨w j l, hw j l⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) =
      ((φ (∑ j, (⟨w j l, hw j l⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) := by
    rw [map_sum]; exact (map_sum Qbar.subtype _ _).symm
  have : ∑ j, ((⟨w j l, hw j l⟩ : ↥Qbar) • a j) = ∑ j, a j * w j l := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  rw [hsum, this, hl, map_zero]
  rfl
