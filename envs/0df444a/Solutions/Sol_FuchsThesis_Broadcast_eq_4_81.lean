-- Prove2me | solution 1 for FuchsThesis.Broadcast.eq_4_81
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T17:57:00.724047+00:00
-- url     : https://prove2.me/submissions/7eed2d86-683e-42b5-a4e1-33221d0b1849

import Theorems.Thm_FuchsThesis_Broadcast_eq_4_80
import Theorems.Thm_FuchsThesis_Broadcast_eq_4_58
import Theorems.Thm_FuchsThesis_Broadcast_fidelity_range
import Definitions.Def_FuchsThesis_Broadcast_IsClone
noncomputable section
open Matrix WildeQIT FuchsThesis.Broadcast
open scoped MatrixOrder ComplexOrder Kronecker
set_option autoImplicit false
namespace QuantumValueCloning
variable {n : Type} [Fintype n] [DecidableEq n]

lemma tensor_left (ρ : Matrix n n ℂ) (hρ : IsDensityOperator ρ) : partialTraceLeft (ρ ⊗ₖ ρ)=ρ := by
  ext i j
  simp only [partialTraceLeft,Matrix.of_apply,Matrix.kronecker_apply,← Finset.sum_mul]
  have ht : ∑ k, ρ k k=1 := hρ.2
  rw [ht,one_mul]

lemma tensor_right (ρ : Matrix n n ℂ) (hρ : IsDensityOperator ρ) : partialTraceRight (ρ ⊗ₖ ρ)=ρ := by
  ext i j
  simp only [partialTraceRight,Matrix.of_apply,Matrix.kronecker_apply,← Finset.mul_sum]
  have ht : ∑ k, ρ k k=1 := hρ.2
  rw [ht,mul_one]

lemma cloning (ρ0 ρ1 : Matrix n n ℂ) (hρ0 : IsDensityOperator ρ0) (hρ1 : IsDensityOperator ρ1)
    (hclone : IsClone ρ0 ρ1) :
    QAlgorithms.rootFidelity ρ0 ρ1=QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1) ∧
    QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1)=(QAlgorithms.rootFidelity ρ0 ρ1)^2 ∧
    (QAlgorithms.rootFidelity ρ0 ρ1=1 ∨ QAlgorithms.rootFidelity ρ0 ρ1=0) ∧
    (ρ0=ρ1 ∨ ρ0*ρ1=0) := by
  obtain ⟨k,Sig,Ups,U,hSig,hUps,hU,hout⟩ := hclone
  have hbc : ∀ ρ ∈ ({ρ0,ρ1} : Set (Matrix n n ℂ)),
      partialTraceLeft (ancillaProcess U Ups (ρ ⊗ₖ Sig))=ρ ∧
      partialTraceRight (ancillaProcess U Ups (ρ ⊗ₖ Sig))=ρ := by
    intro ρ hρ
    rw [hout ρ hρ]
    have hd : IsDensityOperator ρ := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hρ
      rcases hρ with rfl|rfl
      · exact hρ0
      · exact hρ1
    exact ⟨tensor_left ρ hd,tensor_right ρ hd⟩
  have he := FuchsThesis.Broadcast.eq_4_80 ρ0 ρ1 Sig Ups U hρ0 hρ1 hSig hUps hU hbc
  rw [hout ρ0 (by simp),hout ρ1 (by simp)] at he
  have hp := FuchsThesis.Broadcast.eq_4_58 ρ0 ρ1 ρ0 ρ1 hρ0.1 hρ1.1 hρ0.1 hρ1.1
  rw [← pow_two] at hp
  have hrange := FuchsThesis.Broadcast.fidelity_range ρ0 ρ1 hρ0 hρ1
  have hd : QAlgorithms.rootFidelity ρ0 ρ1=1 ∨ QAlgorithms.rootFidelity ρ0 ρ1=0 := by
    have hh : QAlgorithms.rootFidelity ρ0 ρ1*(QAlgorithms.rootFidelity ρ0 ρ1-1)=0 := by
      rw [hp] at he
      nlinarith
    rcases mul_eq_zero.mp hh with h|h
    · exact Or.inr h
    · exact Or.inl (sub_eq_zero.mp h)
  refine ⟨he.symm,hp,hd,?_⟩
  rcases hd with h|h
  · exact Or.inl (hrange.2.2.2.mp h)
  · exact Or.inr (hrange.2.2.1.mp h)
end QuantumValueCloning

end
open Matrix WildeQIT FuchsThesis.Broadcast
open scoped MatrixOrder ComplexOrder Kronecker

set_option autoImplicit false



/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.81), p.117 (PDF p.126): if `{ρ₀, ρ₁}` is clonable, then
`F(ρ₀, ρ₁) = F(ρ₀ ⊗ ρ₀, ρ₁ ⊗ ρ₁) = (F(ρ₀, ρ₁))²`, which means that `F(ρ₀, ρ₁) = 1` or `0`,
i.e., `ρ₀` and `ρ₁` are identical or orthogonal (`ρ₀ ρ₁ = 0`, (4.52)).

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56); `ρ ⊗ ρ` is the Kronecker
product indexed by `n × n`; clonability is `IsClone`. -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hclone : IsClone ρ0 ρ1) :
    QAlgorithms.rootFidelity ρ0 ρ1 = QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1) ∧
    QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1) = (QAlgorithms.rootFidelity ρ0 ρ1) ^ 2 ∧
    (QAlgorithms.rootFidelity ρ0 ρ1 = 1 ∨ QAlgorithms.rootFidelity ρ0 ρ1 = 0) ∧
    (ρ0 = ρ1 ∨ ρ0 * ρ1 = 0) := by
  exact QuantumValueCloning.cloning ρ0 ρ1 hρ0 hρ1 hclone