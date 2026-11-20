-- Prove2me | solution 1 for FuchsThesis.Broadcast.eq_4_80
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-19T22:14:18.659724+00:00
-- url     : https://prove2.me/submissions/2eba83b0-2016-4089-8ef5-41bc0c5899a1

import Theorems.Thm_FuchsThesis_Broadcast_eq_4_76
import Theorems.Thm_FuchsThesis_Broadcast_eq_4_79
import Definitions.Def_FuchsThesis_Broadcast_ancillaProcess
noncomputable section
open Matrix WildeQIT FuchsThesis.Broadcast
open scoped MatrixOrder ComplexOrder Kronecker
set_option autoImplicit false
namespace QuantumValueBroadcast
variable {n : Type} [Fintype n] [DecidableEq n]

lemma process_positive {m : Type} [Fintype m] [DecidableEq m] {k : ℕ}
    (X : Matrix m m ℂ) (hX : X.PosSemidef) (Υ : Matrix (Fin k) (Fin k) ℂ)
    (hΥ : Υ.PosSemidef) (U : Matrix (m×Fin k) (m×Fin k) ℂ) :
    (ancillaProcess U Υ X).PosSemidef := by
  let A := U*(X ⊗ₖ Υ)*Uᴴ
  have hA : A.PosSemidef := (hX.kronecker hΥ).mul_mul_conjTranspose_same U
  have he : ancillaProcess U Υ X=∑ j : Fin k, A.submatrix (fun i => (i,j)) (fun i => (i,j)) := by
    ext i j
    simp [ancillaProcess,partialTraceRight,A,Matrix.sum_apply,Matrix.submatrix_apply]
  rw [he]
  exact posSemidef_sum _ (fun j _ => hA.submatrix (fun i => (i,j)))

lemma preservation {k : ℕ} (ρ0 ρ1 Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n×n)×Fin k) ((n×n)×Fin k) ℂ)
    (hρ0 : IsDensityOperator ρ0) (hρ1 : IsDensityOperator ρ1)
    (hSig : IsDensityOperator Sig) (hUps : IsDensityOperator Ups)
    (hU : U ∈ Matrix.unitaryGroup ((n×n)×Fin k) ℂ)
    (hbc : ∀ ρ ∈ ({ρ0,ρ1} : Set (Matrix n n ℂ)),
      partialTraceLeft (ancillaProcess U Ups (ρ ⊗ₖ Sig))=ρ ∧
      partialTraceRight (ancillaProcess U Ups (ρ ⊗ₖ Sig))=ρ) :
    QAlgorithms.rootFidelity (ancillaProcess U Ups (ρ0 ⊗ₖ Sig))
      (ancillaProcess U Ups (ρ1 ⊗ₖ Sig))=QAlgorithms.rootFidelity ρ0 ρ1 := by
  have h0 := process_positive (ρ0 ⊗ₖ Sig) (hρ0.1.kronecker hSig.1) Ups hUps.1 U
  have h1 := process_positive (ρ1 ⊗ₖ Sig) (hρ1.1.kronecker hSig.1) Ups hUps.1 U
  have hu := FuchsThesis.Broadcast.eq_4_76 _ _ h0 h1
  rw [(hbc ρ0 (by simp)).1,(hbc ρ1 (by simp)).1] at hu
  exact le_antisymm hu (FuchsThesis.Broadcast.eq_4_79 ρ0 ρ1 Sig Ups U hρ0 hρ1 hSig hUps hU)
end QuantumValueBroadcast

end
open Matrix WildeQIT FuchsThesis.Broadcast
open scoped MatrixOrder ComplexOrder Kronecker




/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.80), p.117 (PDF p.126): the elementary constraint on
broadcasting. If a process `E` of the form (4.51) broadcasts `{ρ₀, ρ₁}`, i.e. `ρ̃ₛ = E(ρₛ ⊗ Σ)`
satisfies `tr_A ρ̃ₛ = ρₛ` and `tr_B ρ̃ₛ = ρₛ` for `s = 0, 1` (4.49), then
`F_A(ρ₀, ρ₁) = F(ρ̃₀, ρ̃₁) = F_B(ρ₀, ρ₁)`, where `F_A` and `F_B` are both the fidelity
`F(ρ₀, ρ₁)`; that is, `F(ρ̃₀, ρ̃₁) = F(ρ₀, ρ₁)`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56). `F_A(ρ₀, ρ₁)` and
`F_B(ρ₀, ρ₁)` are, in the source, `F(ρ₀, ρ₁)` written through an optimal POVM on `A` resp. `B`
("FA(ρ0, ρ1) denotes simply the fidelity F(ρ0, ρ1)", p.117), so both equalities of (4.80) are the
single equation `F(ρ̃₀, ρ̃₁) = F(ρ₀, ρ₁)`. Encoding as in `IsBroadcast`: `A`, `B` indexed by `n`,
`C` by `Fin k`, `tr_A`/`tr_B` the left/right partial traces, `E = ancillaProcess U Υ`. -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] {k : ℕ}
    (ρ0 ρ1 Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n × n) × Fin k) ((n × n) × Fin k) ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hSig : WildeQIT.IsDensityOperator Sig) (hUps : WildeQIT.IsDensityOperator Ups)
    (hU : U ∈ Matrix.unitaryGroup ((n × n) × Fin k) ℂ)
    (hbc : ∀ ρ ∈ ({ρ0, ρ1} : Set (Matrix n n ℂ)),
      WildeQIT.partialTraceLeft (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ ∧
      WildeQIT.partialTraceRight (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ) :
    QAlgorithms.rootFidelity (ancillaProcess U Ups (ρ0 ⊗ₖ Sig))
        (ancillaProcess U Ups (ρ1 ⊗ₖ Sig)) = QAlgorithms.rootFidelity ρ0 ρ1 := by
  exact QuantumValueBroadcast.preservation ρ0 ρ1 Sig Ups U hρ0 hρ1 hSig hUps hU hbc