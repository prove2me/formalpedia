-- Prove2me | solution 1 for DistQuantumQuery.Supplement.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:02:46.317208+00:00
-- url     : https://prove2.me/submissions/559146c6-8417-4b4c-8977-1a7edc1754b2

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_DistQuantumQuery_Supplement_schurChannel

open scoped Matrix ComplexOrder
namespace DistQuantumQuery.Supplement

theorem theorem_2_5 {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) :
    WildeQIT.EntBreaking.IsQuantumChannel (schurChannel G) := by
  refine ⟨?_, ?_⟩
  · intro r X hX
    have hM : (Gᵀ.submatrix (fun p : Fin r × n => p.2) (fun p : Fin r × n => p.2)).PosSemidef :=
      hG.transpose.submatrix _
    have heq : QAlgorithms.idTensorSuperop (R := Fin r) (schurChannel G) X =
        X ⊙ (Gᵀ.submatrix (fun p : Fin r × n => p.2) (fun p : Fin r × n => p.2)) := by
      ext p q
      simp [QAlgorithms.idTensorSuperop, schurChannel, Matrix.hadamard]
    rw [heq]
    exact hX.hadamard hM
  · intro X
    simp [schurChannel, Matrix.trace, Matrix.hadamard, hdiag]

end DistQuantumQuery.Supplement

open DistQuantumQuery.Supplement in
theorem solution {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) :
    WildeQIT.EntBreaking.IsQuantumChannel (schurChannel G) :=
  DistQuantumQuery.Supplement.theorem_2_5 G hG hdiag
