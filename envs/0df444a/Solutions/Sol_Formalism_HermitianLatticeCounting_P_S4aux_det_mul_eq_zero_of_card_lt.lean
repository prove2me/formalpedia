-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.det_mul_eq_zero_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.797327+00:00
-- url     : https://prove2.me/submissions/a342fcc4-ed4d-4217-b3b9-e00c5df1d4b4

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hlt : Fintype.card κ < Fintype.card ι) (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = 0 := by
  obtain ⟨e⟩ : Nonempty (κ ↪ ι) := Function.Embedding.nonempty_of_card_le hlt.le
  obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∉ Set.range e := by
    by_contra hcon
    push Not at hcon
    have : Function.Surjective e := hcon
    have := Fintype.card_le_of_surjective e this
    omega
  let P : Matrix κ ι R := (1 : Matrix ι ι R).submatrix e id
  have hPP : P * P.transpose = 1 := by
    ext j j'
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      e.injective.eq_iff]
  have h1 : A * B = (A * P) * (P.transpose * B) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
  rw [h1, Matrix.det_mul]
  have h2 : (A * P).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro i
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => hl0 ⟨j, h⟩), mul_zero]
  rw [h2, zero_mul]
end Formalism.HermitianLatticeCounting.P.S4aux
