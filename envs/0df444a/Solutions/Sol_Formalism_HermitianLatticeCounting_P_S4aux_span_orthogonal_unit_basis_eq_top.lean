-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.span_orthogonal_unit_basis_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:38.665132+00:00
-- url     : https://prove2.me/submissions/a8e9f8d7-6524-4f83-9422-d8993e9cf753

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left
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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (v : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Submodule.span O (Set.range v) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  let M : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun i l => b.repr (v i) l
  let G : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l l' => h (b l) (b l')
  have hv : ∀ i, v i = ∑ l, M i l • b l := fun i => (b.sum_repr (v i)).symm
  have hD : M * G * M.conjTranspose = Matrix.diagonal fun i => h (v i) (v i) := by
    ext i i'
    have e1 : h (v i) (v i') = ∑ l', (∑ l, M i l * G l l') * star (M i' l') := by
      conv_lhs => rw [hv i, hv i']
      rw [orth_pair_gen]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [orth_pair_left, mul_comm]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← e1, Matrix.diagonal_apply]
    split_ifs with hii
    · rw [hii]
    · exact horth i i' hii
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (M * G * M.conjTranspose).det := by
      rw [hD, Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 hunit
    rw [Matrix.det_mul, Matrix.det_mul, mul_assoc] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have : b l = ∑ i, M⁻¹ l i • v i := by
    have e2 : ∑ i, M⁻¹ l i • v i = ∑ l', (M⁻¹ * M) l l' • b l' := by
      simp only [Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv i, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l' _ => by rw [smul_smul]
    rw [e2, Matrix.nonsing_inv_mul M hdet]
    simp [Matrix.one_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.HermitianLatticeCounting.P.S4aux
