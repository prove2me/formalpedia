-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.gram_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:16.72981+00:00
-- url     : https://prove2.me/submissions/04fa0e22-e499-455b-8605-8608e0258d6c

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hSD : SelfDual h) :
    IsUnit (Matrix.of fun i l : Module.Free.ChooseBasisIndex O abelian₂ =>
      h (Module.Free.chooseBasis O abelian₂ i) (Module.Free.chooseBasis O abelian₂ l)).det := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  have hw : ∀ i, ∃ w, ∀ x, b.coord i x = h x w := fun i => hSD.2 (b.coord i)
  choose w hw using hw
  let Pst : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l i => star (b.repr (w i) l)
  have hmul : (Matrix.of fun i l => h (b i) (b l)) * Pst = 1 := by
    ext j i
    rw [Matrix.mul_apply]
    have h1 : h (b j) (w i) = ∑ l, h (b j) (b l) * star (b.repr (w i) l) := by
      conv_lhs => rw [← b.sum_repr (w i), map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, mul_comm]
    have h3 : h (b j) (w i) = if j = i then 1 else 0 := by
      rw [← hw, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Matrix.of_apply, Pst]
    rw [← h1, h3, Matrix.one_apply]
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this
end Formalism.HermitianLatticeCounting.P.S4aux
