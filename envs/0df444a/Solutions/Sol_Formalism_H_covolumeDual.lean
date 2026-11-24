-- Prove2me | solution 1 for Formalism.H.covolumeDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:08.278816+00:00
-- url     : https://prove2.me/submissions/b54c2649-fd5d-482d-a126-1bcb05130f73

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_covolDual_det_mul
import Theorems.Thm_Formalism_H_covolDual_vol_fd
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_dualLattice_dual_span_eq
import Theorems.Thm_Formalism_H_exists_basis_span_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution : CovolumeDual V := by
  intro Λ _ _ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  subst he
  have h := covolDual_det_mul
    ((stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)) e
  set o := (stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)
  set eD := LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e with heD
  have hli : LinearIndependent ℤ e := e.linearIndependent.restrict_scalars' ℤ
  have hliD : LinearIndependent ℤ eD := eD.linearIndependent.restrict_scalars' ℤ
  have heq : Submodule.span ℤ (Set.range eD) = dual (Submodule.span ℤ (Set.range e)) :=
    (dualLattice_dual_span_eq e).symm
  have hb : ((↑) : Submodule.span ℤ (Set.range e) → V) ∘ Module.Basis.span hli = e :=
    funext fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  have hbD : ((↑) : dual (Submodule.span ℤ (Set.range e)) → V) ∘
      (Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq) = eD :=
    funext fun i => by simp [Module.Basis.span_apply]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume
      ((Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq)) o.toBasis,
    ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume (Module.Basis.span hli) o.toBasis, hb, hbD,
    covolDual_vol_fd, mul_one, mul_one, ← abs_inv]
  exact congrArg abs (eq_inv_of_mul_eq_one_left h)
end Formalism.H
