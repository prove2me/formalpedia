-- Prove2me | solution 1 for Formalism.H.mFourier_torusProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:24.083972+00:00
-- url     : https://prove2.me/submissions/c8cbbaab-4f91-4e27-bb17-499f20dc051e

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.H
theorem _root_.solution (e : Module.Basis ι ℝ V) (m : ι → ℤ) (t : ι → ℝ) :
    UnitAddTorus.mFourier m (torusProj ι t) =
      Complex.exp (2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ)) := by
  have hinner : (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ) = ∑ i, (m i : ℝ) * t i := by
    rw [equivFunL_symm_eq, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, inner_dualVec_basis, mul_comm]
  rw [hinner]
  show (∏ i, fourier (m i) ((t i : ℝ) : UnitAddCircle)) = _
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring
end Formalism.H
