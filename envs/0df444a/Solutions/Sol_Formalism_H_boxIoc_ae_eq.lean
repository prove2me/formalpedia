-- Prove2me | solution 1 for Formalism.H.boxIoc_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:08.022935+00:00
-- url     : https://prove2.me/submissions/2ceb77a0-37b4-447c-96e1-2004ac96337b

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.H
theorem _root_.solution :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ))
      =ᵐ[volume] boxIco ι := by
  have h1 : ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ)) =
      Set.univ.pi fun i => Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
    ext x
    simp [Set.mem_univ_pi]
  rw [h1]
  show _ =ᵐ[Measure.pi fun _ => volume] _
  exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
end Formalism.H
