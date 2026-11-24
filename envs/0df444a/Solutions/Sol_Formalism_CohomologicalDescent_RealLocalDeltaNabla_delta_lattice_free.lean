-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.delta_lattice_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:11.541302+00:00
-- url     : https://prove2.me/submissions/4894a7e1-4046-49c8-92b8-80ebfe2bb5c9

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_weyl_int_module_free
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_flat_baseChange_injective
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_lattice_tensor
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : DeltaFree := by
  intro O _ _ _ r n hn ν hν
  have := weyl_int_module_free r n hn ν hν
  have htf : Module.IsTorsionFree ℤ O :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.injective_int (algebraMap ℤ O))
  have hfl : Module.Flat ℤ O := inferInstance
  have hinj := flat_baseChange_injective ℤ O _ (weyl ℤ r n hn ν)
  have e1 : (O ⊗[ℤ] ↥(weyl ℤ r n hn ν)) ≃ₗ[O] ↥((weyl ℤ r n hn ν).baseChange O) :=
    LinearEquiv.ofInjective _ hinj
  have e2 : ↥((weyl ℤ r n hn ν).baseChange O) ≃ₗ[O]
      ↥(((weyl ℤ r n hn ν).baseChange O).map (polyBC ℤ O r n).toLinearMap) :=
    (polyBC ℤ O r n).submoduleMap _
  rw [(lattice_tensor ℤ O r n hn ν).1] at e2
  have e3 : ↥(deltaIn O r n hn ν) ≃ₗ[O] ↥(weyl O r n hn ν) :=
    Submodule.comapSubtypeEquivOfLe (weylLeDual O r n hn ν hν)
  exact Module.Free.of_equiv ((e1.trans e2).trans e3.symm)
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
