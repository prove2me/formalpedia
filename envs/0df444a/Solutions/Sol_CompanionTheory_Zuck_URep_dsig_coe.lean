-- Prove2me | solution 1 for CompanionTheory.Zuck.URep.dsig_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:50.121788+00:00
-- url     : https://prove2.me/submissions/016c5550-a9dc-4b3d-a9a8-37ea49d3fc65

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (IsURepOn InLieHpk dsigW IsHCParam)
attribute [instance] FRep.fin FRep.dec
variable {k r : ℕ}
namespace CompanionTheory.Zuck
namespace URep
theorem _root_.solution (U : URep k r) {X : Mx k r} (hX : InLieHpk k r X) (v : U.R.smSub) :
    (U.dsig X v : U.R.H) = PI.UpqRep.dsig (k := k) (r := r) U.R.σ X v := by
  simp only [URep.dsig, dif_pos hX]; rfl
end URep
end CompanionTheory.Zuck
