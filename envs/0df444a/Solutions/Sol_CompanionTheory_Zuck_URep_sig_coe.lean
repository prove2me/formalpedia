-- Prove2me | solution 1 for CompanionTheory.Zuck.URep.sig_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:33.456076+00:00
-- url     : https://prove2.me/submissions/0b3fe020-b4d3-478e-908d-91c0599265eb

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
theorem _root_.solution (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (v : U.R.smSub) :
    (U.sig g v : U.R.H) = U.R.σ g v := by
  simp only [URep.sig, dif_pos hg]; rfl
end URep
end CompanionTheory.Zuck
