-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.aug_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:38.241841+00:00
-- url     : https://prove2.me/submissions/3d31ed4f-4280-4531-97e9-e12e7342eebd

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_augmentation_jet_variable
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_scale_jet_variable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) :
    (jetAug : Jet R κ m →ₐ[R] R) (sc m c p) = (jetAug : Jet R κ m →ₐ[R] R) p := by
  have h : (jetAug : Jet R κ m →ₐ[R] R).comp (sc m c) = jetAug := by
    apply jet_ext'
    intro j
    rw [AlgHom.comp_apply, scale_jet_variable, map_smul, augmentation_jet_variable, smul_zero]
  exact congrArg (fun g : Jet R κ m →ₐ[R] R => g p) h
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
