-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.psi_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:56.469291+00:00
-- url     : https://prove2.me/submissions/606a093e-6f1b-4c44-85a2-b14e149e6559

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_isOpen_dom
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_isPreconnected_dom
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_hasDerivAt_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution (hP : IsogenyP) (hd : ZetaHasDeriv) (L : PeriodPair) (α : ℂ) (S : Finset ℂ)
    (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) {x y : ℂ}
    (hx : α * x ∉ L.lattice) (hy : α * y ∉ L.lattice) : psi L α S x = psi L α S y := by
  have hdiff : DifferentiableOn ℂ (psi L α S) (dom L α) := fun w hw =>
    (hasDerivAt_psi hP hd L α S hα hst hS w hw).differentiableAt.differentiableWithinAt
  have hder : Set.EqOn (deriv (psi L α S)) 0 (dom L α) := fun w hw =>
    (hasDerivAt_psi hP hd L α S hα hst hS w hw).deriv
  exact (isOpen_dom L α).is_const_of_deriv_eq_zero (isPreconnected_dom L α hα) hdiff hder hx hy
end Formalism.L2.Th1.F.S2IsogenyPsi
