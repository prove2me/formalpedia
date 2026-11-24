-- Prove2me | solution 1 for Formalism.UG.P.nabla_subspace_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:28.267727+00:00
-- url     : https://prove2.me/submissions/d475bf38-4637-40a3-a75a-2c34633e8b68

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Theorems.Thm_Formalism_UG_P_linSubst_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.NablaStable := by
  intro O _ n _ _ k g P hP
  rw [nabla, mem_homogeneousSubmodule] at hP ⊢
  exact linSubst_isHomogeneous _ hP
end Formalism.UG.P
