-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.psiFin_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:39:46.070913+00:00
-- url     : https://prove2.me/submissions/c8a37b3c-4474-4c47-a2fb-a193eb635b3e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace Formalism.L2.SG.Pf.StdChar
theorem _root_.solution (a : F) :
    psiFin F (algebraMap F (Af F) a) = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ))) := by
  have h := (exists_psiF F).choose_spec.2 a
  unfold psiFin
  rw [h, ← AddCircle.coe_neg, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring
end Formalism.L2.SG.Pf.StdChar
