-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.lamAf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:08.796902+00:00
-- url     : https://prove2.me/submissions/efe885e5-0980-4cb6-b63d-db1a5a3f39d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution {L₁ L₂ : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : L₁ ≤ L₂) :
    lamAf (F := I.F) L₁ ≤ lamAf (F := I.F) L₂ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x, h x.2⟩, rfl⟩
end Formalism.L2.SG.Pf.RedBasicsPf
