-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:38.171166+00:00
-- url     : https://prove2.me/submissions/79652f39-fa6b-4436-8b11-11a341af4c45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_wLat0_eq

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
theorem _root_.solution (y : I.L) :
    (y : Fin I.n → I.E) ∈ wLat0 I w ↔ y ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by
  have e : wLat0 I w = (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)).map I.L.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, wLat0_eq]
  rw [e]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    rwa [← hzy']
  · intro h
    exact ⟨y, h, rfl⟩
end Formalism.L2.SG.Pf.RedBasicsPf
