-- Prove2me | solution 1 for Formalism.UG.P.adelic_stabilizer_finite_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:42.347156+00:00
-- url     : https://prove2.me/submissions/b7de710b-b8d7-4652-bb14-fd8e40ed9220

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Theorems.Thm_Formalism_UG_P_adelstabL_upper
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_adelstab_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.AdelicStabFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan g
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  exact adelstab_core σ J hτ hH hdet hdef _ (levelAfL σ J Λ) inf_le_right c₁ c₂ hc₁ hc₂ h₁ h₂ g
end Formalism.UG.P
