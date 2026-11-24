-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.equi_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:50.062548+00:00
-- url     : https://prove2.me/submissions/bf62f511-a7c7-4fb5-a616-a51aea85e224

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
namespace Formalism.L2.SG.ColsDim
theorem _root_.solution {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
    (Γ' : Subgroup Gf) (ρ : Representation k Γ' W) (χ : K →* kˣ) :
    Equi k Γ'.subtype K ρ χ = Formalism.L2.SG.ClassAct.AMFChi k Γ' K ρ χ := rfl
end Formalism.L2.SG.ColsDim
