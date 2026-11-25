-- Prove2me | solution 1 for CompanionTheory.L3H.integral_of_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:43.390577+00:00
-- url     : https://prove2.me/submissions/f35de85d-6077-4b18-a280-34bd2c54de0a

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable {R : Type} [CommRing R] [Algebra R ℂ]
namespace CompanionTheory.L3H
theorem _root_.solution [Module R W] [IsScalarTower R ℂ W] [IsNoetherianRing R] (N : Submodule R W) (hN : N ≠ ⊥)
    (hfg : N.FG) (ν : ℂ) (hν : ∀ w ∈ N, ν • w ∈ N) : IsIntegral R ν :=
  isIntegral_of_smul_mem_submodule N hN hfg ν hν
end CompanionTheory.L3H
