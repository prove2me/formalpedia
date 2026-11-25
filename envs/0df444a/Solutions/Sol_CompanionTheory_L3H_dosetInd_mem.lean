-- Prove2me | solution 1 for CompanionTheory.L3H.dosetInd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:03:25.830586+00:00
-- url     : https://prove2.me/submissions/55209e90-7361-409f-8f33-349c0ce8b577

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Theorems.Thm_Formalism_UG_Final_DosetIndMem


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
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}
namespace CompanionTheory.L3H
theorem _root_.solution (s : SplitPlace L) (d : GL (Fin n) (s.v.adicCompletion L⁺)) : dosetInd ℂ (KL s n) d ∈ Hecke ℂ (KL s n) :=
  Final.DosetIndMem _ _ ℂ d
end CompanionTheory.L3H
