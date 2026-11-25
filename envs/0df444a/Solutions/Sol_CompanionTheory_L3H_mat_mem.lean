-- Prove2me | solution 1 for CompanionTheory.L3H.mat_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:34.047354+00:00
-- url     : https://prove2.me/submissions/3ae97789-07bc-46bc-8b87-bbed0876b1c9

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl

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
namespace CompanionTheory.L3H
theorem _root_.solution {S : Subring (AL L)} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S)
    (i j : Fin n) : (A * B) i j ∈ S :=
  Matrix.mul_apply (M := A) (N := B) ▸ Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hA i a) (hB a j)
end CompanionTheory.L3H
