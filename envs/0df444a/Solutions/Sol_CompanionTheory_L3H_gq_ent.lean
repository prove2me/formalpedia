-- Prove2me | solution 1 for CompanionTheory.L3H.gq_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:43.555002+00:00
-- url     : https://prove2.me/submissions/d8d43065-a9c1-42a5-a947-4f71ba24a2e1

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
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}
namespace CompanionTheory.L3H
theorem _root_.solution {γ : GA L n} (hγ : γ ∈ GQ L n) : ∃ γ₀ : GL (Fin n) L, (γ : GL (Fin n) (AL L)) =
    Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀ := by
  obtain ⟨γ₀, -, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨γ₀, e.symm⟩
end CompanionTheory.L3H
