-- Prove2me | solution 1 for Formalism.L2.SG.ClassAct.mem_FixAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:47.333607+00:00
-- url     : https://prove2.me/submissions/9bcf72ba-23b5-42b4-8cae-6a4899d8a341

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ClassAct
open Formalism.UG Module
variable {G : Type} [Group G]
namespace Formalism.L2.SG.ClassAct
theorem _root_.solution {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W] {Γ K : Subgroup G}
    {ρ : Representation k Γ W} {χ : K →* kˣ} {D : Subgroup G} {f : G → W} :
    f ∈ FixAt k Γ K ρ χ D ↔ f ∈ AMFChi k Γ K ρ χ ∧ ∀ δ ∈ D, ∀ g : G, f (g * δ) = f g := by
  unfold FixAt
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun δ hδ g => congrFun (h2 δ hδ) g⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun δ hδ => funext fun g => h2 δ hδ g⟩
end Formalism.L2.SG.ClassAct
