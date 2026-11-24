-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Frob.frob_mul_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:56:07.048171+00:00
-- url     : https://prove2.me/submissions/a52b1071-6825-4aef-a8d7-2b23181804c6

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Frob
namespace Formalism.FrobeniusOrbits.Frob
theorem _root_.solution {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] (Q : Ideal S) (ρ τ : G) (hρ : ρ ∈ Q.inertia G)
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ (ρ * τ) Q := by
  intro x
  have h1 : ρ • (τ • x) - τ • x ∈ Q := hρ (τ • x)
  have h2 := hτ x
  try simp only [MulSemiringAction.toAlgHom_apply] at h2 ⊢
  rw [mul_smul]
  have h3 := Q.add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3
end Formalism.FrobeniusOrbits.Frob
