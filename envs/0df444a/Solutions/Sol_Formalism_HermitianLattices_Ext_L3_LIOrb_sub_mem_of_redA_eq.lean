-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.sub_mem_of_redA_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:18.831882+00:00
-- url     : https://prove2.me/submissions/49475a3a-4549-4056-8a5a-4b487804e09e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K))
    {a b : autSub h A} (e : redA I a = redA I b) {z : V} (hz : z ∈ A) :
    (b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z ∈ I • A := by
  have h1 := congrArg (fun φ => φ (Submodule.Quotient.mk (⟨z, hz⟩ : ↥A))) e
  simp only [redA, Submodule.mapQ_apply] at h1
  rw [eq_comm, Submodule.Quotient.eq] at h1
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
  simp only [Submodule.subtype_apply] at h2
  exact h2
end Formalism.HermitianLattices.Ext.L3.LIOrb
