-- Prove2me | solution 1 for Formalism.L2.SG.ClassAct.diaFree_of_isNeat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:39.627028+00:00
-- url     : https://prove2.me/submissions/1f34a349-9220-4749-a625-ff9b0d848691

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
theorem _root_.solution {Γ K K₀ D : Subgroup G} (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) :
    DiaFree Γ K D := by
  intro x δ hδ h
  obtain ⟨γ, hγ, κ, hκ, hx⟩ := (DoubleCoset.eq Γ K (x * δ) x).mp h

  have hst : (⟨γ⁻¹, Γ.inv_mem hγ⟩ : Γ) ∈ stabAt Γ K₀ x := by
    show x⁻¹ * γ⁻¹ * x ∈ K₀
    have e : x⁻¹ * γ⁻¹ * x = δ * κ := by
      calc x⁻¹ * γ⁻¹ * x = x⁻¹ * γ⁻¹ * (γ * (x * δ) * κ) := by rw [← hx]
        _ = δ * κ := by group
    rw [e]
    exact K₀.mul_mem (hD hδ) (hK hκ)
  rw [hn x] at hst
  have hγ1 : γ = 1 := by
    have := congrArg Subtype.val (Set.mem_singleton_iff.mp hst)
    simpa using this
  subst hγ1
  have e2 : δ = κ⁻¹ := by
    have : x * 1 = x * (δ * κ) := by
      calc x * 1 = x := mul_one x
        _ = 1 * (x * δ) * κ := hx
        _ = x * (δ * κ) := by group
    have := (mul_left_cancel this).symm
    exact eq_inv_of_mul_eq_one_left this
  rw [e2]
  exact K.inv_mem hκ
end Formalism.L2.SG.ClassAct
