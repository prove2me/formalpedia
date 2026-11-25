-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.filt_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:31:56.193897+00:00
-- url     : https://prove2.me/submissions/304bd969-185d-4e02-a001-a405564f6c23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_mem_cj
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_relIndex_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (F : ℕ → Subgroup G) (hmono : ∀ k, F (k + 1) ≤ F k)
    (hcomm : ∀ k (g a : G), a ∈ F k → g * a * g⁻¹ * a⁻¹ ∈ F (k + 1)) (m : ℕ)
    (htop : F 0 = ⊤) (hbot : F m = ⊥) (X : Subgroup G) (g : G) :
    X.relIndex (cj g X) = (cj g X).relIndex X := by
  have hN : ∀ k, (F k).Normal := fun k => ⟨fun a ha g => by
    have h1 := (F k).mul_mem (hmono k (hcomm k g a ha)) ha
    rwa [show g * a * g⁻¹ * a⁻¹ * a = g * a * g⁻¹ by group] at h1⟩
  have hgr : ∀ k, X ⊓ F k ⊔ F (k + 1) = cj g X ⊓ F k ⊔ F (k + 1) := by
    intro k
    apply le_antisymm
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      intro x hx
      have hy : g * x * g⁻¹ ∈ cj g X ⊓ F k :=
        ⟨(mem_cj g X _).2 ⟨x, hx.1, rfl⟩, (hN k).conj_mem x hx.2 g⟩
      have hc := hcomm k g x hx.2
      rw [show x = (g * x * g⁻¹ * x⁻¹)⁻¹ * (g * x * g⁻¹) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((F (k + 1)).inv_mem hc))
        (Subgroup.mem_sup_left hy)
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      intro y hy
      obtain ⟨x, hxX, rfl⟩ := (mem_cj g X y).1 hy.1
      have hxk : x ∈ F k := by
        have := (hN k).conj_mem _ hy.2 g⁻¹
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      have hc := hcomm k g x hxk
      rw [show g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ⟨hxX, hxk⟩)
  have hX : ∀ k (Z : Subgroup G), Z ⊓ F k ⊓ F (k + 1) = Z ⊓ F (k + 1) := fun k Z => by
    rw [inf_assoc, inf_of_le_right (hmono k)]
  have main : ∀ j k, k + j = m →
      (X ⊓ cj g X ⊓ F k).relIndex (X ⊓ F k) = (X ⊓ cj g X ⊓ F k).relIndex (cj g X ⊓ F k) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      rw [hbot]
      simp only [inf_bot_eq]
    | succ j ih =>
      intro k hk
      have := hN (k + 1)
      have hle1 : X ⊓ cj g X ⊓ F k ≤ X ⊓ F k := inf_le_inf_right _ inf_le_left
      have hle2 : X ⊓ cj g X ⊓ F k ≤ cj g X ⊓ F k := inf_le_inf_right _ inf_le_right
      rw [relIndex_split (F (k + 1)) _ _ hle1, relIndex_split (F (k + 1)) _ _ hle2,
        hX k (X ⊓ cj g X), hX k X, hX k (cj g X), ih (k + 1) (by omega), hgr k]
  have h0 := main m 0 (by omega)
  rw [htop] at h0
  simp only [inf_top_eq] at h0
  rw [← Subgroup.inf_relIndex_right X (cj g X), ← Subgroup.inf_relIndex_left X (cj g X)]
  exact h0.symm
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
