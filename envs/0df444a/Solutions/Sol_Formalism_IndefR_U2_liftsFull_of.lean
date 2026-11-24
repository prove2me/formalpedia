-- Prove2me | solution 1 for Formalism.IndefR.U2.liftsFull_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:43.574806+00:00
-- url     : https://prove2.me/submissions/62120af9-08c6-4809-a198-87d0f43bfaa0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
import Theorems.Thm_Formalism_IndefR_U2_notLifted_le_ker
import Theorems.Thm_Formalism_IndefR_U2_range_adj_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
namespace Formalism.IndefR.U2
theorem _root_.solution (hD : OrthDecomp op good Ix) (hI : Intw θ op opB) (hG : GoodIn θ good goodB)
    (hA : IsAdj θ θa) (hO : OntoParts θa op opB good goodB Ix) : LiftsFull θ op opB good goodB Ix := by
  set L : Submodule ℂ A := ⨆ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good with hL
  set M : Submodule ℂ A := ⨆ c ∈ {c | c ∈ Ix ∧ c ∉ Lifted opB goodB Ix}, eigPart op c ⊓ good with hM
  have hMker : M ≤ LinearMap.ker θ := iSup₂_le fun c hc => notLifted_le_ker hI hG hc.1 hc.2
  have hgood : good ≤ L ⊔ M := by
    refine hD.span.trans (iSup₂_le fun c hc => ?_)
    by_cases h : c ∈ Lifted opB goodB Ix
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun c (_ : c ∈ Lifted opB goodB Ix) => eigPart op c ⊓ good) c h le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun c (_ : c ∈ {c | c ∈ Ix ∧ c ∉ Lifted opB goodB Ix}) => eigPart op c ⊓ good)
          c ⟨hc, h⟩ le_rfl)
  have hOrth : M ⟂ L := by
    rw [hM, Submodule.isOrtho_iSup_left]
    intro c
    rw [Submodule.isOrtho_iSup_left]
    intro hc
    rw [hL, Submodule.isOrtho_iSup_right]
    intro c'
    rw [Submodule.isOrtho_iSup_right]
    intro hc'
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    have hne : c ≠ c' := fun h => hc.2 (h ▸ hc')
    exact hD.orth c hc.1 c' hc'.1 hne u hu v hv
  apply le_antisymm
  · rintro x ⟨hxk, hxg⟩
    obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp (hgood hxg)
    have h1 : ⟪m, l + m⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hxk m (hMker hm)
    have h2 : ⟪m, l⟫_ℂ = 0 := Submodule.isOrtho_iff_inner_eq.mp hOrth m hm l hl
    have h3 : ⟪m, m⟫_ℂ = 0 := by rw [inner_add_right, h2, zero_add] at h1; exact h1
    rw [inner_self_eq_zero] at h3
    rw [h3, add_zero]
    exact hl
  · exact iSup₂_le fun c hc => le_inf ((hO c hc).trans (range_adj_le hA)) inf_le_right
end Formalism.IndefR.U2
