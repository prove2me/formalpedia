-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.Tr.rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:31.880512+00:00
-- url     : https://prove2.me/submissions/0945205e-30b2-4188-9902-a897e7e972cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_first_axis_injective
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_inj_y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}
namespace Formalism.IndefR.LatticeTransfer.Lat
namespace Tr
theorem _root_.solution [FiniteDimensional K V] (h : Tr p₀ p x y c) :
    finrank K (LinearMap.range p) = n * finrank K (LinearMap.range p₀) := by
  have hfix0 : ∀ a : LinearMap.range p₀, p₀ a = a := by
    rintro ⟨_, z, rfl⟩; exact h.1 z
  have hfix : ∀ a : LinearMap.range p, p a = a := by
    rintro ⟨_, z, rfl⟩; exact h.2.1 z
  have hpi : finrank K (Fin n → LinearMap.range p₀) = n * finrank K (LinearMap.range p₀) := by
    rw [Module.finrank_pi_fintype]; simp
  rw [← hpi]
  apply le_antisymm
  · let Y : LinearMap.range p →ₗ[K] (Fin n → LinearMap.range p₀) :=
      LinearMap.pi fun i => LinearMap.codRestrict _ (y i ∘ₗ (LinearMap.range p).subtype)
        fun a => ⟨_, h.2.2.2.1 i a (hfix a)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := Y) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply Subtype.ext
    refine h.inj_y a (hfix a) fun i => ?_
    exact congrArg Subtype.val (congrFun ha i)
  · let X : (Fin n → LinearMap.range p₀) →ₗ[K] LinearMap.range p :=
      LinearMap.codRestrict _ (∑ j, x j ∘ₗ (LinearMap.range p₀).subtype ∘ₗ LinearMap.proj j)
        fun a => by
          rw [LinearMap.sum_apply]
          exact Submodule.sum_mem _ fun j _ => ⟨_, h.2.2.1 j (a j) (hfix0 _)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := X) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := congrArg Subtype.val ha
    simp only [X, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.proj_apply, ZeroMemClass.coe_zero] at h1
    have h2 := h.first_axis_injective (fun j => (a j : V)) (fun j => hfix0 _) h1
    funext j
    exact Subtype.ext (congrFun h2 j)
end Tr
end Formalism.IndefR.LatticeTransfer.Lat
