-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_prep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:07.62332+00:00
-- url     : https://prove2.me/submissions/db9ee7db-0ca1-430d-bb98-8364e92d19a9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isom_move

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφh : ∀ a b, h (φ a) (φ b) = h a b := fun a b => hφ a b
  have hx' : φ x ∈ W₂ := (hW x).1 hx
  obtain ⟨τ, hτ, hτx, hτfix, hτW⟩ := exists_isom_move hs hd (x := φ x) (y := X) (by rw [hφh, hxX])
  have hτh : ∀ a b, h (τ a) (τ b) = h a b := fun a b => hτ a b
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, fun v => ?_, fun v hv => ?_⟩
  · change v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hx' hX (φ v), ← hW v, ← hτx, hτh, hφh]
  · change τ (φ v) = φ v
    apply hτfix
    · rw [hφh]; exact hv x hx
    · have hX' : φ.symm X ∈ W₁ := (hW _).2 (by rwa [LinearEquiv.apply_symm_apply])
      rw [← LinearEquiv.apply_symm_apply φ X, hφh]
      exact hv _ hX'
end Formalism.HermitianLattices.Ext.L3.U0
