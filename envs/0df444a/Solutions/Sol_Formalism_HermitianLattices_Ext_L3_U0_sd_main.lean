-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.sd_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:59.401016+00:00
-- url     : https://prove2.me/submissions/af4faf47-0959-4502-94d9-a01c2f712855

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_finrank_cutW_lt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_exists_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_prep
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_iff_of_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_symm_zero


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
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    refine ⟨φ, hφ, fun _ _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have : v = 0 := by
        have := hM.le v hv
        rwa [hbot, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact N.zero_mem
    · have : v = 0 := by
        have := (hW v).mpr (hN.le _ hv)
        rwa [hbot, Submodule.mem_bot] at this
      rw [this]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    by_cases hbot : W₁ = ⊥
    · exact ih W₁ W₂ M N φ (by rw [hbot]; simp) hM hN hφ hW
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
    obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
      hXu.symm
    obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ φ'
      (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
      (hM.cut hx hu) (hN.cut hX (by rw [hXu]; exact hu)) hφ'i hφ'W
    have hgx : g x = X := by
      rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
    refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
    rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]
end Formalism.HermitianLattices.Ext.L3.U0
