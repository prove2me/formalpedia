-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.asd_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:57.988696+00:00
-- url     : https://prove2.me/submissions/b814c499-3e3c-4230-8c7c-6c8d42bb34e1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_finrank_cutW_lt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_orth_transfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_z_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_asd_base
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
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (z₁ z₂ : V) (φ : V ≃ₗ[K] V),
      finrank K W₁ ≤ n → IsASD S π h W₁ M z₁ → IsASD S π h W₂ N z₂ → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    exfalso
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    have := hM.le _ hM.z_mem
    rw [hbot, Submodule.mem_bot] at this
    exact hM.z_ne this
  | succ n ih =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    by_cases h1 : ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0
    · obtain ⟨ξ, hξ, hξ0, hzξ⟩ := h1
      obtain ⟨η, hη, hη0, hzη⟩ := exists_orth_transfer hd hφ' (fun v hv => (hW v).mp hv)
        (hM.le _ hM.z_mem) hM.z_ne (hN.le _ hN.z_mem) hN.z_ne hξ hξ0 hzξ
      obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0 hzξ
      obtain ⟨w₀, hw₀, hw₀u⟩ := hN.exists_unit_norm hS hπ hs hd hη hη0 hzη
      obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
        hw₀ hw₀u
      obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
        hXu.symm
      obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ _ _ φ'
        (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
        (hM.cut hS hπ hs hx hu) (hN.cut hS hπ hs hX (by rw [hXu]; exact hu)) hφ'i hφ'W
      have hgx : g x = X := by
        rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
      refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
      rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]
    · refine asd_base hS hπ hs hM hN hφ hW h1 ?_
      rintro ⟨η, hη, hη0, hzη⟩
      apply h1
      have hsym : ∀ a b, h (φ.symm a) (φ.symm b) = h a b := by
        intro a b
        rw [← hφ', φ.apply_symm_apply, φ.apply_symm_apply]
      exact exists_orth_transfer hd hsym
        (fun v hv => by rw [hW, φ.apply_symm_apply]; exact hv)
        (hN.le _ hN.z_mem) hN.z_ne (hM.le _ hM.z_mem) hM.z_ne hη hη0 hzη
end Formalism.HermitianLattices.Ext.L3.U0
