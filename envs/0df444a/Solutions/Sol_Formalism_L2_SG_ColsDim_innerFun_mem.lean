-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.innerFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:51.99366+00:00
-- url     : https://prove2.me/submissions/4069ba09-2dcc-4a7c-8e0b-991bd318a9b5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ColsDim_conj_inv_norm_one
import Theorems.Thm_Formalism_L2_SG_ColsDim_inner_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG
open InnerProductSpace
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.SG.ColsDim
theorem _root_.solution (ιi : Γ →* Gi) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (φ : Sharp ℂ ιi ιf K π ψ) :
    (fun x => (innerₛₗ ℂ ((φ : Gf → V) x) : Dual ℂ V)) ∈ Equi ℂ ιf K (dualRep ιi π) ψ := by
  have hφ := (mem_Equi ιf K (π.comp ιi) ψ⁻¹ _).1 φ.2
  rw [mem_Equi]
  intro γ x κ
  ext ξ
  show inner ℂ ((φ : Gf → V) (ιf γ * x * κ)) ξ = (ψ κ : ℂ) * inner ℂ ((φ : Gf → V) x) (π (ιi γ⁻¹) ξ)
  rw [hφ γ x κ, inner_smul_left, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    conj_inv_norm_one _ (hψ κ), MonoidHom.comp_apply, inner_unitary π hπ, ← map_inv ιi γ]
end Formalism.L2.SG.ColsDim
