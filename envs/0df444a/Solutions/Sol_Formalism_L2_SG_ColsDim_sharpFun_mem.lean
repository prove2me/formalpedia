-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.sharpFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:53.366792+00:00
-- url     : https://prove2.me/submissions/528c03f5-ce6e-46e9-86d0-c347863c798d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ColsDim_conj_inv_norm_one
import Theorems.Thm_Formalism_L2_SG_ColsDim_inner_unitary
import Theorems.Thm_Formalism_L2_SG_ColsDim_inner_sharpFun

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
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (f : Equi ℂ ιf K (dualRep ιi π) ψ) :
    sharpFun (f : Gf → Dual ℂ V) ∈ Sharp ℂ ιi ιf K π ψ := by
  have hf := (mem_Equi ιf K (dualRep ιi π) ψ _).1 f.2
  show _ ∈ Equi ℂ ιf K (π.comp ιi) ψ⁻¹
  rw [mem_Equi]
  intro γ x κ
  apply ext_inner_right ℂ
  intro ξ
  rw [inner_sharpFun, hf γ x κ, inner_smul_left, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    conj_inv_norm_one _ (hψ κ), MonoidHom.comp_apply, inner_unitary π hπ, inner_sharpFun, ← map_inv]
  rfl
end Formalism.L2.SG.ColsDim
