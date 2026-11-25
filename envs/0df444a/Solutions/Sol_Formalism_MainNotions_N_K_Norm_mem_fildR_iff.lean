-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.mem_fildR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:10.645356+00:00
-- url     : https://prove2.me/submissions/d0353ce0-d667-4f07-81f3-756987e1e831

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_MainNotions_N_K_Norm_filV_map_tmul
import Theorems.Thm_Formalism_MainNotions_N_K_Norm_congr_symm_tmul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) x ∈ FildR PD ρ' τ a := by
  set E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) with hEd
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hM : ∀ c x, E (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c (E x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, mulVdR]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hF : x ∈ FilV PD (LL := LL) (V := V) a ↔ E x ∈ FilV PD (LL := LL) (V := V') a := by
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (filV_map_tmul PD e a y).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp _) y, ?_⟩
      rw [← filV_map_tmul PD e.symm a y, hy, hEd, congr_symm_tmul]
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
  refine and_congr (and_congr ⟨fun h g => ?_, fun h g => E.injective ?_⟩ ⟨fun h c => ?_, fun h c => E.injective ?_⟩) hF
  · rw [← hE, h g]
  · rw [hE]; exact h g
  · rw [← hM, h c, map_smul]
  · rw [hM, map_smul]; exact h c
end Formalism.MainNotions.N.K.Norm
