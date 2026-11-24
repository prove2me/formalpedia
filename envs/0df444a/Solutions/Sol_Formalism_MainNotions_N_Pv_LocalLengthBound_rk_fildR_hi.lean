-- Prove2me | solution 1 for Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:58.44447+00:00
-- url     : https://prove2.me/submissions/a68090eb-118f-4b87-9914-fa7ce023633b

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientImageDivisibility_RkMultVOfNotJump
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_anti
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_sep
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_fildR_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.Pv Formalism.MainNotions.N.Pv.LocalLengthBound
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
variable (ρ : Representation LL G V)
namespace Formalism.MainNotions.N.Pv.LocalLengthBound
theorem _root_.solution (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ := by
  classical
  haveI hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℤ, ∀ a, finrank LL ↥(FildR PD ρ τ a0) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    have hS : (Set.range fun a : ℤ => finrank LL ↥(FildR PD ρ τ a)).Nonempty := ⟨_, 0, rfl⟩
    obtain ⟨a0, ha0⟩ := Nat.sInf_mem hS
    have ha0' : finrank LL ↥(FildR PD ρ τ a0) =
        sInf (Set.range fun a : ℤ => finrank LL ↥(FildR PD ρ τ a)) := ha0
    exact ⟨a0, fun a => by rw [ha0']; exact Nat.sInf_le ⟨a, rfl⟩⟩
  have hle : ∀ a, a0 ≤ a → finrank LL ↥(FildR PD ρ τ a) ≤ finrank LL ↥(FildR PD ρ τ a0) := by
    intro a ha
    first
    | exact Submodule.finrank_le_finrank_of_le (rk_fildR_anti PD ρ τ ha)
    | exact Submodule.finrank_mono (rk_fildR_anti PD ρ τ ha)
  have heq : ∀ a, a0 ≤ a → FildR PD ρ τ a = FildR PD ρ τ a0 := fun a ha =>
    Submodule.eq_of_le_of_finrank_eq (rk_fildR_anti PD ρ τ ha) (le_antisymm (hle a ha) (ha0 a))
  have hbot : FildR PD ρ τ a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine rk_filV_sep PD (LL := LL) (V := V) x fun b => ?_
    rcases le_total a0 b with hb | hb
    · rw [← heq b hb] at hx
      exact (Submodule.mem_inf.1 hx).2
    · exact rk_filV_anti PD hb (Submodule.mem_inf.1 hx).2
  exact ⟨a0, fun a ha => (heq a ha).trans hbot⟩
end Formalism.MainNotions.N.Pv.LocalLengthBound
