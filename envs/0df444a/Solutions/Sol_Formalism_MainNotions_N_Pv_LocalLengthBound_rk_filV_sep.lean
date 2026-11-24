-- Prove2me | solution 1 for Formalism.MainNotions.N.Pv.LocalLengthBound.rk_filV_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:39.084452+00:00
-- url     : https://prove2.me/submissions/ec02a6d5-920e-409e-a09b-2b3f7e6b8cd3

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientImageDivisibility_RkMultVOfNotJump

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
namespace Formalism.MainNotions.N.Pv.LocalLengthBound
theorem _root_.solution (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : V ⊗[Qp] BdR ≃ₗ[Qp] (Module.Free.ChooseBasisIndex Qp V →₀ BdR),
      ∀ (v : V) (y : BdR) (i), e (v ⊗ₜ y) i = (Module.Free.chooseBasis Qp V).repr v i • y := by
    first
    | exact ⟨TensorProduct.equivFinsuppOfBasisLeft (Module.Free.chooseBasis Qp V), fun v y i =>
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _⟩
    | exact ⟨TensorProduct.equivFinsuppOfBasisLeft (Module.Free.chooseBasis Qp V), fun v y i => by
        simp [TensorProduct.equivFinsuppOfBasisLeft]⟩
    | exact ⟨(TensorProduct.congr (Module.Free.chooseBasis Qp V).repr (LinearEquiv.refl Qp BdR)).trans
        (TensorProduct.finsuppScalarLeft _ _ _), fun v y i => by simp⟩
    | exact ⟨(TensorProduct.congr (Module.Free.chooseBasis Qp V).repr (LinearEquiv.refl Qp BdR)).trans
        TensorProduct.finsuppScalarLeft, fun v y i => by simp⟩
  have hmem : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, he]
      exact Submodule.smul_of_tower_mem _ _ w.2
    | add y z hy hz =>
      simp only [map_add, Finsupp.add_apply]
      exact Submodule.add_mem _ hy hz
  have h0 : e x = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hmem a x (hx a) i
  exact (LinearEquiv.map_eq_zero_iff e).1 h0
end Formalism.MainNotions.N.Pv.LocalLengthBound
