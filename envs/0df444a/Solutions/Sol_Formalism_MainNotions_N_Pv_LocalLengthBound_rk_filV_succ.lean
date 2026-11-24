-- Prove2me | solution 1 for Formalism.MainNotions.N.Pv.LocalLengthBound.rk_filV_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:41.061951+00:00
-- url     : https://prove2.me/submissions/c64ec069-845f-49c5-92fb-40d37d562ade

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
theorem _root_.solution (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
end Formalism.MainNotions.N.Pv.LocalLengthBound
