-- Prove2me | solution 1 for Formalism.MainNotions.N.Pv.LocalLengthBound.rk_filV_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:00.26211+00:00
-- url     : https://prove2.me/submissions/ad7c5704-92be-4b1c-bc1a-f3f4357c6d65

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientImageDivisibility_RkMultVOfNotJump
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_anti
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_exh

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
theorem _root_.solution (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset (V ⊗[Qp] BdR), Submodule.span LL (s : Set (V ⊗[Qp] BdR)) = U :=
    (Submodule.fg_iff_finiteDimensional U).2 inferInstance
  have hex : ∀ x ∈ s, ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := fun x _ => rk_filV_exh PD x
  choose! f hf using hex
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne f, ?_⟩
    rw [← hs, Submodule.span_le]
    intro x hx
    exact rk_filV_anti PD (Finset.inf'_le f hx) (hf x hx)
  · refine ⟨0, ?_⟩
    rw [← hs, Finset.not_nonempty_iff_eq_empty.1 hne]
    simp
end Formalism.MainNotions.N.Pv.LocalLengthBound
