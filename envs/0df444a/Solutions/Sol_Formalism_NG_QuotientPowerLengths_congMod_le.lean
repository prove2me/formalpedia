-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.congMod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:12.866256+00:00
-- url     : https://prove2.me/submissions/def501af-2c46-488e-b141-e38b2fcb31e7

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_quot_mono
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_img_le
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_core
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_vx_pres
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_VS_pres
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_VS_sup_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (hsum : (⨆ x, Vx T act x) = ⊤) (L : Submodule O V) (hL : L.FG)
    (S : Finset X) (E : Set (Module.End (FractionRing O) V)) (w : X → ℕ∞)
    (hcomm : ∀ g ∈ E, ∀ f : T, g * act f = act f * g)
    (hEL : ∀ g ∈ E, ∀ v ∈ L, g v ∈ L) (hES : ∀ g ∈ E, ∀ v ∈ L, g v ∈ VS T act (S : Set X))
    (hmin : ∀ x ∈ S, ∃ g ∈ E, ∃ l : O, (∀ v ∈ Vx T act x, g v = l • v) ∧ addVal O l ≤ w x) :
    Module.length O (CongMod T act L (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T act x) : ℕ∞) * w x := by
  have hcore := core E (Vx T act) w S
    (fun f hf x _ => vx_pres f (hcomm f hf) x) hmin (VS T act ((S : Set X)ᶜ))
    (fun f hf => VS_pres f (fun y => vx_pres f (hcomm f hf) y) _) L hL hEL
    (by
      intro v _
      have hv : v ∈ VS T act (S : Set X) ⊔ VS T act ((S : Set X)ᶜ) := by
        rw [VS_sup_compl hsum (S : Set X)]
        exact Submodule.mem_top
      exact hv)
  refine le_trans (quot_mono ?_) hcore
  unfold Dsub
  refine Submodule.comap_mono (sup_le_sup_right ?_ _)
  refine le_inf ?_ (img_le hEL)
  unfold img
  rw [Submodule.span_le]
  rintro v ⟨f, hf, n, hn, rfl⟩
  exact hES f hf n hn
end Formalism.NG.QuotientPowerLengths
