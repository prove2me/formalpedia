-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_isSub_bot_or_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:55.246538+00:00
-- url     : https://prove2.me/submissions/d509fb8e-4e6b-424e-b54b-50c5f3f7babc

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations.FilPhi
theorem _root_.solution [NeZero n] (F : FilPhi LL D n Emb)
    (hl : ∀ i, finrank LL ↥(F.Dl i) = 1) (D' : Submodule LL D) (hD : F.IsSub D') :
    D' = ⊥ ∨ D' = ⊤ := by
  by_cases h : ∀ i, D' ⊓ F.Dl i = ⊥
  · left
    rw [hD.2]
    simp [h]
  · right
    push Not at h
    obtain ⟨i, hi⟩ := h
    have key : ∀ j, F.Dl j ≤ D' → F.Dl (j + 1) ≤ D' := by
      intro j hj
      rw [← F.φ_Dl j]
      rintro _ ⟨x, hx, rfl⟩
      exact hD.1 x (hj hx)
    have hi' : F.Dl i ≤ D' := by
      have hle : D' ⊓ F.Dl i ≤ F.Dl i := inf_le_right
      have h1 : finrank LL ↥(D' ⊓ F.Dl i) ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero]; exact hi
      have h2 : finrank LL ↥(D' ⊓ F.Dl i) ≤ finrank LL ↥(F.Dl i) := Submodule.finrank_mono hle
      have heq : D' ⊓ F.Dl i = F.Dl i :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hl i] at h2 ⊢; omega)
      rw [← heq]; exact inf_le_left
    have hall : ∀ k : ℕ, F.Dl (i + k) ≤ D' := by
      intro k
      induction k with
      | zero => simpa using hi'
      | succ k ih =>
        have := key _ ih
        rwa [add_assoc, ← Nat.cast_succ] at this
    have hj : ∀ j, F.Dl j ≤ D' := by
      intro j
      have := hall (j - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    rw [eq_top_iff, ← F.internal.submodule_iSup_eq_top]
    exact iSup_le hj
end Formalism.WeaklyAdmissibleFiltrations.FilPhi
