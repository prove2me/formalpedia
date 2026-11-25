-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.emb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:30.414992+00:00
-- url     : https://prove2.me/submissions/0bcef9ae-9939-45bb-a361-778d52bfe41a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_hb_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_tauX_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_em_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_card_le_of_chars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} (hte : ∀ a, tauX (em a) e = 1)
    (b : Module.Basis (Fin d) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (τ : OE →+* R) (hτ : tauX τ e = 1) : ∃ a, τ = em a := by
  by_contra hne
  push Not at hne
  let ff : Option (ZMod d) → OE →+* R := fun o => o.elim τ em
  have hff : Function.Injective ff := by
    intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some a' => exact absurd h (hne a')
    | some a =>
      cases o' with
      | none => exact absurd h.symm (hne a)
      | some a' => exact congrArg some (em_inj em hsep h)
  let χ : Option (ZMod d) → (ℤ_[l] ⊗[ℤ] OE) →+* FractionRing R :=
    fun o => (algebraMap R (FractionRing R)).comp (tauX (ff o)).toRingHom
  have hχ : Function.Injective χ := by
    intro o o' h
    apply hff
    apply tauX_inj (l := l)
    intro s
    exact IsFractionRing.injective R (FractionRing R) (DFunLike.congr_fun h s)
  have := card_le_of_chars (F := ℤ_[l]) χ hχ ((algebraMap R (FractionRing R)).comp (algebraMap ℤ_[l] R))
    (fun o r => by
      show algebraMap R (FractionRing R) (tauX (ff o) (algebraMap ℤ_[l] _ r)) = _
      rw [AlgHom.commutes]
      rfl) e
    (fun o => by
      show algebraMap R (FractionRing R) (tauX (ff o) e) = 1
      cases o with
      | none => show algebraMap R (FractionRing R) (tauX τ e) = 1; rw [hτ, map_one]
      | some a => show algebraMap R (FractionRing R) (tauX (em a) e) = 1; rw [hte, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simp [ZMod.card] at this
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
