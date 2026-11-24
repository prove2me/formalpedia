-- Prove2me | solution 1 for Formalism.UG.P.definite_form_signature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:20.707846+00:00
-- url     : https://prove2.me/submissions/25fd5851-df41-4084-9e48-2ba16df4b1b5

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_Q_dot
import Theorems.Thm_Formalism_UG_P_stdform_psd
import Theorems.Thm_Formalism_UG_P_stdform_conj
import Theorems.Thm_Formalism_UG_P_stdform_hform_fixed
import Theorems.Thm_Formalism_UG_P_stdform_Q_eq
import Theorems.Thm_Formalism_UG_P_stdform_sig_pos
import Theorems.Thm_Formalism_UG_P_stdform_sig_neg
import Theorems.Thm_Formalism_UG_P_sig_data
import Theorems.Thm_Formalism_UG_P_sig_quad
import Theorems.Thm_Formalism_UG_P_signature_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.DefSig := by
  intro F E _ _ _ n _ _ σ J ι τ hσ hι hfix hJ hdet
  have hfixed : ∀ x : n → E, ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x :=
    fun x => hfix _ (stdform_hform_fixed σ τ hσ J hJ x)
  have hτx : ∀ x : n → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx h
    apply hx
    funext i
    have := congrFun h i
    exact τ.injective (by simpa using this)
  constructor
  · intro hdef
    have hMh : IsHerm (starRingEnd ℂ) (J.map τ) := by
      have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
        have := congrFun (congrFun hJ j) i
        simpa [cT] using this
      ext i j
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [← stdform_conj σ τ hσ, hJ']
    have hMdet : IsUnit (J.map τ).det := by
      have h := (RingHom.map_det τ J).symm
      rw [show (J.map τ) = τ.mapMatrix J from rfl, h]
      exact hdet.map τ
    obtain ⟨p, q, hs⟩ := signature_exists n (J.map τ) hMh hMdet
    obtain ⟨hcard, Q, hQ⟩ := sig_data (J.map τ) p q hs
    have hM : ∀ i j, ∃ e, τ e = (J.map τ) i j := fun i j => ⟨J i j, rfl⟩
    rcases hdef with hpos | hneg
    · have hpsd := stdform_psd τ (J.map τ) hM 1 (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hpos x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha, one_mul]
        exact hιa)
      have hq : q = 0 := by
        by_contra hq0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hq
      have hp : p = Fintype.card n := by omega
      subst hp
      exact Or.inl hs
    · have hpsd := stdform_psd τ (J.map τ) hM (-1) (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hneg x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha]
        linarith)
      have hp : p = 0 := by
        by_contra hp0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hp
      have hq : q = Fintype.card n := by omega
      subst hq
      exact Or.inr hs
  · rintro (hs | hs)
    · left
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_pos _ hs _ (hτx x hx)
    · right
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_neg _ hs _ (hτx x hx)
end Formalism.UG.P
