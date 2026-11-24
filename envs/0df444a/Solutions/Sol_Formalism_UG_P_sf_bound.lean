-- Prove2me | solution 1 for Formalism.UG.P.sf_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:09.315807+00:00
-- url     : https://prove2.me/submissions/40ec8960-8a9e-4b10-84f2-9e9d22e0c271

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Theorems.Thm_Formalism_UG_P_sf_cs
import Theorems.Thm_Formalism_UG_P_sf_map
import Theorems.Thm_Formalism_UG_P_sf_gram
import Theorems.Thm_Formalism_UG_P_sf_single
import Theorems.Thm_Formalism_UG_P_sf_sign

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) (g : Matrix n n E)
    (hg : cT (σ : E →+* E) g * J * g = J) (i j : n) :
    ‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖ := by
  classical
  obtain ⟨s, hs, hsign⟩ := sf_sign σ J τ hτ hdef
  have hA : ∀ a b, conj ((J.map τ) b a) = (J.map τ) a b := by
    intro a b
    have h3 : τ ((σ : E →+* E) (J b a)) = conj (τ (J b a)) := RingHom.congr_fun hτ _
    have h4 : (σ : E →+* E) (J b a) = J a b := by
      have h1 : (cT (σ : E →+* E) J) a b = J a b := by rw [hH]
      exact h1
    simp only [Matrix.map_apply]
    rw [← h3, h4]
  have hc : (J * g) i j = hform (σ : E →+* E) J (Pi.single i 1) (fun k => g k j) := by
    rw [sf_single]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hb : hform (σ : E →+* E) J (fun k => g k j) (fun k => g k j) = J j j := by
    rw [← sf_gram, hg]
  have ha : hform (σ : E →+* E) J (Pi.single i 1) (Pi.single i 1) = J i i := by
    rw [sf_single]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hau : τ (J i i) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    rw [← sf_map _ τ hτ, ha]
  have hcu : τ ((J * g) i j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hc]
  have hbv : τ (J j j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (g k j)) (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hb]
  obtain ⟨tw, htw, -, htw0⟩ := hsign ((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E))
  obtain ⟨ta, hta, hta1, -⟩ := hsign (Pi.single i 1 : n → E)
  obtain ⟨tb, htb, -, htb0⟩ := hsign (fun k => g k j)
  have hei : (Pi.single i 1 : n → E) ≠ 0 := by
    intro h
    have h5 := congr_fun h i
    simp at h5
  have hta' := hta1 hei
  rw [ha] at hta
  rw [hb] at htb
  rw [sf_map _ τ hτ] at htw
  have hw : (fun k => τ (((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E)) k)) =
      τ (J i i) • (fun k => τ (g k j)) + (-τ ((J * g) i j)) • (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    funext k
    simp [map_add, map_mul, map_neg]
  rw [hw, hau, hcu, sf_cs _ hA, ← hau, ← hcu, ← hbv, hta, htb] at htw
  rw [← Complex.normSq_eq_conj_mul_self] at htw
  have key : ta * (ta * tb - Complex.normSq (τ ((J * g) i j))) = tw := by exact_mod_cast htw
  have hN : Complex.normSq (τ ((J * g) i j)) = ‖τ ((J * g) i j)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [hN] at key
  have h1 : ‖τ ((J * g) i j)‖ ^ 2 ≤ ta * tb := by
    by_contra hneg
    push_neg at hneg
    have h6 : s * tw < 0 := by
      rw [← key]
      nlinarith
    linarith
  have h3 : ta * tb ≤ |ta| * |tb| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [hta, htb]
  have hn1 : ‖((ta : ℝ) : ℂ)‖ = |ta| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖((tb : ℝ) : ℂ)‖ = |tb| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn1, hn2]
  nlinarith [abs_nonneg ta, abs_nonneg tb, norm_nonneg (τ ((J * g) i j))]
end Formalism.UG.P
