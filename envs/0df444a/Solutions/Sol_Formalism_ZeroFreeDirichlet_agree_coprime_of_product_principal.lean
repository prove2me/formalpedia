-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.agree_coprime_of_product_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:05.414082+00:00
-- url     : https://prove2.me/submissions/92967655-900d-481a-9bad-5c2f193d7235

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality
import Theorems.Thm_Formalism_ZeroFreeDirichlet_real_character_apply_sq_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q₁ q : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) (hψ1 : ψ = 1) :
    ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q) := by
  intro n hn
  have hu : IsUnit (n : ZMod (q₁ * q)) := (ZMod.isUnit_iff_coprime n (q₁ * q)).mpr hn
  have e1 : χ₁ (n : ZMod q₁) * χ (n : ZMod q) = 1 := by
    rw [← hψ n, hψ1, MulChar.one_apply hu]
  have e2 := real_character_apply_sq_eq_one χ h2 (Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hn)
  calc χ₁ (n : ZMod q₁) = χ₁ (n : ZMod q₁) * (χ (n : ZMod q) * χ (n : ZMod q)) := by
        rw [e2, mul_one]
    _ = (χ₁ (n : ZMod q₁) * χ (n : ZMod q)) * χ (n : ZMod q) := by ring
    _ = χ (n : ZMod q) := by rw [e1, one_mul]
end Formalism.ZeroFreeDirichlet
