-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.product_real_characters_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:05.32924+00:00
-- url     : https://prove2.me/submissions/fdad6629-a967-4846-8bea-74da1ca0948d

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality

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
theorem _root_.solution {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h1 : χ₁ ^ 2 = 1) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) :
    ψ ^ 2 = 1 := by
  ext a
  have hm : (((a : ZMod (q₁ * q)).val : ℕ) : ZMod (q₁ * q)) = a := ZMod.natCast_zmod_val _
  set m := (a : ZMod (q₁ * q)).val with hmdef
  have hcop : m.Coprime (q₁ * q) :=
    (ZMod.isUnit_iff_coprime m (q₁ * q)).mp (by rw [hm]; exact a.isUnit)
  have c1 : m.Coprime q₁ := Nat.Coprime.coprime_dvd_right (dvd_mul_right q₁ q) hcop
  have c2 : m.Coprime q := Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hcop
  rw [MulChar.one_apply_coe, MulChar.pow_apply' ψ two_ne_zero, ← hm, hψ m, mul_pow,
    ← MulChar.pow_apply' χ₁ two_ne_zero, ← MulChar.pow_apply' χ two_ne_zero, h1, h2,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q₁).mpr c1),
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr c2), one_mul]
end Formalism.ZeroFreeDirichlet
