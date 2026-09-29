-- Prove2me | solution 1 for CannonFloydParry.isIntegralSubsimplex01_leftPart_and_rightPart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:51:53.658672+00:00
-- url     : https://prove2.me/submissions/0e4b4d90-2e7c-46bb-8553-2310a24513a5

import Definitions.Def_CannonFloydParry_PIP
import Theorems.Thm_CannonFloydParry_isIntegralSubsimplex01_iff

/-!
# Farey intervals and integral projective maps of `[0,1]` (CFP §7, pp. 251–253)

Basic facts: the action of `GL(2, ℤ)` on `(t, 1)`, Farey intervals, and the explicit linear
fractional map `mob I J` between two Farey intervals.
-/

namespace CannonFloydParry.S7

open FracInterval

/-! ### `glAct` on `(t, 1)` -/

/-! ### Farey intervals -/

section Farey

variable {I : FracInterval}

lemma IsFarey.leftPart (hI : I.IsFarey) : I.leftPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨hb, by simp [FracInterval.leftPart]; omega, by simp [FracInterval.leftPart]; omega,
    le_refl _ |>.trans hab, by simp [FracInterval.leftPart]; omega, ?_⟩
  simp only [FracInterval.leftPart]
  push_cast
  linear_combination hdet

lemma IsFarey.rightPart (hI : I.IsFarey) : I.rightPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨by simp [FracInterval.rightPart]; omega, hc, hd, by simp [FracInterval.rightPart]; omega,
    hcd, ?_⟩
  simp only [FracInterval.rightPart]
  push_cast
  linear_combination hdet

end Farey

/-! ### Reduced fractions -/

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

end CannonFloydParry.S7

/-!
# The linear fractional map between two Farey intervals (CFP §7, p. 252)

`mob I J` is the map `ρ ∘ (M_J M_I⁻¹)` in the coordinate `t`; it is integral projective on
`[I.lo, I.hi]`, maps it onto `[J.lo, J.hi]` endpoint to endpoint, and it is the only integral
projective map on `[I.lo, I.hi]` with those endpoint values.
-/

namespace CannonFloydParry.S7

variable {I J : FracInterval}

/-! ### Uniqueness -/

end CannonFloydParry.S7

/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

lemma subsimplex_of_farey {K : FracInterval} (hK : K.IsFarey) : IsIntegralSubsimplex01 K.lo K.hi :=
  ((CannonFloydParry.isIntegralSubsimplex01_iff hK.1 hK.2.1 hK.2.2.1 hK.2.2.2.1
    hK.2.2.2.2.1).mpr hK.2.2.2.2.2).2.2.2

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/

theorem isIntegralSubsimplex01_leftPart_and_rightPart' {I : FracInterval} (hI : I.IsFarey) :
    IsIntegralSubsimplex01 I.leftPart.lo I.leftPart.hi ∧
      IsIntegralSubsimplex01 I.rightPart.lo I.rightPart.hi :=
  ⟨subsimplex_of_farey (IsFarey.leftPart hI), subsimplex_of_farey (IsFarey.rightPart hI)⟩

/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {I : FracInterval} (hI : I.IsFarey) :
    IsIntegralSubsimplex01 I.leftPart.lo I.leftPart.hi ∧
      IsIntegralSubsimplex01 I.rightPart.lo I.rightPart.hi := by
  exact S7.isIntegralSubsimplex01_leftPart_and_rightPart' hI
