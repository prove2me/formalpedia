-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.ge_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:33.82453+00:00
-- url     : https://prove2.me/submissions/c07af4f9-08ac-4e82-8a3e-48f3ebd335d7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
namespace VF
theorem _root_.solution (V : VF C) {ζ : C} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at h
    exact zero_ne_one h
  have h1 : n • V.v ζ = 0 := by
    rw [← AddValuation.map_pow, h, AddValuation.map_one]
  have ht : V.v ζ ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact hζ0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul, mul_eq_zero] at h1
  have hr0 : r = 0 := h1.resolve_left (Nat.cast_ne_zero.mpr hn)
  unfold VF.Ge
  rw [← hr]
  exact WithTop.coe_le_coe.mpr hr0.ge
end VF
end Formalism.L2.FormalSeriesBounds
