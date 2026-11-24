-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.pow_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:25.10618+00:00
-- url     : https://prove2.me/submissions/470c1c11-bde9-4d51-91c6-1a78b4d24017

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
namespace Formalism.IndefR.LocBrg
theorem _root_.solution {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ N : ℕ, γ ^ N < δ := by
  rcases eq_or_ne γ 0 with h0 | h0
  · exact ⟨1, by rw [h0, pow_one]; exact zero_lt_iff.mpr δ.ne_zero⟩
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp h0
  obtain ⟨d, hd⟩ := WithZero.ne_zero_iff_exists.mp δ.ne_zero
  rw [← hd]
  have hg : g < 1 := by exact_mod_cast hγ
  have ha : Multiplicative.toAdd g < 0 := by
    have := Multiplicative.toAdd_lt.mpr hg
    simpa using this
  have hn : 1 - Multiplicative.toAdd d ≤ ((Int.toNat (1 - Multiplicative.toAdd d) : ℕ) : ℤ) :=
    Int.self_le_toNat _
  have hn0 : (0 : ℤ) ≤ ((Int.toNat (1 - Multiplicative.toAdd d) : ℕ) : ℤ) := Nat.cast_nonneg _
  refine ⟨Int.toNat (1 - Multiplicative.toAdd d), ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  nlinarith
end Formalism.IndefR.LocBrg
