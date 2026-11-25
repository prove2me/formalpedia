-- Prove2me | solution 1 for Formalism.UG.P.levelv_nat_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:52.126429+00:00
-- url     : https://prove2.me/submissions/6e7e753b-a0f1-4117-8a7d-62b7f3d9321e

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hfin : ∀ s : R, s ≠ 0 → Finite (R ⧸ Ideal.span {s})) (x : K) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ y : R, algebraMap R K y = N • x := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  haveI := hfin s hs0
  have hN : ringChar (R ⧸ Ideal.span {s}) ≠ 0 :=
    CharP.char_ne_zero_of_finite (R ⧸ Ideal.span {s}) (ringChar (R ⧸ Ideal.span {s}))
  have hmem : ((ringChar (R ⧸ Ideal.span {s}) : ℕ) : R) ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨ringChar (R ⧸ Ideal.span {s}), hN, t * a, ?_⟩
  have hs' : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  rw [nsmul_eq_mul, ← map_natCast (algebraMap R K), ← ht, map_mul, map_mul]
  field_simp <;> ring
end Formalism.UG.P
