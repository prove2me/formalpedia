-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_Km_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:35:31.964482+00:00
-- url     : https://prove2.me/submissions/ff1fe0e2-54e5-43a7-9841-37ea882f46e7

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaRed
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl
private theorem cT_one_eq_one : cT σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  rw [cT_apply_eq_sigma_transpose]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
end FIwasawaRed
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution : fIwasawaKm σ (1 : Matrix (Fin n) (Fin n) L) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt
  refine ⟨by rw [cT_one_eq_one, Matrix.one_mul, Matrix.mul_one], fun i j => ?_⟩
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le'
end Formalism.UG.P
