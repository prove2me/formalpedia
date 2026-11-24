-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:25.361083+00:00
-- url     : https://prove2.me/submissions/3a14a95e-6cd4-41c8-98bb-499bb3ff5907

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_coef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (l : Fin m) (j : Fin 6) :
    wirtBar l (coef k j) x = if ¬ (j : ℕ) < 3 ∧ l = k then ck k j x else 0 := by
  rw [wirtBar, fderiv_coef hx, fderiv_coef hx]
  by_cases hj : (j : ℕ) < 3 <;> by_cases hl : l = k
  · simp only [hl, hj, if_true, not_true_eq_false, false_and, if_false, Pi.single_eq_same,
      smul_eq_mul]
    linear_combination (ck k j x / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, hj, if_false, not_false_eq_true, and_self, if_true, Pi.single_eq_same,
      smul_eq_mul, star_one, Complex.star_def, Complex.conj_I]
    linear_combination (-(ck k j x) / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]
end Formalism.QuantumDeterminants.WirtingerDerivatives
