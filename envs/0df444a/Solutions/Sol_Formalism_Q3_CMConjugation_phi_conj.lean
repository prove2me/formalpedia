-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.phi_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:22.460599+00:00
-- url     : https://prove2.me/submissions/0f01ca07-e4e4-4114-9dac-0506a9c9603f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_q_pos
import Theorems.Thm_Formalism_Q3_CMConjugation_alpha_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMConjugation
theorem _root_.solution (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (i : Fin 3) :
    starRingEnd ℂ (φ (α i)) = -φ (α i) := by
  set z := φ (α i) with hzdef
  have hz : z ^ 2 = -(q i : ℂ) := by
    rw [hzdef, ← map_pow, alpha_sq hα i, map_neg, map_natCast]
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exfalso
    have hre := Complex.conj_eq_iff_re.1 h2
    have h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q i : ℝ) : ℝ) : ℂ) := by
      push_cast; rw [hre]; exact hz
    have h4 := Complex.ofReal_injective h3
    have h5 : (0 : ℝ) < q i := by exact_mod_cast q_pos hq i
    nlinarith [sq_nonneg z.re]
  · exact h2
end Formalism.Q3.CMConjugation
