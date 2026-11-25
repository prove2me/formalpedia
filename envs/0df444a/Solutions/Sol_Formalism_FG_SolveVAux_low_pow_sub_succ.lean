-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_pow_sub_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:18.90189+00:00
-- url     : https://prove2.me/submissions/25aebae8-44a0-4a45-bbb8-ea0c07158b8b

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_P_add
import Theorems.Thm_Formalism_FG_SolveVAux_P_single
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (e : ι →₀ ℕ)
    (he : 2 ≤ e.degree) : Low (M + 1) (P k e - P k' e) := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! hc; exact hne (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff]; omega
  set e' := e - Finsupp.single i 1 with he'
  have hsplit : e = e' + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : e.degree = e'.degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  have h1 : Low 1 (P k' e') := low_mono (by omega) (low_P hk' e')
  rw [hsplit, P_add, P_add, P_single, P_single, pow_one, pow_one]
  have e2 : P k e' * k i - P k' e' * k' i =
      (P k e' - P k' e') * k i + P k' e' * (k i - k' i) := by
    ring
  rw [e2]
  refine low_add (low_mul (low_pow_sub₂ hkk e') (hk i)) ?_
  rw [add_comm]
  exact low_mul h1 (hkk i)
end Formalism.FG.SolveVAux
