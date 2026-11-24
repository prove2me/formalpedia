-- Prove2me | solution 1 for Formalism.GM.ProjS.eq_zero_of_eulL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:44.053796+00:00
-- url     : https://prove2.me/submissions/3e3f265a-105e-44ed-b9b3-65047165c4ff

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_coeff_eulL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) [CharZero k]
    (h : eulL t g = ((a : k) - (b : k)) • g) : g = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have h1 := congrArg (coeff m) h
  rw [coeff_eulL, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm ((a : k) - b)] at h1
  have h2 : (∑ c, (m (t c) : k)) = (a : k) - b := mul_left_cancel₀ hne h1
  have h3 : ((∑ c, m (t c) + b : ℕ) : k) = ((a : ℕ) : k) := by
    push_cast
    rw [h2]
    ring
  have h4 := Nat.cast_injective h3
  omega
end Formalism.GM.ProjS
