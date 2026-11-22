-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:21.318799+00:00
-- url     : https://prove2.me/submissions/ccce86c8-1b01-4757-b336-97df32ff63bc

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
namespace CoeffHom
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ : Fin n → ℕ}
    (hP : CoeffHom P μ) (e : ℕ) : CoeffHom (P ^ e) (e • μ) := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact CoeffHom.one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP
end CoeffHom
end Formalism.GradedWeylDivisibility
