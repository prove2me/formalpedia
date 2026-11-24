-- Prove2me | solution 1 for Formalism.G0.DetDividesP.degreeOf_eq_zero_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:22.874797+00:00
-- url     : https://prove2.me/submissions/caafa491-1bdf-4be6-8af1-ca5991c19bc4

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {σ : Type} {p f : MvPolynomial σ K} (x : σ) (hpf : p ∣ f) (hf : f ≠ 0)
    (h : degreeOf x f = 0) : degreeOf x p = 0 := by
  obtain ⟨q, rfl⟩ := hpf
  have hp : p ≠ 0 := left_ne_zero_of_mul hf
  have hq : q ≠ 0 := right_ne_zero_of_mul hf
  rw [degreeOf_mul_eq hp hq] at h
  omega
end Formalism.G0.DetDividesP
