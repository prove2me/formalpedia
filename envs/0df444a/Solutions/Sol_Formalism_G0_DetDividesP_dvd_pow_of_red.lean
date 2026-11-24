-- Prove2me | solution 1 for Formalism.G0.DetDividesP.dvd_pow_of_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:50.323802+00:00
-- url     : https://prove2.me/submissions/d4507386-c082-4f90-a2af-012b293fd661

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_red_of_mul
import Theorems.Thm_Formalism_G0_DetDividesP_dvd_of_red_one

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
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A) :
    ∀ (n : ℕ) (G : MvPolynomial (ι × Fin r) K), Red A G n → detLetters (K := K) A ^ n ∣ G := by
  intro n
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G h
    have h1 : Red A G 1 := fun L _ _ g x hx =>
      (pow_dvd_pow Polynomial.X (by omega)).trans (h L g x hx)
    obtain ⟨G', rfl⟩ := dvd_of_red_one hr A hA G h1
    have h2 := red_of_mul hr A G' n h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih G' h2)
end Formalism.G0.DetDividesP
