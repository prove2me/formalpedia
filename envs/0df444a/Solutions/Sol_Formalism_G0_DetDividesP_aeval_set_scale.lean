-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_set_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:36.133899+00:00
-- url     : https://prove2.me/submissions/003a2442-5f0c-4261-a577-ba9801c79729

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_letter_scale

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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (U : Finset ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 ∈ U then t * z p else z p) G =
      t ^ (∑ i ∈ U, d i) * MvPolynomial.aeval z G := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    have : (fun p : ι × Fin r => if p.1 ∈ insert i U then t * z p else z p) =
        fun p => if p.1 = i then t * (if p.1 ∈ U then t * z p else z p)
          else (if p.1 ∈ U then t * z p else z p) := by
      funext p
      by_cases h1 : p.1 = i
      · simp [h1, hi]
      · simp [h1, Finset.mem_insert]
    rw [this, aeval_letter_scale hG, ih, Finset.sum_insert hi, pow_add]; ring
end Formalism.G0.DetDividesP
