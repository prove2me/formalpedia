-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_letter_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:22.669935+00:00
-- url     : https://prove2.me/submissions/0ccbdb0c-655c-4de0-bcbc-1cbdeb195539

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_weighted_scale

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
    {d : ι → ℕ} (hG : MultiHom G d) (i : ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 = i then t * z p else z p) G = t ^ d i * MvPolynomial.aeval z G := by
  rw [← aeval_weighted_scale _ (hG i) t z]
  have : (fun p : ι × Fin r => if p.1 = i then t * z p else z p) =
      fun p => t ^ (if p.1 = i then 1 else 0) * z p := by
    funext p; split_ifs <;> simp
  rw [this]
end Formalism.G0.DetDividesP
