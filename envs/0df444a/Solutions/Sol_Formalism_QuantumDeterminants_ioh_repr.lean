-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:29.368813+00:00
-- url     : https://prove2.me/submissions/c63742aa-9705-4e2f-abbc-bb118d617b3a

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_single
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_mem_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_ext
import Theorems.Thm_Formalism_REAL_ecSumV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (P Q : Matrix (Fin n) (Fin n) ℂ) :
    IOHRepr (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) (iohE ε E P Q) := by
  intro a b F x h g hg
  have hF : SmoothOnGV ε F :=
    io_smooth_congr (fun g' hg' => (io_rep_ext x g' hg').trans (h g' hg').symm) (io_mem_smooth x)
  show EcV ε (P * Matrix.single a b 1 * Q) F g =
    (((∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩
  rw [ecSumV n ε E F _ g hF hg]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, ioh_single]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [ioE_rep h c d g hg]
end Formalism.QuantumDeterminants
