-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:09.821343+00:00
-- url     : https://prove2.me/submissions/ed92fa01-1dd0-467f-91b1-ecd72f91d0df

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
theorem _root_.solution (t : K) (s : ℕ) : antiB t s * antiB t s = (t * t) • (1 : Matrix (Fin s) (Fin s) K) := by
  ext i k
  have hi := i.isLt
  have hk := k.isLt
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Finset.sum_eq_single (⟨s - 1 - i.val, by omega⟩ : Fin s)]
  · simp only [antiB, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro j _ hj
    simp only [antiB]
    rw [if_neg, zero_mul]
    intro h
    apply hj
    ext
    show (j : ℕ) = s - 1 - i.val
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.SG.Pf.StabilizerIndexVolumes
