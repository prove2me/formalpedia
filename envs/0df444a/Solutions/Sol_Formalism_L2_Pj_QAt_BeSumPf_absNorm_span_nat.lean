-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.BeSumPf.absNorm_span_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:44.709977+00:00
-- url     : https://prove2.me/submissions/72532c1b-2798-49ff-a339-4583f6dfea9d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open Formalism.L2.Pj.QAt.BeSumPf
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.Pj.QAt.BeSumPf
theorem _root_.solution (n' : ℕ) :
    Ideal.absNorm (Ideal.span {(n' : 𝓞 K)}) = n' ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have h : ((n' : 𝓞 K)) = algebraMap ℤ (𝓞 K) (n' : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp [Int.natAbs_pow]
end Formalism.L2.Pj.QAt.BeSumPf
