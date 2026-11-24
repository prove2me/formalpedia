-- Prove2me | solution 1 for Formalism.L2.Pj.CurveCount.aeval_div_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:43.258607+00:00
-- url     : https://prove2.me/submissions/cf50b9f8-a52b-41e1-a2e1-0df4327e88a5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA
import Theorems.Thm_P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial
namespace Formalism.L2.Pj.CurveCount
theorem _root_.solution {K L σ : Type*} [Field K] [Field L] [Algebra K L] (g : σ → L) (c : L)
    {P : MvPolynomial σ K} {k : ℕ} (hP : P.IsHomogeneous k) :
    aeval (fun i => g i / c) P = c⁻¹ ^ k * aeval g P := by
  have h := eval₂_mul_homog (algebraMap K L) c⁻¹ g hP
  show MvPolynomial.eval₂ (algebraMap K L) (fun i => g i / c) P =
    c⁻¹ ^ k * MvPolynomial.eval₂ (algebraMap K L) g P
  rw [← h]
  congr 1
  funext i
  rw [div_eq_mul_inv, mul_comm]
end Formalism.L2.Pj.CurveCount
