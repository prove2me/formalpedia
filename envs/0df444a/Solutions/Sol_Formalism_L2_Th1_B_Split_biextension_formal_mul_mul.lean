-- Prove2me | solution 1 for Formalism.L2.Th1.B.Split.biextension_formal_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:31.879984+00:00
-- url     : https://prove2.me/submissions/c180d764-daa1-4b61-96ec-7407858693a2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_sub
import Theorems.Thm_Formalism_L2_Th1_C_Calc_phNorm_pt
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Split
open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}
namespace Formalism.L2.Th1.B.Split
theorem _root_.solution (hF : Frame R l linv ph) {a b : K} (hN : PhNormAt R l linv ph a b)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) ((a * b) • be0 l linv ph x y) := by
  have e1 := phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)
  have e2 := phNorm_pt hF.1 hN hx
  have e3 := phNorm_pt hF.1 hN hy
  rw [fmul_fadd hF.1 a hx.1 hy.1] at e1
  have := cong_sub (cong_sub e1 e2) e3
  rw [← smul_sub, ← smul_sub] at this
  exact this
end Formalism.L2.Th1.B.Split
