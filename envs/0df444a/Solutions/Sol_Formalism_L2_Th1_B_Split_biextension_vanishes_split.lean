-- Prove2me | solution 1 for Formalism.L2.Th1.B.Split.biextension_vanishes_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:04.253177+00:00
-- url     : https://prove2.me/submissions/2e03569c-724a-4e8f-9ff5-a32dcbfcdf09

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
import Theorems.Thm_Formalism_L2_Th1_B_Split_cong_smul
import Theorems.Thm_Formalism_L2_Th1_B_Split_lg_of_smul
import Theorems.Thm_Formalism_L2_Th1_B_Split_biextension_formal_mul_mul
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_symm
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_trans
import Theorems.Thm_Formalism_L2_Th1_C_Pts_addDefect_comm
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul


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
theorem _root_.solution (hF : Frame R l linv ph) {a b : K} (ha : EndInt R l linv a)
    (hB : IsBinomScalar R a) (hZ : ZLinAt R l linv ph a) (hN : PhNormAt R l linv ph a b)
    (hc : a * (a - b) ≠ 0) (hinv : IsBinomScalar R (a * (a - b))⁻¹)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    LG R (be0 l linv ph x y) := by
  have hax : IsPt R (fmul l linv a x) := isPt_fmul hF.1 ha hx
  have e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y))
      (a • be0 l linv ph (fmul l linv a x) y) := hZ σ _ _ hax hy
  have e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y) := by
    have := hZ σ y x hy hx
    rwa [addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x] at this
  have e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y) :=
    cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)
  refine lg_of_smul hc hinv ?_
  have e : (a * (a - b)) • be0 l linv ph x y =
      a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y := by
    rw [smul_smul, ← sub_smul, mul_sub]
  rw [e]
  exact e3
end Formalism.L2.Th1.B.Split
