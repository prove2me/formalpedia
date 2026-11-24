-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.inVar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:28.330709+00:00
-- url     : https://prove2.me/submissions/e247e77b-e358-4802-9464-ad20faa3e9b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
section Div
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Div
section Alg
variable {K : Type} [Field K] [CharZero K]
private theorem coeff_single_one_at1_eq_ite {ι : Type} [DecidableEq ι] (x y : ι) (l : PowerSeries K) :
    MvPowerSeries.coeff (Finsupp.single y 1) (at1 x l) =
      if x = y then PowerSeries.coeff 1 l else 0 := by
  unfold at1
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X x), finsum_eq_single _ 1]
  · split_ifs with hxy
    · subst hxy
      simp [MvPowerSeries.coeff_X]
    · simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, Ne.symm hxy]
  · intro d hd
    rw [MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro he
    rw [Finsupp.single_eq_single_iff] at he
    rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact hd h1.symm
    · exact one_ne_zero h1
end Alg
section Norm
variable {K : Type} [NormedField K] [CharZero K]
end Norm
end Formalism.L2.Th1.B.E2
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {ι : Type} {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : ι) :
    at1 x l ≠ 0 := by
  classical
  intro h0
  have e := coeff_single_one_at1_eq_ite x x l
  rw [h0, map_zero, if_pos rfl, hl1] at e
  exact zero_ne_one e
end Formalism.L2.Th1.B.E2
