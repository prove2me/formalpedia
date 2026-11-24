-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_first_coboundary_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:21.983751+00:00
-- url     : https://prove2.me/submissions/358b6f48-76b5-46ce-aae8-ab970d2576d2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs3
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst2_comp
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
namespace Pair
section Alg
variable {K : Type} [Field K]
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
private theorem mvSubst_sub {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f - g) = subst φ f - subst φ g := by
  first
  | exact MvPowerSeries.subst_sub hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_sub _ f g)
  | exact map_sub (substAlgHom hφ) f g
private theorem constantCoeff_in3_eq_zero {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  have hx : ∀ i : Fin 2, constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1] i) = 0 := by
    intro i; fin_cases i <;> simp
  first
  | exact constantCoeff_subst_eq_zero hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx hF0
  | exact constantCoeff_subst_eq_zero hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hF0 hx
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hF0 hx
  | (apply constantCoeff_subst_eq_zero <;> first | assumption | exact hasSubst_finite_of_constantCoeff_eq_zero hx)
end Alg
section NormedLin
variable {K : Type} [NormedField K]
end NormedLin
section Normed
variable {K : Type} [NormedField K] [CharZero K]
end Normed
end Pair
open Pair
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) {τ : Type}
    {a b c : MvPowerSeries τ K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hc : constantCoeff c = 0) (H : MvPowerSeries (Fin 2) K) :
    subst ![a, b, c] (d1 F H) =
      subst ![subst ![a, b] F, c] H - subst ![a, c] H - subst ![b, c] H := by
  have h3 := hs3 ha hb hc
  have hX : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have e1 : subst ![a, b, c] (in3 F) = subst ![a, b] F := by
    unfold in3
    rw [subst2_comp h3 (hX 0) (hX 1)]
    simp only [subst_X h3]
    first | rfl | simp
  unfold d1
  rw [mvSubst_sub h3, mvSubst_sub h3, subst2_comp h3 (constantCoeff_in3_eq_zero hF0) (hX 2),
    subst2_comp h3 (hX 0) (hX 2), subst2_comp h3 (hX 1) (hX 2), e1]
  simp only [subst_X h3]
  first | rfl | simp
end Formalism.L2.Th1.D.Pair
