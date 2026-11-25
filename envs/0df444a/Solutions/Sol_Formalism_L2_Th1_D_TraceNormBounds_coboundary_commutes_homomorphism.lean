-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.coboundary_commutes_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:55.736249+00:00
-- url     : https://prove2.me/submissions/d3d16e34-f348-4655-aea0-635a5919b26e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_constantCoeff_first_two_of_three
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_constantCoeff_first_two_of_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_constantCoeff_first_two_of_three
import Theorems.Thm_Formalism_LT_InvIntP_key
import Theorems.Thm_P2M_Formalism_LT_LTL_key__07a773ad9047

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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
namespace TraceNormBounds
section Alg
variable {K : Type} [Field K]
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
private theorem hasSubst_vec_pair_of_constantCoeff_eq_zero {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]
private theorem mvSubst_sub_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f - g) = subst φ f - subst φ g := by
  first
  | exact MvPowerSeries.subst_sub hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_sub _ f g)
  | exact map_sub (substAlgHom hφ) f g
private theorem mvSubst_at1_eq_powerSeries_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b) (x : ι)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  have hx : HasSubst (fun _ : Unit => (X x : MvPowerSeries ι K)) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => by simp
  show subst b (subst (fun _ : Unit => (X x : MvPowerSeries ι K)) f) = subst (fun _ : Unit => b x) f
  rw [subst_comp_subst_apply hx hb]
  simp only [subst_X hb]
private theorem mvSubst_powerSeries_subst_of_constantCoeff_eq_zero {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  show subst b (subst (fun _ : Unit => a) f) = subst (fun _ : Unit => subst b a) f
  rw [subst_comp_subst_apply h1 hb]
private theorem mvSubst_subst_vec_pair_eq_subst_vec_pair {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    {a b : MvPowerSeries ι K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin 2) K) :
    subst φ (subst ![a, b] f) = subst ![subst φ a, subst φ b] f := by
  rw [subst_comp_subst_apply (hasSubst_vec_pair_of_constantCoeff_eq_zero ha hb) hφ]
  congr 1
  funext i
  fin_cases i <;> rfl
end Alg
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Normed
end TraceNormBounds
open TraceNormBounds
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {F FE : MvPowerSeries (Fin 2) K} {θ : PowerSeries K}
    (hF0 : constantCoeff F = 0) (hFE0 : constantCoeff FE = 0) (h : IsHom F FE θ)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] H) =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (d1 FE H) := by
  have hθ := h.1
  have hX3 : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have hX2 : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat2 : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX2 i) θ hθ
  have hat3 : ∀ i : Fin 3, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX3 i) θ hθ
  have hφ3 : HasSubst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] := by
    apply hasSubst_finite_of_constantCoeff_eq_zero
    intro i
    fin_cases i
    · exact hat3 0
    · exact hat3 1
    · exact hat3 2
  have h01 : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1] := hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 1)
  have key : PowerSeries.subst (in3 F) θ =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (in3 FE) := by
    unfold in3
    rw [← mvSubst_powerSeries_subst_of_constantCoeff_eq_zero h01 hF0, h.2, mvSubst_subst_vec_pair_eq_subst_vec_pair h01 (hat2 0) (hat2 1), mvSubst_at1_eq_powerSeries_subst h01, mvSubst_at1_eq_powerSeries_subst h01,
      mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 0) (hX3 1), subst_X hφ3, subst_X hφ3]
    rfl
  have key' : PowerSeries.subst ((![in3 F, X 2] : Fin 2 → MvPowerSeries (Fin 3) K) 0) θ =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (in3 FE) := key
  unfold d1
  rw [mvSubst_sub_of_hasSubst hφ3, mvSubst_sub_of_hasSubst hφ3,
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (constantCoeff_first_two_of_three hF0) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 1) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (constantCoeff_first_two_of_three hFE0) (hX3 2), mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 0) (hX3 2), mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 1) (hX3 2)]
  simp only [mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (constantCoeff_first_two_of_three hF0) (hX3 2)), mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 2)),
    mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 1) (hX3 2)), subst_X hφ3]
  first
  | (rw [key']; rfl)
  | (rw [key]; rfl)
  | (rw [key']; simp)
  | (rw [key]; simp)
end Formalism.L2.Th1.D.TraceNormBounds
