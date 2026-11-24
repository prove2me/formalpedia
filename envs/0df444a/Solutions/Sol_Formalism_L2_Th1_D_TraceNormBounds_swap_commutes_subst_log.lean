-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.swap_commutes_subst_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:13.286529+00:00
-- url     : https://prove2.me/submissions/e0363f0e-770d-4eca-a2ae-c136e75f6915

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
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
private theorem mvSubst_at1_eq_powerSeries_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b) (x : ι)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  have hx : HasSubst (fun _ : Unit => (X x : MvPowerSeries ι K)) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => by simp
  show subst b (subst (fun _ : Unit => (X x : MvPowerSeries ι K)) f) = subst (fun _ : Unit => b x) f
  rw [subst_comp_subst_apply hx hb]
  simp only [subst_X hb]
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
theorem _root_.solution {θ : PowerSeries K} (hθ : PowerSeries.constantCoeff θ = 0)
    (H : MvPowerSeries (Fin 2) K) :
    swap2 (subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] H) =
      subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] (swap2 H) := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX i) θ hθ
  unfold swap2
  rw [mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)) (hat 0) (hat 1), mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1)) (hX 1) (hX 0),
    mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)), mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0))]
  simp only [subst_X (hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1))]
  rfl
end Formalism.L2.Th1.D.TraceNormBounds
