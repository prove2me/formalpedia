-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.cob_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:15.992375+00:00
-- url     : https://prove2.me/submissions/c939cee3-2011-48f8-99af-2a871de14322

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
private theorem powerSeries_subst_subst_eq_subst_comp {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    {e : PowerSeries K} (he : PowerSeries.constantCoeff e = 0) (f : PowerSeries K) :
    PowerSeries.subst (PowerSeries.subst a e) f = PowerSeries.subst a (PowerSeries.subst e f) := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  have h2 : HasSubst (fun _ : Unit => e) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => he
  show subst (fun _ : Unit => subst (fun _ : Unit => a) e) f =
    subst (fun _ : Unit => a) (subst (fun _ : Unit => e) f)
  rw [subst_comp_subst_apply h2 h1]
private theorem mvSubst_powerSeries_subst_of_constantCoeff_eq_zero {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  show subst b (subst (fun _ : Unit => a) f) = subst (fun _ : Unit => subst b a) f
  rw [subst_comp_subst_apply h1 hb]
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
    (phE : PowerSeries K) :
    cob F (PowerSeries.subst θ phE) =
      subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] (cob FE phE) := by
  have hθ := h.1
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX i) θ hθ
  have hφ : HasSubst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] := hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1)
  have e0 : ∀ i : Fin 2, PowerSeries.subst (![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] i) phE =
      at1 i (PowerSeries.subst θ phE) := by
    intro i; fin_cases i <;> (unfold at1; exact powerSeries_subst_subst_eq_subst_comp (hX _) hθ phE)
  unfold cob
  rw [mvSubst_sub_of_hasSubst hφ, mvSubst_sub_of_hasSubst hφ, mvSubst_powerSeries_subst_of_constantCoeff_eq_zero hφ hFE0, ← h.2, mvSubst_at1_eq_powerSeries_subst hφ, mvSubst_at1_eq_powerSeries_subst hφ,
    powerSeries_subst_subst_eq_subst_comp hF0 hθ, e0 0, e0 1]
end Formalism.L2.Th1.D.TraceNormBounds
