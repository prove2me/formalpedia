-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.subst_linSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:16.196798+00:00
-- url     : https://prove2.me/submissions/deeb2637-187a-4548-b4b3-dd03644295ef

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (M : ZV d N0 N1 → ι' → K) (A : ι → ι' → K) (Mg : ZV d N0 N1 → ι → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (z : ZV d N0 N1) :
    MvPowerSeries.subst
        (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
        (linSub M z) = linSub Mg z := by
  have ha : MvPowerSeries.HasSubst (fun j : ι' =>
      (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  have hC : ∀ c : K, MvPowerSeries.subst (fun j : ι' =>
      (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.C c : MvPowerSeries ι' K) = MvPowerSeries.C c := by
    intro c
    first
    | simpa using (MvPowerSeries.substAlgHom ha).commutes c
    | (rw [← MvPowerSeries.coe_substAlgHom ha]; simpa using (MvPowerSeries.substAlgHom ha).commutes c)
    | (rw [← MvPowerSeries.coe_substAlgHom ha]
       exact (MvPowerSeries.substAlgHom ha).commutes c)
  unfold linSub
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_mul, MvPowerSeries.coe_substAlgHom, hC, MvPowerSeries.subst_X ha, h, map_sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring
end Formalism.DworkPowerSeriesWeights
