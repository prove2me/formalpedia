-- Prove2me | solution 1 for CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_mem_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7abc3d97-f824-5bbc-99dc-fdb4e79a7291

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
import Theorems.Thm_Valued_multipliable_one_add_of_tendsto_cofinite_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid

set_option autoImplicit false

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {a b z₀ z : K} (ha : a ∈ affinoid ϖ n) (hb : b ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n)
    (hz : z ∈ affinoid ϖ n) :
    ThetaMultipliable ρ a b z₀ z := by
  have hlim : Tendsto (fun γ : G => thetaFactor ρ a b z₀ z γ - 1) cofinite (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_right_iff]
    intro ε _
    have hε : MonoidWithZeroHom.ValueGroup₀.embedding (ε : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)))) ≠ 0 := by
      intro h0
      exact ε.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h0.trans (map_zero _).symm))
    filter_upwards [CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt ϖ ρ hρ n
      ha hb hz₀ _ hε] with γ hγ
    exact (Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).2 (hγ z hz)
  have h := Valued.multipliable_one_add_of_tendsto_cofinite_zero (fun γ : G => thetaFactor ρ a b z₀ z γ - 1) hlim
  rw [ThetaMultipliable]
  convert h using 1
  funext γ
  ring

end S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid (solution)
