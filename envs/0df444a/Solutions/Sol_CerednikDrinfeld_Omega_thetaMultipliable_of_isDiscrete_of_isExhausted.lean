-- Prove2me | solution 1 for CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/425e07a4-3c3c-59bd-af80-7f7553614d39

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    ThetaMultipliable ρ a b z₀ z := by
  obtain ⟨na, hna⟩ := hex a ha
  obtain ⟨nb, hnb⟩ := hex b hb
  obtain ⟨n₀, hn₀⟩ := hex z₀ hz₀
  obtain ⟨nz, hnz⟩ := hex z hz
  set N := max (max na nb) (max n₀ nz) with hN
  have hmono := affinoid_mono ϖ
  exact CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_mem_affinoid ϖ ρ hρ N
    (hmono (le_trans (le_max_left _ _) (le_max_left _ _)) hna)
    (hmono (le_trans (le_max_right _ _) (le_max_left _ _)) hnb)
    (hmono (le_trans (le_max_left _ _) (le_max_right _ _)) hn₀)
    (hmono (le_trans (le_max_right _ _) (le_max_right _ _)) hnz)

end S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted (solution)
