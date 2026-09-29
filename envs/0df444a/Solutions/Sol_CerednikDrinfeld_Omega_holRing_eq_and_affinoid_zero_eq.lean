-- Prove2me | solution 1 for CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d048d781-e01f-5c43-93c7-b4038fc192e4

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid mem_affinoid_iff' IsHolOn holRing"
namespace HolRingCofinal
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem IsHolOn.comp_inclusion {S S' : Set K} (h : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (f ∘ Set.inclusion h) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (h hz), ⟨b, fun k z => hb k (Set.inclusion h z)⟩, hlim.comp (Set.inclusion h)⟩

theorem PseudoUniformizer.ϖ_ne_zero (ϖ : PseudoUniformizer K₀ K) : ϖ.ϖ ≠ 0 := by
  intro h
  have := ϖ.pos
  rw [h, map_zero, Valuation.map_zero] at this
  exact lt_irrefl _ this

theorem exists_affinoid_subset_affinoid (ϖ ϖ' : PseudoUniformizer K₀ K) (n : ℕ) :
    ∃ m : ℕ, affinoid ϖ' n ⊆ affinoid ϖ m := by
  obtain ⟨N, hN, -⟩ := ϖ.scale (ϖ'.ϖ ^ n) (pow_ne_zero n (PseudoUniformizer.ϖ_ne_zero ϖ'))
  rw [map_pow, Valuation.map_pow] at hN

  have hinv : (Valued.v (algebraMap K₀ K ϖ'.ϖ))⁻¹ ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ N := by
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos ϖ.pos N) hN
  refine ⟨N, fun z hz => ?_⟩
  rw [mem_affinoid_iff'] at hz ⊢
  exact ⟨hz.1.trans hinv, fun a => hN.trans (hz.2 a)⟩

theorem holRing_le_holRing (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ ≤ holRing ϖ' := by
  intro f hf n
  obtain ⟨m, hm⟩ := exists_affinoid_subset_affinoid ϖ ϖ' n
  exact IsHolOn.comp_inclusion hm (hf m)

end CerednikDrinfeld.Omega.HolRingCofinal

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid mem_affinoid_iff' IsHolOn holRing"
namespace HolRingCofinal
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

theorem affinoid_zero_eq {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ ϖ' : PseudoUniformizer K₀ K) : affinoid ϖ 0 = affinoid ϖ' 0 := by
  ext z
  rw [mem_affinoid_iff', mem_affinoid_iff']
  simp only [pow_zero]

end CerednikDrinfeld.Omega.HolRingCofinal

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ = holRing ϖ' ∧ affinoid ϖ 0 = affinoid ϖ' 0 := by
  exact ⟨le_antisymm (CerednikDrinfeld.Omega.HolRingCofinal.holRing_le_holRing ϖ ϖ')
    (CerednikDrinfeld.Omega.HolRingCofinal.holRing_le_holRing ϖ' ϖ),
    CerednikDrinfeld.Omega.HolRingCofinal.affinoid_zero_eq ϖ ϖ'⟩

end S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq (solution)
