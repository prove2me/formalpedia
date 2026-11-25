-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_unit_heads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:37.011635+00:00
-- url     : https://prove2.me/submissions/80aaa466-3913-4d25-9ecf-be5be3749747

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx12
end Formalism.FourierDecayAlt.P.Jx12
namespace Formalism.FourierDecayAlt.P
private lemma isPSD_comp_of_isPSD_image {X Y : Type} {inst : DecidableEq Y} (F : Finset X) (η : X → Y)
    (k : Y → Y → ℂ) (hk : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun h h' => k (η h) (η h')) := by
  intro a
  have hmap : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y) =
      ∑ p ∈ F.image η, ∑ q ∈ F.image η,
        (∑ x ∈ F.filter (fun x => η x = p), a x) * conj (∑ y ∈ F.filter (fun y => η y = q), a y) *
          k p q := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
  have hk' := hk (fun p => ∑ x ∈ F.filter (fun x => η x = p), a x)
  beta_reduce at hk' ⊢
  rw [key]
  exact hk'
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.TopUnitHeads := by
  intro hAg hN0 K _ _ _ R ψ hLD E α _ m σ u τ₀ η F Θ hm hG hτ hA t
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have h1 := (hLD.selfDual 1).2 R.one_mem
    simpa using h1 r hr
  have h7 := hA.2.2.2.2.2.2 (by
      intro p hp
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
      exact hG h hh) ((u : K) * σ t - τ₀)
  have hmem : ((u : K) * σ t - τ₀ ∈ R) ↔ t ∈ (topSys R ψ σ u τ₀ η Θ).L := by
    show _ ↔ (u : K) * σ t ∈ R
    constructor
    · intro h
      simpa using R.add_mem h hτ
    · intro h
      exact R.sub_mem h hτ
  have hpull := isPSD_comp_of_isPSD_image F η _ h7
  have hF : A5.IsPSD F (fun h h' => (if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
      (topSys R ψ σ u τ₀ η Θ).N t t h h') := by
    intro a
    have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
        (topSys R ψ σ u τ₀ η Θ).N t t x y) =
        ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if (u : K) * σ t - τ₀ ∈ R then A5.N0 R ψ (η x) (η y) else 0) -
          Θ ((u : K) * σ t - τ₀) (η x) (η y)) := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      have hN : (topSys R ψ σ u τ₀ η Θ).N t t x y = Θ ((u : K) * σ t - τ₀) (η x) (η y) := by
        simp [topSys]
      have h1 : A5.N0 R ψ (η x) (η y) = 1 :=
        hN0 K R ψ hψ (η x) (η y) ((hm x hx).trans (hm y hy).symm) (hG x hx) (hG y hy)
      simp only [hN, h1, hmem]
    have hp := hpull a
    beta_reduce at hp ⊢
    rw [e]
    exact hp
  exact ((hAg α F _).1.trans (hAg α F _).2.symm).2 hF
end Formalism.FourierDecayAlt.P
