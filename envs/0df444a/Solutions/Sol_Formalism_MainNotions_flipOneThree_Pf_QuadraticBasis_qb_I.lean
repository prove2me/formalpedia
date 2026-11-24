-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:50.576347+00:00
-- url     : https://prove2.me/submissions/42f973fd-29df-40d5-9cb2-086b574e846e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_unit_of_not_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b : W} (h : w ∣ j a + j b * θ) :
    (p : W) ∣ a ∧ (p : W) ∣ b := by
  have hb : (p : W) ∣ b := by
    by_contra hb
    obtain ⟨u, rfl⟩ := qb_unit_of_not_dvd hpW hb
    apply hθ (-(↑u⁻¹ * a))
    have h0 := Dvd.dvd.mul_left h (j ↑u⁻¹)
    have e : j ↑u⁻¹ * (j a + j ↑u * θ) = θ - j (-(↑u⁻¹ * a)) := by
      have h1 : j ↑u⁻¹ * j ↑u = 1 := by rw [← map_mul]; simp
      rw [map_neg, map_mul]
      linear_combination θ * h1
    rwa [e] at h0
  refine ⟨?_, hb⟩
  by_contra ha
  have hu := (qb_unit_of_not_dvd hpW ha).map j
  obtain ⟨b', rfl⟩ := hb
  have h2 : w ∣ j ((p : W) * b') * θ := by
    rw [map_mul, map_natCast, ← hw2]
    exact ⟨w * j b' * θ, by ring⟩
  have h3 : w ∣ j a := (dvd_add_left h2).1 h
  exact hw.not_isUnit (isUnit_of_dvd_unit h3 hu)
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
