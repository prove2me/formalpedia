-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:18.481799+00:00
-- url     : https://prove2.me/submissions/864196a6-c65a-4383-a9fc-d08d54ccf9c7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_I

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
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) :
    ∃ a' b' c' d' : W, a = p * a' ∧ b = p * b' ∧ c = p * c' ∧ d = p * d' ∧
      j a' + j b' * θ + j c' * w + j d' * θ * w = 0 := by
  have hw0 : w ≠ 0 := hw.ne_zero
  have h1 : w ∣ j a + j b * θ := ⟨-(j c + j d * θ), by linear_combination h⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h1
  simp only [map_mul, map_natCast, ← hw2] at h
  have h2 : w * (w * (j a' + j b' * θ) + (j c + j d * θ)) = 0 := by linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_left hw0
  have h4 : w ∣ j c + j d * θ := ⟨-(j a' + j b' * θ), by linear_combination h3⟩
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h4
  simp only [map_mul, map_natCast, ← hw2] at h3
  refine ⟨a', b', c', d', rfl, rfl, rfl, rfl, ?_⟩
  have h5 : w * (j a' + j b' * θ + j c' * w + j d' * θ * w) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h5).resolve_left hw0
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
