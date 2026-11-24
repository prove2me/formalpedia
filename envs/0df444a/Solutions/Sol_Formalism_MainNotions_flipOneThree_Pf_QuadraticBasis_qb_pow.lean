-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:51.39712+00:00
-- url     : https://prove2.me/submissions/b147f644-02b2-4120-9c58-40de330edb75

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_step

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
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (m : ℕ) : ∀ {a b c d : W},
    j a + j b * θ + j c * w + j d * θ * w = 0 →
    (p : W) ^ m ∣ a ∧ (p : W) ^ m ∣ b ∧ (p : W) ^ m ∣ c ∧ (p : W) ^ m ∣ d := by
  induction m with
  | zero => intro a b c d _; simp
  | succ m ih =>
    intro a b c d h
    obtain ⟨a', b', c', d', rfl, rfl, rfl, rfl, h'⟩ := qb_step j w θ hpW hw2 hw hθ h
    obtain ⟨ha, hb, hc, hd⟩ := ih h'
    simp only [pow_succ']
    exact ⟨mul_dvd_mul_left _ ha, mul_dvd_mul_left _ hb, mul_dvd_mul_left _ hc, mul_dvd_mul_left _ hd⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
