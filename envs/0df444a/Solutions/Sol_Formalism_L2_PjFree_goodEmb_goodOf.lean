-- Prove2me | solution 1 for Formalism.L2.PjFree.goodEmb_goodOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:42.548682+00:00
-- url     : https://prove2.me/submissions/0810517e-c8d0-419a-ad15-769edc807231

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
namespace Formalism.L2.PjFree
theorem _root_.solution (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with hσ
  · exact hσ
  · have hx : ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ) ^ 2 + ((H.d : ℕ) : c.F) = 0 := by
      apply Subtype.ext
      have e : (((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
      push_cast [e]
      rw [H.sqrt_neg_disc_sq]
      ring
    have hy : (σ ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ)) ^ 2 = H.rt0 ^ 2 := by
      have h0 := congrArg σ hx
      rw [map_add, map_pow, map_natCast, map_zero] at h0
      rw [H.sqrt_neg_disc_sq]
      linear_combination h0
    have hre : H.rt0.re = 0 := by
      have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
      have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
      simp [sq] at h1 h2
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.mpr H.d_prime.pos
      have e2 : H.rt0.re * H.rt0.im = 0 := by linear_combination h2 / 2
      have e3 : H.rt0.re ^ 4 = -(H.d * H.rt0.re ^ 2) := by
        linear_combination (H.rt0.re ^ 2) * h1 + (H.rt0.re * H.rt0.im) * e2
      have h4 : H.rt0.re ^ 4 ≤ 0 := by
        rw [e3]
        exact neg_nonpos.mpr (mul_nonneg hd.le (sq_nonneg _))
      have h5 : H.rt0.re ^ 4 = 0 := le_antisymm h4 (by positivity)
      exact (pow_eq_zero_iff (by norm_num)).mp h5
    have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
      apply Complex.ext <;> simp [hre]
    unfold GoodEmb at hσ ⊢
    simp only [RingHom.comp_apply] at hσ ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
    · exact absurd h hσ
    · rw [h, map_neg, hconj, neg_neg]
end Formalism.L2.PjFree
