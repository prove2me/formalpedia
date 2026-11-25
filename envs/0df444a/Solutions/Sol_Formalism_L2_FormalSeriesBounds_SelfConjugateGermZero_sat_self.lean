-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.sat_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:17.652372+00:00
-- url     : https://prove2.me/submissions/429608cd-6017-4140-841b-a2f15f996af6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_gm_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, hsum⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c', ?_, ?_⟩
  · intro x c'
    have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm (p.ty0 c' + p.hd) x.1 (g + 1)) := gm_int Y p _ _ _
    have h2 : (0 : WithTop ℝ) ≤ V.v (w0 x.2 c') := hw0 x.2 c'
    show (0 : WithTop ℝ) ≤ V.v (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c')
    rw [AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro c c'
    have key : ∀ x : Fin 2 × Fin dd,
        (Y.rawSelf p).u g c x * (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c') =
          (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (g + 1)) * (p.e c x.2 * w0 x.2 c') := by
      intro x
      show p.gm (p.ty0 c) x.1 g * p.e c x.2 * (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c') = _
      ring
    simp only [key]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hsum c c']
    split_ifs with hcc
    · subst hcc
      simp only [mul_one]
      have hh := p.gm_hyp (p.ty0 c) (g + 1) g
      rw [if_neg (by fin_cases g <;> decide)] at hh
      rw [← hh]
      exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
    · simp
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
