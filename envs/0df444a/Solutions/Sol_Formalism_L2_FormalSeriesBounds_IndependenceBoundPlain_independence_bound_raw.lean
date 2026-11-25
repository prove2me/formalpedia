-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.IndependenceBoundPlain.independence_bound_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:48.972599+00:00
-- url     : https://prove2.me/submissions/65a44990-4f79-4223-8399-8444e8c10893

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentitySelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_even_val_add_two
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_independence_bound_of_span_raw


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
open Formalism.L2.FormalSeriesBounds.IndependenceBoundPlain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.IndependenceBoundPlain
theorem _root_.solution [IsAlgClosed C] [NeZero d] (hrk : X.RankHyp) (H : ∀ g, X.CartHyp V g) (hR2 : RawChart.RankMaximalCondition H)
    (hcoef : PlainCoefficientIdentity X H) : RawChart.IndependenceBoundCondition H := by
  intro hAlt g a hbig N w x hg hV hind
  have key : ∀ g' : Fin 2, X.big g' a → X.big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ X.big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // X.ty (1 - g) q = a + 2} = X.j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := hcoef hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  have hspan : ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * M (σ r).1 q) := by
    intro w x hg hV
    obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
    refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
    have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
      rw [← Finset.sum_filter_of_ne (p := fun q' => X.ty (1 - g) q' = a + 2)
        (fun q' _ hne => by
          by_contra hq
          exact hne (by rw [hsupp q' hq, zero_mul]))]
      rw [Finset.sum_subtype (Finset.univ.filter fun q' => X.ty (1 - g) q' = a + 2)
        (p := fun q' => X.ty (1 - g) q' = a + 2) (fun q' => by simp)]
      exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
    rw [← hsum]
    exact hc1 q
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) (fun r => M (σ r).1) hspan
    N w x hg hV hind
end Formalism.L2.FormalSeriesBounds.IndependenceBoundPlain
