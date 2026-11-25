-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.independence_span_of_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:25.157582+00:00
-- url     : https://prove2.me/submissions/cd5c546a-4957-4951-8553-1d88d7a20d2a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_even_val_add_two

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
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : CoefficientIdentityCondition) : IndependenceSpanCondition := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hAlt g a hbig
  have key : ∀ g' : Fin 2, (Y.raw p).big g' a → (Y.raw p).big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, (Y.raw p).big 1 b ↔ ¬ (Y.raw p).big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ (Y.raw p).big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // (Y.raw p).ty (1 - g) q = a + 2} = (Y.raw p).j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := h C V O dd Y d I p hrk H hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun r => M (σ r).1, fun w x hg hV => ?_⟩
  obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
  refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
  have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
    rw [← Finset.sum_filter_of_ne (p := fun q' => (Y.raw p).ty (1 - g) q' = a + 2)
      (fun q' _ hne => by
        by_contra hq
        exact hne (by rw [hsupp q' hq, zero_mul]))]
    rw [Finset.sum_subtype (Finset.univ.filter fun q' => (Y.raw p).ty (1 - g) q' = a + 2)
      (p := fun q' => (Y.raw p).ty (1 - g) q' = a + 2) (fun q' => by simp)]
    exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
  rw [← hsum]
  exact hc1 q
end Formalism.L2.FormalSeriesBounds
