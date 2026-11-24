-- Prove2me | solution 1 for Formalism.REAL.commutator_word_operator_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:35.476635+00:00
-- url     : https://prove2.me/submissions/e47c1e66-8238-4ad1-a04b-ab0120167863

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_word_product_zero
import Theorems.Thm_Formalism_REAL_word_product_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    ∀ (j : ℕ) (α : Fin j → Fin n × Fin n), E c d * u1W E α - u1W E α * E c d =
      ∑ i, ((if d = (α i).1 then u1W E (Function.update α i (c, (α i).2)) else 0) -
        (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) else 0)) := by
  intro j
  induction j with
  | zero =>
    intro α
    rw [word_product_zero]
    simp
  | succ j ih =>
    intro α
    have hlast : ∀ v : Fin n × Fin n, u1W E (Function.update α (Fin.last j) v) =
        E v.1 v.2 * u1W E (Fin.init α) := by
      intro v
      rw [word_product_succ]
      simp
    have hcast : ∀ (i : Fin j) (v : Fin n × Fin n), u1W E (Function.update α i.castSucc v) =
        E (α (Fin.last j)).1 (α (Fin.last j)).2 * u1W E (Function.update (Fin.init α) i v) := by
      intro i v
      rw [word_product_succ]
      have hne : Fin.last j ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
      simp [Function.update_apply, hne, Fin.init_update_castSucc]
    have hsplit : E c d * u1W E α - u1W E α * E c d =
        (E c d * E (α (Fin.last j)).1 (α (Fin.last j)).2 -
          E (α (Fin.last j)).1 (α (Fin.last j)).2 * E c d) * u1W E (Fin.init α) +
        E (α (Fin.last j)).1 (α (Fin.last j)).2 *
          (E c d * u1W E (Fin.init α) - u1W E (Fin.init α) * E c d) := by
      rw [word_product_succ E α]
      noncomm_ring
    rw [hsplit, hE c d (α (Fin.last j)).1 (α (Fin.last j)).2, ih (Fin.init α), Finset.mul_sum,
      Fin.sum_univ_castSucc, hlast, hlast]
    rw [add_comm ((_ - _) * u1W E (Fin.init α))]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcast, hcast]
      simp only [Fin.init]
      by_cases h1 : d = (α i.castSucc).1 <;> by_cases h2 : (α i.castSucc).2 = c <;>
        simp [h1, h2, mul_sub]
    · by_cases h1 : d = (α (Fin.last j)).1 <;> by_cases h2 : (α (Fin.last j)).2 = c <;>
        simp [h1, h2, sub_mul]
end Formalism.REAL
