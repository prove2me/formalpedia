-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:19.131893+00:00
-- url     : https://prove2.me/submissions/d4c5b28a-e353-4e5a-b369-f34dc6d27a75

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_collapse
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_iff_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
open Classical
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_mid b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ (hs.1 _) le_rfl K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D mu nu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((E c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D mu nu) → Fin n,
        if (∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_add (qs_D mu nu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_ps, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D mu nu) (qs_ext mu J) (qs_ext nu K') a
    by_cases h : (∀ c : ↥(qs_D mu nu), a c ∈ qs_ext nu K' c.1) ∧ qs_ext mu J = qs_rem (qs_D mu nu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.1 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_add_card hmu hnu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    have h3 : ∀ c : ↥(qs_D mu nu), (qs_add (qs_D mu nu) (qs_ext mu J) a c.1).erase (a c) = qs_ext mu J c.1 := by
      intro c; rw [qs_add_mem, Finset.erase_insert (h c)]
    simp only [h3]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
