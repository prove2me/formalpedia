-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:36.610383+00:00
-- url     : https://prove2.me/submissions/c8645dbc-0df9-4363-8c2e-04a3e50c5c93

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_collapse
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_iff_add
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_mem


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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_midD b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ le_rfl (hs.1 0) K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D nu mu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (E c.1) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D nu mu) → Fin n,
        if (∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_rem (qs_D nu mu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_psD, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D nu mu) (qs_ext nu K') (qs_ext mu J) a
    by_cases h : (∀ c : ↥(qs_D nu mu), a c ∉ qs_ext nu K' c.1) ∧
        qs_ext mu J = qs_add (qs_D nu mu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.2 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_rem_card hnu hmu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    simp only [qs_rem_mem]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
