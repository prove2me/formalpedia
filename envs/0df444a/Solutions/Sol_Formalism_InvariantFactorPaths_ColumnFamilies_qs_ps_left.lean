-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:38.875816+00:00
-- url     : https://prove2.me/submissions/24a523c1-8a0a-46d3-a669-fdccf1ab0bf9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_D_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SymMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_collapse
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_core
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_sym


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
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_mid b mu nu J α K := by
  have hT : ∀ I, TMat mu J I = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ le_rfl (hs.1 0) J I
  have hm : ∀ m : ↥(qs_D mu nu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0), qs_mn (qs_gC n) (qs_ext mu J c) (qs_rem (qs_D mu nu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D mu nu), qs_gC n (a c) (m c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gC n) b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymMat n b α β *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_rem_card hmu hnu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gC n) (qs_card_D hmu hnu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D mu nu) → Fin n, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_ps, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core (qs_gC n) _ _ (qs_D_sub mu nu)]
  · simp only [if_neg h, Finset.sum_const_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
