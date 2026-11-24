-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:35.153324+00:00
-- url     : https://prove2.me/submissions/283e7ea5-8572-47d8-b2b7-dd038a7ca510

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_D_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SymDMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_collapse
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_core_inv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gC_mul_gI
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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_midD b mu nu J α K := by
  have hT : ∀ I, TMat mu J I =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ (hs.1 _) le_rfl J I
  have hm : ∀ m : ↥(qs_D nu mu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
                qs_mn (qs_gC n) (qs_ext mu J c) (qs_add (qs_D nu mu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D nu mu), qs_gI n (m c) (a c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gI n).transpose b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymDMat n b α β *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymDMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_add_card hnu hmu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gI n).transpose (qs_card_D hnu hmu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; simp only [Matrix.transpose_apply]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b,
      TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D nu mu) → Fin n, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_psD, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core_inv (qs_gC n) (qs_gI n) (qs_gC_mul_gI n) _ _ (qs_D_sub nu mu)]
  · simp only [if_neg h, Finset.sum_const_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
