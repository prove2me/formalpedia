-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_count_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:46.197692+00:00
-- url     : https://prove2.me/submissions/789f0f80-039a-41a6-b056-8039dc7b66b9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
private theorem lt_colH_iff_le_of_dominant {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Iio t := by
      intro m hm
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      linarith
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hsub : Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [mem_Iic] at hm
      simp only [mem_filter, mem_univ, true_and]
      exact le_trans h (hmu hm)
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) (t : ℕ) :
    (univ.filter fun κ : {κ // 0 < sz κ} => t < sz κ.1).card =
      (univ.filter fun x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu) =>
        t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x).card := by
  by_cases htn : t < n
  · have h1 : (univ.filter fun κ : {κ // 0 < sz κ} => t < sz κ.1).card =
        (univ.filter fun κ : Fin K => t < sz κ).card := by
      refine Finset.card_bij (fun κ _ => κ.1) ?_ ?_ ?_
      · intro κ hκ
        simpa using hκ
      · intro a _ b _ h
        exact Subtype.ext h
      · intro κ hκ
        simp only [mem_filter, mem_univ, true_and] at hκ
        exact ⟨⟨κ, by omega⟩, by simpa using hκ, rfl⟩
    have h2 := hshape ⟨t, htn⟩
    unfold Formalism.GradedWeylDivisibility.shapeDeg at h2
    simp only [Fin.val_mk] at h2
    have hle : mu ⟨t, htn⟩ ≤ mu 0 := hmu (by rw [Fin.le_def]; simp)
    have hlast : mu (lastIdx n) ≤ mu ⟨t, htn⟩ := hmu (by rw [Fin.le_def]; simp [lastIdx]; omega)
    have key : (univ.filter fun c : ↥(TCols mu) => t < colH mu c.1).card =
        (Ioc (mu (lastIdx n)) (mu ⟨t, htn⟩)).card := by
      refine Finset.card_bij (fun c _ => c.1) ?_ ?_ ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        have hc2 := c.2
        simp only [TCols, mem_Ioc] at hc2
        rw [mem_Ioc]
        exact ⟨hc2.1, (lt_colH_iff_le_of_dominant hmu ⟨t, htn⟩ c.1).mp hc⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro c hc
        rw [mem_Ioc] at hc
        refine ⟨⟨c, by simp only [TCols, mem_Ioc]; exact ⟨hc.1, hc.2.trans hle⟩⟩, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        exact (lt_colH_iff_le_of_dominant hmu ⟨t, htn⟩ c).mpr hc.2
    have hR : (univ.filter fun x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu) =>
        t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x).card =
        (mu (lastIdx n) + k).toNat + (univ.filter fun c : ↥(TCols mu) => t < colH mu c.1).card := by
      rw [card_filter, card_filter, Fintype.sum_sum_type]
      simp [htn]
      exact (card_filter _ _).symm
    rw [h1, hR, key, Int.card_Ioc]
    omega
  · push_neg at htn
    have a : ∀ κ : {κ // 0 < sz κ}, ¬ t < sz κ.1 := by
      intro κ
      have := hsz κ.1
      omega
    have b : ∀ x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu),
        ¬ t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x := by
      intro x
      cases x with
      | inl _ =>
        simp only [Sum.elim_inl]
        omega
      | inr c =>
        simp only [Sum.elim_inr]
        have : colH mu c ≤ n := by
          unfold colH
          exact (card_filter_le _ _).trans (by simp)
        omega
    rw [card_eq_zero.mpr (filter_false_of_mem fun κ _ => a κ),
      card_eq_zero.mpr (filter_false_of_mem fun x _ => b x)]
end Formalism.InvariantFactorPaths.ColumnFamilies
