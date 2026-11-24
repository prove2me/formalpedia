-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.minor_bound_extra_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:05.135086+00:00
-- url     : https://prove2.me/submissions/1fb75eba-7d4d-43ef-a947-5170e72a9ba5

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_of_minorsDvd
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_submatrix_det_not_dvd_of_mul_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_not_pow_sum_dvd_prod
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_det_sigma_reindexed_square_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : MinorBoundExtra := by
  intro R _ _ π n h c Φ b ch al ν hπ hΦ hsub hch hoth hdvd
  generalize hI : Finset.univ.image b = I at hsub hoth hdvd ⊢
  have hloc : ∀ r : ↥I, ∃ (t v : ℕ) (F G : Fin t → {j // b j = r.1}),
      t = (if r.1 ∈ ch then 1 else ν r.1) ∧ v = (if r.1 ∈ ch then al r.1 else ν r.1 * h) ∧
      ¬ π ^ (v + 1) ∣ ((Φ.toSquareBlock b r.1).submatrix F G).det := by
    intro r
    by_cases hr : r.1 ∈ ch
    · obtain ⟨s, hs, u, hu⟩ := hch r.1 hr
      refine ⟨1, al r.1, fun _ => ⟨s, (hs s).2 rfl⟩, fun _ => ⟨s, (hs s).2 rfl⟩,
        (if_pos hr).symm, (if_pos hr).symm, ?_⟩
      rw [Matrix.det_fin_one]
      show ¬ π ^ (al r.1 + 1) ∣ Φ s s
      rw [hu, pow_succ, mul_comm (π ^ al r.1) π,
        mul_dvd_mul_iff_right (pow_ne_zero _ hπ.ne_zero)]
      exact fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd u.isUnit)
    · obtain ⟨⟨M', hM'⟩, hν⟩ := hoth r.1 (Finset.mem_sdiff.2 ⟨r.2, hr⟩)
      have hcard : Fintype.card (Fin (ν r.1)) ≤ Fintype.card {j // b j = r.1} := by
        rw [Fintype.card_fin, Fintype.card_subtype]; exact hν
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      have hx : ¬ π ^ (Fintype.card (Fin (ν r.1)) * h + 1) ∣
          π ^ (Fintype.card (Fin (ν r.1)) * h) := by
        rw [pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]; omega
      obtain ⟨F, G, hFG⟩ := exists_submatrix_det_not_dvd_of_mul_eq π h _ M' e e.injective hM' hx
      rw [Fintype.card_fin] at hFG
      exact ⟨ν r.1, ν r.1 * h, F, G, (if_neg hr).symm, (if_neg hr).symm, hFG⟩
  choose tt vv F G htt hvv hnd using hloc
  have hBT : (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
      (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).BlockTriangular
        (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1) := by
    intro x y hxy
    refine hΦ ?_
    show b (G y.1 y.2).1 < b (F x.1 x.2).1
    rw [(F x.1 x.2).2, (G y.1 y.2).2]
    exact hxy
  have hnd' : ¬ π ^ (∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1),
      (if a ∈ ch then al a else ν a * h) + 1) ∣
      (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).det := by
    rw [hBT.det]
    refine not_pow_sum_dvd_prod hπ _ _ _ ?_
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    rw [det_sigma_reindexed_square_block Φ b I tt F G x.1]
    have h3 := hnd x.1
    rwa [hvv x.1] at h3
  have hle : ∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1),
      (if a ∈ ch then al a else ν a * h) ≤ ∑ a ∈ I, (if a ∈ ch then al a else ν a * h) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    exact x.1.2
  have hsumv : ∑ a ∈ I, (if a ∈ ch then al a else ν a * h) =
      ∑ r ∈ ch, al r + (∑ r ∈ I \ ch, ν r) * h := by
    rw [← Finset.sum_sdiff hsub, add_comm, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun r hr => if_pos hr
    · exact Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2
  have hcardT : Fintype.card (Σ r : ↥I, Fin (tt r)) = ch.card + ∑ r ∈ I \ ch, ν r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, htt]
    rw [Finset.sum_coe_sort I (fun r => if r ∈ ch then 1 else ν r), ← Finset.sum_sdiff hsub,
      add_comm]
    congr 1
    · rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun r hr => if_pos hr
    · exact Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2
  have hall := dvd_det_submatrix_of_minorsDvd (π ^ c) Φ hdvd
  have h1 := hall
    (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1
      ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
    (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1
      ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
  have h2 : Φ.submatrix
      (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1
        ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
      (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1
        ((Fintype.equivFinOfCardEq hcardT).symm i).2).1) =
      (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).submatrix
          (Fintype.equivFinOfCardEq hcardT).symm (Fintype.equivFinOfCardEq hcardT).symm := rfl
  rw [h2, Matrix.det_submatrix_equiv_self] at h1
  by_contra hc
  rw [not_le, ← hsumv] at hc
  exact hnd' (dvd_trans (pow_dvd_pow π (Nat.succ_le_of_lt (lt_of_le_of_lt hle hc))) h1)
end Formalism.CohomologicalDescent.HeightDescentMinors
