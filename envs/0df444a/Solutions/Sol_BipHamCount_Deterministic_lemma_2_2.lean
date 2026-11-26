-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:53:23.485056+00:00
-- url     : https://prove2.me/submissions/a2b0db65-e31d-461a-829b-4f1ad935a188

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators
namespace BipHamCount.Deterministic

/-- Lemma 2.2 (Cauchy–Binet), p.5, with no dimension restriction.
This includes |K|<|I|, when the right side is empty and det(MN)=0.
The two minor factors use the same increasing order on J. -/
theorem p2m_cauchyBinet {R : Type*} [CommRing R] (r : ℕ) {K : Type*} [Fintype K] [LinearOrder K]
    (M : Matrix (Fin r) K R) (N : Matrix K (Fin r) R) :
    (M * N).det = ∑ J ∈ (Finset.univ : Finset K).powersetCard r,
      if h : J.card = r then (M.submatrix id (J.orderEmbOfFin h)).det * (N.submatrix (J.orderEmbOfFin h) id).det else 0 := by
  classical
  have hexp : (M * N).det = ∑ f : Fin r → K, (∏ i, M i (f i)) * (N.submatrix f id).det := by
    have hrow : (fun i => (M * N) i) = fun i => ∑ k, M i k • N k := by
      funext i j
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply]
    show Matrix.detRowAlternating (fun i => (M * N) i) = _
    rw [hrow]
    have := (Matrix.detRowAlternating (R := R) (n := Fin r)).toMultilinearMap.map_sum (g := fun i k => M i k • N k)
    rw [show (Matrix.detRowAlternating (fun i => ∑ k, M i k • N k) : R)
        = (Matrix.detRowAlternating (R := R) (n := Fin r)).toMultilinearMap (fun i => ∑ k, M i k • N k) from rfl, this]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [MultilinearMap.map_smul_univ]
    rfl
  have hzero : ∀ f : Fin r → K, ¬ Function.Injective f → (N.submatrix f id).det = 0 := by
    intro f hf
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    exact Matrix.det_zero_of_row_eq hne (funext fun j => by simp [Matrix.submatrix_apply, hab])
  rw [hexp, ← Finset.sum_filter_of_ne (p := fun f : Fin r → K => Function.Injective f)
    (fun f _ h => by
      by_contra hf
      exact h (by rw [hzero f hf, mul_zero]))]
  have hmaps : ∀ f ∈ (Finset.univ.filter fun f : Fin r → K => Function.Injective f),
      Finset.univ.image f ∈ (Finset.univ : Finset K).powersetCard r := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ hf.2, Finset.card_univ, Fintype.card_fin]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have h : J.card = r := (Finset.mem_powersetCard.1 hJ).2
  rw [dif_pos h]
  set e := J.orderEmbOfFin h with he
  have hbij : ∑ f ∈ (Finset.univ.filter fun f : Fin r → K => Function.Injective f).filter (fun f => Finset.univ.image f = J),
        (∏ i, M i (f i)) * (N.submatrix f id).det
      = ∑ σ : Equiv.Perm (Fin r), (∏ i, M i (e (σ i))) * (N.submatrix (fun i => e (σ i)) id).det := by
    symm
    refine Finset.sum_bij (fun σ _ => fun i => e (σ i)) ?_ ?_ ?_ ?_
    · intro σ _
      rw [Finset.mem_filter, Finset.mem_filter]
      have hinj : Function.Injective fun i => e (σ i) := e.injective.comp σ.injective
      refine ⟨⟨Finset.mem_univ _, hinj⟩, ?_⟩
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
        exact J.orderEmbOfFin_mem h _
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, h]
    · intro σ _ τ _ hst
      exact Equiv.ext fun i => e.injective (congrFun hst i)
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_filter] at hf
      obtain ⟨⟨_, hinj⟩, himg⟩ := hf
      have hmem : ∀ i, ∃ k, e k = f i := by
        intro i
        have : f i ∈ J := himg ▸ Finset.mem_image_of_mem f (Finset.mem_univ i)
        have hr : f i ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact this
        exact hr
      choose g hg using hmem
      have ginj : Function.Injective g := fun a b hab => hinj (by rw [← hg a, ← hg b, hab])
      refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj), Finset.mem_univ _, ?_⟩
      funext i; exact hg i
    · intro σ _; rfl
  rw [hbij]
  have hdetN : ∀ σ : Equiv.Perm (Fin r), (N.submatrix (fun i => e (σ i)) id).det
      = (Equiv.Perm.sign σ : R) * (N.submatrix e id).det := by
    intro σ
    have : N.submatrix (fun i => e (σ i)) id = (N.submatrix e id).submatrix σ id := rfl
    rw [this, Matrix.det_permute]
  simp only [hdetN]
  have hM : (M.submatrix id e).det = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : R) * ∏ i, M i (e (σ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hM, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by ring


theorem _root_.solution {R : Type*} [CommRing R] (r : ℕ) {K : Type*}
    [Fintype K] [LinearOrder K] (M : Matrix (Fin r) K R) (N : Matrix K (Fin r) R) :
    (M * N).det = ∑ J ∈ (Finset.univ : Finset K).powerset.filter (fun J => J.card = r),
      minor M Finset.univ J * minor N J Finset.univ := by
  classical
  rw [p2m_cauchyBinet r M N]
  have hset : (Finset.univ : Finset K).powerset.filter (fun J => J.card = r) = (Finset.univ : Finset K).powersetCard r := by
    rw [Finset.powersetCard_eq_filter]
  rw [hset]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have h : J.card = r := (Finset.mem_powersetCard.1 hJ).2
  have hu : (Finset.univ : Finset (Fin r)).card = r := by simp
  have key : ∀ (c : (Finset.univ : Finset (Fin r)).card = J.card → True), True := fun _ => trivial
  rw [dif_pos h]
  have e1 : ∀ i : Fin (Finset.univ : Finset (Fin r)).card, (Finset.univ : Finset (Fin r)).orderEmbOfFin rfl i = finCongr hu i := by
    intro i
    have := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin r))) (h := rfl) (f := fun i => finCongr hu i)
      (fun _ => Finset.mem_univ _) (fun a b hab => hab)
    exact (congrFun this i).symm
  have e2 : ∀ (T : J.card = (Finset.univ : Finset (Fin r)).card) (i : Fin (Finset.univ : Finset (Fin r)).card),
      J.orderEmbOfFin T i = J.orderEmbOfFin h (finCongr hu i) := by
    intro T i
    have := Finset.orderEmbOfFin_unique (s := J) (h := T) (f := fun i => J.orderEmbOfFin h (finCongr hu i))
      (fun _ => J.orderEmbOfFin_mem h _) (fun a b hab => (J.orderEmbOfFin h).strictMono hab)
    exact (congrFun this i).symm
  have c1 : J.card = (Finset.univ : Finset (Fin r)).card := by rw [h, hu]
  have m1 : BipHamCount.Deterministic.minor M Finset.univ J = (M.submatrix id (J.orderEmbOfFin h)).det := by
    unfold BipHamCount.Deterministic.minor
    rw [dif_pos c1, ← Matrix.det_submatrix_equiv_self (finCongr hu) (M.submatrix id (J.orderEmbOfFin h))]
    congr 1
    ext i j
    simp only [BipHamCount.Deterministic.squareSub, Matrix.submatrix_apply, id_eq]
    rw [e1, e2]
  have c2 : (Finset.univ : Finset (Fin r)).card = J.card := c1.symm
  have m2 : BipHamCount.Deterministic.minor N J Finset.univ = (N.submatrix (J.orderEmbOfFin h) id).det := by
    unfold BipHamCount.Deterministic.minor
    rw [dif_pos c2, ← Matrix.det_submatrix_equiv_self (finCongr h) (N.submatrix (J.orderEmbOfFin h) id)]
    congr 1
    ext i j
    simp only [BipHamCount.Deterministic.squareSub, Matrix.submatrix_apply, id_eq]
    congr 1
    have := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin r))) (h := c2) (f := fun j => finCongr (h.symm ▸ rfl : J.card = r) j)
      (fun _ => Finset.mem_univ _) (fun a b hab => hab)
    exact (congrFun this j).symm
  rw [m1, m2]


end BipHamCount.Deterministic

