-- Prove2me | solution 1 for BipHamCount.Deterministic.Fval_det_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:04:13.069684+00:00
-- url     : https://prove2.me/submissions/53d5d728-87f8-480d-aaa8-088329dbde4c

import Theorems.Thm_BipHamCount_Deterministic_lemma_2_3
import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators
namespace BipHamCount.Deterministic

/-- Lemma 2.2 (Cauchy–Binet), p.5, with no dimension restriction.
This includes |K|<|I|, when the right side is empty and det(MN)=0.
The two minor factors use the same increasing order on J. -/
private theorem p2m_cauchyBinet {R : Type*} [CommRing R] (r : ℕ) {K : Type*} [Fintype K] [LinearOrder K]
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



open Finset Polynomial
open scoped Polynomial

private def maskedProduct {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (Z : Finset (Fin m)) :
    Matrix (Fin m) (Fin m) ℤ := fun i j => ∑ z ∈ Z, A i z * B z j

private theorem product_minor {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (Z I : Finset (Fin m)) :
    minor (maskedProduct A B Z) I I = ∑ J ∈ (univ : Finset (Fin m)).powerset.filter
      (fun J => J.card = I.card ∧ J ⊆ Z), minor A I J * minor B J I := by
  classical
  let e := I.orderEmbOfFin rfl
  let M : Matrix (Fin I.card) (Fin m) ℤ := fun i j => A (e i) j
  let N : Matrix (Fin m) (Fin I.card) ℤ := fun i j => if i ∈ Z then B i (e j) else 0
  rw [minor, dif_pos rfl, show squareSub (maskedProduct A B Z) I I rfl = M * N by
    ext i j
    rw [Matrix.mul_apply]
    simp [squareSub,maskedProduct,M,N,e, mul_ite]]
  rw [p2m_cauchyBinet, powersetCard_eq_filter, sum_filter, sum_filter]
  refine sum_congr rfl fun J _ => ?_
  by_cases h : J.card = I.card
  · simp only [h, if_true, true_and, dite_true]
    let f := J.orderEmbOfFin h
    have ha : minor A I J = (M.submatrix id f).det := by simp [minor, h]; rfl
    have hb : minor B J I = (B.submatrix f e).det := by
      rw [minor, dif_pos h.symm, ← Matrix.det_submatrix_equiv_self (finCongr h) (B.submatrix f e)]
      congr 1
    by_cases hs : J ⊆ Z
    · rw [if_pos hs,ha,hb]
      congr 2
      ext i j
      change (if f i ∈ Z then B (f i) (e j) else 0) = _
      exact if_pos (hs (J.orderEmbOfFin_mem h i))
    · rw [if_neg hs]
      obtain ⟨z,hz,hz'⟩ := Finset.not_subset.mp hs
      obtain ⟨i,hi⟩ : ∃ i, f i = z := by
        have : z ∈ Set.range f := by simpa [f, Finset.range_orderEmbOfFin] using hz
        exact this
      have hn : (N.submatrix f id).det = 0 := Matrix.det_eq_zero_of_row_eq_zero i (by
        intro j
        change (if f i ∈ Z then B (f i) (e j) else 0) = 0
        simp [hi,hz'])
      rw [show J.orderEmbOfFin h = f by rfl,hn,mul_zero]
  · simp [h]

private lemma minor_polynomial_C {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (I : Finset (Fin m)) :
    minor (M.map (C : ℤ →+* ℤ[X])) I I = C (minor M I I) := by
  rw [minor, minor, dif_pos rfl, dif_pos rfl, RingHom.map_det]
  rfl

private lemma complement_sum {m : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Finset (Fin m) → R) : ∑ I, f I = ∑ S, f Sᶜ := by
  refine Finset.sum_bij' (fun I _ => Iᶜ) (fun S _ => Sᶜ) ?_ ?_ ?_ ?_ ?_ <;> simp

private lemma diag_product {m : ℕ} (d : Fin m → ℤ) (v : Fin m) (S : Finset (Fin m)) :
    (∏ i ∈ S, if i ≠ v then C (d i) * (Polynomial.X : ℤ[X]) else 0) =
      if v ∉ S then C (∏ i ∈ S, d i) * Polynomial.X ^ S.card else 0 := by
  classical
  rw [Finset.prod_ite_zero]
  by_cases h : v ∈ S
  · simp [h]
  · simp [h, Finset.prod_mul_distrib, map_prod]

private noncomputable def weightMatrix {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (U V : Finset (Fin m)) : Matrix (Fin m) (Fin m) ℤ[X] :=
  Matrix.diagonal (fun i => if i ≠ v then C (w A B U V i) * Polynomial.X else 0) +
    (maskedProduct A B (U ∪ V)ᶜ).map C

private lemma weightMatrix_coeff {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (U V : Finset (Fin m)) (q : ℕ) :
    (weightMatrix A B v U V).det.coeff q = ∑ S : Finset (Fin m),
      if v ∉ S ∧ q = S.card then
        minor (maskedProduct A B (U ∪ V)ᶜ) Sᶜ Sᶜ * ∏ i ∈ S, w A B U V i else 0 := by
  classical
  rw [weightMatrix, lemma_2_3, powerset_univ, complement_sum]
  simp only [compl_compl, finsetSum_coeff, minor_polynomial_C,diag_product]
  refine sum_congr rfl fun S _ => ?_
  by_cases h : v ∈ S
  · simp [h]
  · simp only [h,not_false_eq_true,if_true,true_and,← mul_assoc,← map_mul,coeff_C_mul_X_pow]

private lemma complement_minor_sum {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (Z S : Finset (Fin m)) :
    minor (maskedProduct A B Zᶜ) Sᶜ Sᶜ = ∑ T ∈ (univ : Finset (Fin m)).powerset.filter
      (fun T => T.card = S.card ∧ Z ⊆ T), minor A Sᶜ Tᶜ * minor B Tᶜ Sᶜ := by
  classical
  rw [product_minor, powerset_univ,sum_filter,sum_filter,complement_sum]
  refine sum_congr rfl fun T _ => ?_
  have hs : S.card ≤ m := by simpa using card_le_univ S
  have ht : T.card ≤ m := by simpa using card_le_univ T
  have hc : Tᶜ.card = Sᶜ.card ↔ T.card = S.card := by simp only [card_compl,Fintype.card_fin]; omega
  simp only [hc,compl_le_compl_iff_le]

private lemma Fval_coeff {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (U V : Finset (Fin m)) :
    ∑ q ∈ range (k+1), (-1 : ℤ)^(m-q+1) * (weightMatrix A B v U V).det.coeff q =
      Fval A B v k U V := by
  classical
  simp_rw [weightMatrix_coeff, Finset.mul_sum]
  rw [sum_comm,Fval, sum_filter]
  have hP : (univ.erase v).powerset = (univ : Finset (Finset (Fin m))).filter (fun S => v ∉ S) := by
    ext S
    simp [Finset.subset_erase]
  rw [hP,sum_filter]
  refine sum_congr rfl fun S _ => ?_
  by_cases hs : v ∈ S
  · simp [hs]
  · by_cases hk : S.card ≤ k
    · rw [if_pos hs,if_pos hk, Finset.sum_eq_single_of_mem S.card (by simp; omega)]
      · simp only [hs,not_false_eq_true,eq_self,and_self,if_true,card_compl,Fintype.card_fin]
        rw [complement_minor_sum, Finset.sum_mul, Finset.mul_sum]
        refine sum_congr rfl fun T hT => ?_
        ring
      · intro q _ hq
        simp [hq]
    · simp only [hs,not_false_eq_true, if_true,if_neg hk]
      refine Finset.sum_eq_zero fun q hq => ?_
      have : q ≠ S.card := by have := mem_range.mp hq; omega
      simp [this]
theorem _root_.solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (U V : Finset (Fin m)) :
    let M : Matrix (Fin m) (Fin m) ℤ :=
      fun i j => ∑ z ∈ (U ∪ V)ᶜ, A i z * B z j
    let Q := (Matrix.diagonal (fun i => if i ≠ v then
      Polynomial.C (w A B U V i) * Polynomial.X else 0) + M.map Polynomial.C).det
    ∑ q ∈ Finset.range (k + 1), (-1 : ℤ) ^ (m - q + 1) * Q.coeff q =
      Fval A B v k U V := by
  exact Fval_coeff A B v k U V

end BipHamCount.Deterministic
