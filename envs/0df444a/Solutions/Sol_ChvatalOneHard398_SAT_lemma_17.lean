-- Prove2me | solution 1 for ChvatalOneHard398.SAT.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:00:01.885684+00:00
-- url     : https://prove2.me/submissions/d0a23f81-ad5a-4522-bfe4-96992f91c77d

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Geometry

namespace ChvatalOneHard398.SAT
open CombOpt.ChvatalRank
open Matrix
open scoped BigOperators

private noncomputable def liftCoeff {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (a : Fin (n + k) → ℝ) : Fin n → ℝ :=
  fun i => a (Fin.castAdd k i) + ∑ j, a (Fin.natAdd n j) * (A j i : ℝ)

private noncomputable def liftOffset {n k : ℕ} (b : Fin k → ℤ)
    (a : Fin (n + k) → ℝ) : ℝ :=
  ∑ j, a (Fin.natAdd n j) * (b j : ℝ)

private lemma affineLift_injective {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) : Function.Injective (affineLift A b) := by
  intro x y h
  funext i
  have hi := congrFun h (Fin.castAdd k i)
  simpa [affineLift] using hi

private lemma affineLift_integral_iff {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) (x : Fin n → ℝ) :
    IsIntegralVector (affineLift A b x) ↔ IsIntegralVector x := by
  constructor
  · intro h i
    have hi := h (Fin.castAdd k i)
    simpa [affineLift] using hi
  · intro h
    choose z hz using h
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      refine ⟨z j, ?_⟩
      simp [affineLift, hz]
    · intro j
      refine ⟨∑ l, A j l * z l + b j, ?_⟩
      simp [affineLift, hz]

private lemma dot_affineLift {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) (a : Fin (n + k) → ℝ) (x : Fin n → ℝ) :
    a ⬝ᵥ affineLift A b x = liftCoeff A a ⬝ᵥ x + liftOffset b a := by
  classical
  simp only [dotProduct, affineLift, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    liftCoeff, liftOffset]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have hcomm :
      (∑ j : Fin k, ∑ i : Fin n, a (Fin.natAdd n j) * ((A j i : ℝ) * x i)) =
      ∑ i : Fin n, ∑ j : Fin k, (a (Fin.natAdd n j) * (A j i : ℝ)) * x i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcomm]
  ring

private noncomputable def affineLiftLinear {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + k) → ℝ) where
  toFun := affineLift A 0
  map_add' x y := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [affineLift]
    · intro j
      simp [affineLift, mul_add, Finset.sum_add_distrib, add_comm, add_left_comm]
  map_smul' r x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [affineLift]
    · intro j
      simp [affineLift, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

private noncomputable def affineLiftAffine {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) : (Fin n → ℝ) →ᵃ[ℝ] (Fin (n + k) → ℝ) :=
  (affineLiftLinear A).toAffineMap + AffineMap.const ℝ (Fin n → ℝ) (affineLift A b 0)

private lemma affineLiftAffine_apply {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) (x : Fin n → ℝ) :
    affineLiftAffine A b x = affineLift A b x := by
  change affineLift A 0 x + affineLift A b 0 = affineLift A b x
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [affineLift]
  · intro j
    simp [affineLift]

private lemma cut_affineLift_iff {n k : ℕ} (P : Set (Fin n → ℝ))
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ)
    (a : Fin (n + k) → ℝ) (ha : IsIntegralVector a) (t : ℝ) :
    IsGomoryChvatalCut (affineLift A b '' P) a t ↔
      IsGomoryChvatalCut P (liftCoeff A a) (t - liftOffset b a) := by
  classical
  have ha0 := ha
  choose z hz using ha
  let q : ℤ := ∑ j, z (Fin.natAdd n j) * b j
  have hq : liftOffset b a = (q : ℝ) := by
    simp [liftOffset, q, hz]
  have hc : IsIntegralVector (liftCoeff A a) := by
    intro i
    refine ⟨z (Fin.castAdd k i) + ∑ j, z (Fin.natAdd n j) * A j i, ?_⟩
    simp [liftCoeff, hz]
  constructor
  · rintro ⟨ha', d, hd, ht⟩
    refine ⟨hc, d - liftOffset b a, ?_, ?_⟩
    · intro x hx
      have h := hd (affineLift A b x) ⟨x, hx, rfl⟩
      rw [dot_affineLift] at h
      linarith
    · rw [ht, hq, Int.floor_sub_intCast]
      push_cast
      rfl
  · rintro ⟨hc', d, hd, ht⟩
    refine ⟨ha0, d + liftOffset b a, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [dot_affineLift]
      have h := hd x hx
      linarith
    · rw [hq, Int.floor_add_intCast]
      push_cast
      rw [← ht, ← hq]
      ring

private noncomputable def embedCoeff {n k : ℕ} (c : Fin n → ℝ) : Fin (n + k) → ℝ :=
  Fin.append c 0

private lemma embedCoeff_integral {n k : ℕ} {c : Fin n → ℝ}
    (hc : IsIntegralVector c) : IsIntegralVector (embedCoeff (k := k) c) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [embedCoeff] using hc j
  · intro j
    exact ⟨0, by simp [embedCoeff]⟩

private lemma liftCoeff_embed {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (c : Fin n → ℝ) : liftCoeff A (embedCoeff (k := k) c) = c := by
  funext i
  simp [liftCoeff, embedCoeff]

private lemma liftOffset_embed {n k : ℕ} (b : Fin k → ℤ) (c : Fin n → ℝ) :
    liftOffset b (embedCoeff (k := k) c) = 0 := by
  simp [liftOffset, embedCoeff]

private lemma dot_embedCoeff {n k : ℕ} (c : Fin n → ℝ) (b : Fin k → ℤ)
    (A : Matrix (Fin k) (Fin n) ℤ) (x : Fin n → ℝ) :
    embedCoeff (k := k) c ⬝ᵥ affineLift A b x = c ⬝ᵥ x := by
  rw [dot_affineLift, liftCoeff_embed, liftOffset_embed, add_zero]

private lemma integral_image {n k : ℕ} (P : Set (Fin n → ℝ))
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    {y | y ∈ affineLift A b '' P ∧ IsIntegralVector y} =
      affineLift A b '' {x | x ∈ P ∧ IsIntegralVector x} := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hi⟩
    exact ⟨x, ⟨hx, (affineLift_integral_iff A b x).mp hi⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (affineLift_integral_iff A b x).mpr hi⟩

private lemma bijOn_affineLift {n k : ℕ} (P : Set (Fin n → ℝ))
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    Set.BijOn (affineLift A b) {x | x ∈ P ∧ IsIntegralVector x}
      {y | y ∈ affineLift A b '' P ∧ IsIntegralVector y} := by
  rw [integral_image]
  exact Set.InjOn.bijOn_image (affineLift_injective A b).injOn

private lemma hull_affineLift {n k : ℕ} (P : Set (Fin n → ℝ))
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    integerHull (affineLift A b '' P) = affineLift A b '' integerHull P := by
  rw [integerHull, integerHull, integral_image]
  have himage : ⇑(affineLiftAffine A b) = affineLift A b := by
    funext x
    exact affineLiftAffine_apply A b x
  rw [← himage, AffineMap.image_convexHull]

private lemma closure_affineLift {n k : ℕ} (P : Set (Fin n → ℝ))
    (hP : IsRationalPolyhedron P)
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    chvatalClosure (affineLift A b '' P) = affineLift A b '' chvatalClosure P := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro c t hct
    have he : IsGomoryChvatalCut (affineLift A b '' P)
        (embedCoeff (k := k) c) t := by
      rcases hct with ⟨hci, d, hd, ht⟩
      refine ⟨embedCoeff_integral hci, d, ?_, ht⟩
      rintro z ⟨u, hu, rfl⟩
      rw [dot_embedCoeff]
      exact hd u hu
    have h := hc (embedCoeff (k := k) c) t he
    rwa [dot_embedCoeff] at h
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro a t hct
    have hci : IsIntegralVector a := hct.1
    have hdown := (cut_affineLift_iff P A b a hci t).mp hct
    have h := hc (liftCoeff A a) (t - liftOffset b a) hdown
    rw [dot_affineLift]
    linarith

end ChvatalOneHard398.SAT

open CombOpt.ChvatalRank
open ChvatalOneHard398.SAT

theorem solution {n k : ℕ} (P : Set (Fin n → ℝ)) (hP : IsRationalPolyhedron P)
    (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ) :
    Set.BijOn (affineLift A b) {x | x ∈ P ∧ IsIntegralVector x}
      {y | y ∈ affineLift A b '' P ∧ IsIntegralVector y} ∧
    integerHull (affineLift A b '' P) = affineLift A b '' integerHull P ∧
    chvatalClosure (affineLift A b '' P) = affineLift A b '' chvatalClosure P := by
  exact ⟨bijOn_affineLift P A b, hull_affineLift P A b, closure_affineLift P hP A b⟩
