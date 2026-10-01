-- Prove2me | solution 1 for FoundationsML.Kernels.pds_closure_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:14:33.856037+00:00
-- url     : https://prove2.me/submissions/30d977e3-52a7-4f80-a923-dedd2aa35211

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS

set_option autoImplicit false

namespace P6510ec44

open FoundationsML.Kernels

theorem isPDS_iff {X : Type} (K : X → X → ℝ) :
    IsPDS K ↔ (Matrix.of K).PosSemidef := by
  classical
  constructor
  · intro h
    refine ⟨?_, fun x => ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, h.1 j i]
    · have := h.2 x.support (⇑x)
      refine le_of_le_of_eq this ?_
      simp only [Finsupp.sum, star_trivial, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  · intro hM
    refine ⟨fun x y => ?_, fun S c => ?_⟩
    · have := congrFun (congrFun hM.1 x) y
      simpa [Matrix.conjTranspose_apply] using this.symm
    · let x : X →₀ ℝ := Finsupp.onFinset S (fun i => if i ∈ S then c i else 0) (by
        intro a ha
        by_contra hS
        simp [hS] at ha)
      have hx : x.support ⊆ S := Finsupp.support_onFinset_subset
      have hxv : ∀ i ∈ S, x i = c i := by
        intro i hi
        simp [x, hi]
      have h2 := hM.2 x
      rw [Finsupp.sum_of_support_subset x hx _ (by intro i _; simp)] at h2
      refine le_of_le_of_eq h2 ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finsupp.sum_of_support_subset x hx _ (by intro j _; simp)]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [star_trivial, Matrix.of_apply, hxv i hi, hxv j hj]
      ring

theorem pds_add {X : Type} {K K' : X → X → ℝ} (hK : IsPDS K) (hK' : IsPDS K') :
    IsPDS (fun x y => K x y + K' x y) := by
  refine ⟨fun x y => by show K x y + K' x y = K y x + K' y x; rw [hK.1 x y, hK'.1 x y], fun S c => ?_⟩
  have h := add_nonneg (hK.2 S c) (hK'.2 S c)
  refine le_of_le_of_eq h ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pds_mul {X : Type} {K K' : X → X → ℝ} (hK : IsPDS K) (hK' : IsPDS K') :
    IsPDS (fun x y => K x y * K' x y) := by
  rw [isPDS_iff] at hK hK' ⊢
  have e : (Matrix.of fun x y => K x y * K' x y) = Matrix.hadamard (Matrix.of K) (Matrix.of K') := by
    ext i j
    simp [Matrix.hadamard_apply]
  rw [e]
  exact hK.hadamard hK'

theorem pds_comp {X Y : Type} {K : X → X → ℝ} (hK : IsPDS K) (f : Y → X) :
    IsPDS (fun p q => K (f p) (f q)) := by
  rw [isPDS_iff] at hK ⊢
  have e : (Matrix.of fun p q => K (f p) (f q)) = (Matrix.of K).submatrix f f := by
    ext i j
    simp
  rw [e]
  exact hK.submatrix f

theorem pds_lim {X : Type} (Kn : ℕ → X → X → ℝ) (Klim : X → X → ℝ) (hKn : ∀ n, IsPDS (Kn n))
    (hlim : ∀ x y, Filter.Tendsto (fun n => Kn n x y) Filter.atTop (nhds (Klim x y))) :
    IsPDS Klim := by
  refine ⟨fun x y => ?_, fun S c => ?_⟩
  · have h2 := hlim y x
    have e : (fun n => Kn n y x) = (fun n => Kn n x y) := funext fun n => ((hKn n).1 x y).symm
    rw [e] at h2
    exact tendsto_nhds_unique (hlim x y) h2
  · have ht : Filter.Tendsto (fun n => ∑ i ∈ S, ∑ j ∈ S, c i * c j * Kn n i j) Filter.atTop
        (nhds (∑ i ∈ S, ∑ j ∈ S, c i * c j * Klim i j)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (hlim i j).const_mul _
    exact ge_of_tendsto' ht fun n => (hKn n).2 S c

theorem pds_one {X : Type} : IsPDS (fun (_ : X) (_ : X) => (1 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun S c => ?_⟩
  simp only [mul_one]
  rw [← Finset.sum_mul_sum]
  exact mul_self_nonneg _

theorem pds_pow {X : Type} {K : X → X → ℝ} (hK : IsPDS K) (n : ℕ) :
    IsPDS (fun x y => K x y ^ n) := by
  induction n with
  | zero => simpa using (pds_one (X := X))
  | succ n ih =>
    simp only [pow_succ]
    exact pds_mul ih hK

theorem pds_smul {X : Type} {K : X → X → ℝ} (hK : IsPDS K) {a : ℝ} (ha : 0 ≤ a) :
    IsPDS (fun x y => a * K x y) := by
  refine ⟨fun x y => by show a * K x y = a * K y x; rw [hK.1 x y], fun S c => ?_⟩
  have h := mul_nonneg ha (hK.2 S c)
  refine le_of_le_of_eq h ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pds_zero {X : Type} : IsPDS (fun (_ : X) (_ : X) => (0 : ℝ)) :=
  ⟨fun _ _ => rfl, fun S c => by simp⟩

theorem pds_fsum {X : Type} (f : ℕ → X → X → ℝ) (hf : ∀ n, IsPDS (f n)) (s : Finset ℕ) :
    IsPDS (fun x y => ∑ n ∈ s, f n x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pds_zero (X := X))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact pds_add (hf a) ih

end P6510ec44

open FoundationsML.Kernels in
theorem solution {X : Type} (K K' : X → X → ℝ) (hK : IsPDS K) (hK' : IsPDS K') :
    IsPDS (fun x y => K x y + K' x y) ∧
    IsPDS (fun x y => K x y * K' x y) ∧
    IsPDS (fun p q : X × X => K p.1 q.1 * K' p.2 q.2) ∧
    (∀ (Kn : ℕ → X → X → ℝ) (Klim : X → X → ℝ), (∀ n, IsPDS (Kn n)) →
      (∀ x y, Filter.Tendsto (fun n => Kn n x y) Filter.atTop (nhds (Klim x y))) →
      IsPDS Klim) ∧
    (∀ (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ρ : ℝ) (hρ : 0 < ρ) (hKb : ∀ x y, |K x y| < ρ)
       (hsum : ∀ x y, Summable (fun n => a n * (K x y) ^ n)),
       IsPDS (fun x y => ∑' n, a n * (K x y) ^ n)) := by
  refine ⟨P6510ec44.pds_add hK hK', P6510ec44.pds_mul hK hK', ?_,
    P6510ec44.pds_lim, ?_⟩
  · exact P6510ec44.pds_mul (P6510ec44.pds_comp hK Prod.fst) (P6510ec44.pds_comp hK' Prod.snd)
  · intro a ha ρ hρ hKb hsum
    refine P6510ec44.pds_lim (fun N x y => ∑ n ∈ Finset.range N, a n * K x y ^ n) _
      (fun N => P6510ec44.pds_fsum (fun n x y => a n * K x y ^ n)
        (fun n => P6510ec44.pds_smul (P6510ec44.pds_pow hK n) (ha n)) _) ?_
    intro x y
    exact (hsum x y).hasSum.tendsto_sum_nat
