-- Prove2me | solution 1 for Conway99Formal.BinaryCode.binary_adjacency_image_even_LCD
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:52:52.7724+00:00
-- url     : https://prove2.me/submissions/c6781d5a-d3d9-472d-947d-7a4ddd3921e7

import Mathlib

set_option autoImplicit false

/-!
Binary adjacency-code identities for an actual SRG(99,14,1,2).
Sources: Conway99/Conway99/Claims/C01srgcorealgebra.lean §4;
Conway99/Conway99/Claims/C04finitefieldranks.lean §1;
Conway99/results/R003_enriched_binary_code_odd_cross_rank.md §1;
Conway99/results/R017_binary_genus2_smith_weight60.md §1.
-/

namespace Conway99Formal.BinaryCode

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The literal binary adjacency matrix of the graph. -/
def adjacency : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)

/-- Literal support of a binary word. -/
def support (u : V → ZMod 2) : Finset V := univ.filter fun v => u v ≠ 0

/-- Hamming weight of a binary word. -/
def weight (u : V → ZMod 2) : ℕ := (support u).card

/-- Modulo two, the adjacency matrix of an SRG(99,14,1,2) is idempotent. -/
theorem adjacency_idempotent (h : G.IsSRGWith 99 14 1 2) :
    adjacency G * adjacency G = adjacency G := by
  have hm := h.matrix_eq (α := ZMod 2)
  have h14 : (14 : ZMod 2) = 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hfourteen : (14 : ℕ) • (1 : Matrix V V (ZMod 2)) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul, h14]
  have htwo : (2 : ℕ) • Gᶜ.adjMatrix (ZMod 2) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul, h2]
  rw [hfourteen, htwo] at hm
  simpa [adjacency, sq] using hm

/-- A binary word is in the adjacency image exactly when adjacency fixes it. -/
theorem in_image_iff_fixed (h : G.IsSRGWith 99 14 1 2) (u : V → ZMod 2) :
    (∃ x : V → ZMod 2, (adjacency G).mulVec x = u) ↔
      (adjacency G).mulVec u = u := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [Matrix.mulVec_mulVec, adjacency_idempotent G h]
  · intro hu
    exact ⟨u, hu⟩

/-- Adjacency annihilates the image of its complementary binary projection. -/
theorem complementary_projection (h : G.IsSRGWith 99 14 1 2) :
    adjacency G * (1 + adjacency G) = 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, adjacency_idempotent G h]
  ext i j
  change adjacency G i j + adjacency G i j = 0
  simpa only [ZMod.neg_eq_self_mod_two] using
    (add_neg_cancel (adjacency G i j))

/-- The kernel is the image of the complementary binary projection. -/
theorem kernel_iff_complement_image (h : G.IsSRGWith 99 14 1 2) (u : V → ZMod 2) :
    (adjacency G).mulVec u = 0 ↔
      ∃ x : V → ZMod 2, (1 + adjacency G).mulVec x = u := by
  constructor
  · intro hu
    refine ⟨u, ?_⟩
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hu, add_zero]
  · rintro ⟨x, rfl⟩
    rw [Matrix.mulVec_mulVec, complementary_projection G h, Matrix.zero_mulVec]

/-- The two binary projections have complementary ranks in the same vertex space. -/
theorem complementary_rank_sum (h : G.IsSRGWith 99 14 1 2) :
    (adjacency G).rank + (1 + adjacency G).rank = Fintype.card V := by
  have hker : LinearMap.ker (adjacency G).mulVecLin =
      LinearMap.range (1 + adjacency G).mulVecLin := by
    ext u
    simpa only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply] using
      (kernel_iff_complement_image G h u)
  have hdim := (adjacency G).mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at hdim
  simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using hdim

/-- Rank 54 of binary adjacency gives rank 45 of its complementary projection. -/
theorem complementary_rank_forty_five (h : G.IsSRGWith 99 14 1 2)
    (hrank : (adjacency G).rank = 54) :
    (1 + adjacency G).rank = 45 := by
  have hsum := complementary_rank_sum G h
  rw [hrank, h.card] at hsum
  omega

/-- The orthogonal complement of the adjacency image is the adjacency kernel. -/
theorem orthogonal_image_iff_kernel (u : V → ZMod 2) :
    (∀ y : V → ZMod 2, u ⬝ᵥ (adjacency G).mulVec y = 0) ↔
      (adjacency G).mulVec u = 0 := by
  have hsym : (adjacency G)ᵀ = adjacency G := G.transpose_adjMatrix
  constructor
  · intro hu
    apply dotProduct_eq_zero_iff.mp
    intro y
    have ht := Matrix.dotProduct_transpose_mulVec (adjacency G) y u
    rw [hsym] at ht
    calc
      (adjacency G).mulVec u ⬝ᵥ y = y ⬝ᵥ (adjacency G).mulVec u :=
        dotProduct_comm _ _
      _ = u ⬝ᵥ (adjacency G).mulVec y := ht
      _ = 0 := hu y
  · intro hu y
    have ht := Matrix.dotProduct_transpose_mulVec (adjacency G) y u
    rw [hsym, hu] at ht
    simpa using ht.symm

/-- The binary adjacency image meets its ordinary dot-product orthogonal complement trivially. -/
theorem image_LCD (h : G.IsSRGWith 99 14 1 2) (u : V → ZMod 2)
    (hu : ∃ x : V → ZMod 2, (adjacency G).mulVec x = u)
    (hortho : ∀ y : V → ZMod 2, u ⬝ᵥ (adjacency G).mulVec y = 0) : u = 0 := by
  have hfixed := (in_image_iff_fixed G h u).mp hu
  exact hfixed.symm.trans ((orthogonal_image_iff_kernel G u).mp hortho)

private theorem binary_square (a : ZMod 2) : a * a = a := by
  simpa only [pow_two] using (ZMod.pow_card a)

private theorem self_dot_eq_sum (u : V → ZMod 2) : u ⬝ᵥ u = ∑ i, u i := by
  simp only [dotProduct, binary_square]

private theorem sum_eq_weight (u : V → ZMod 2) :
    (∑ i, u i) = (weight u : ZMod 2) := by
  have hb (a : ZMod 2) : a = if a ≠ 0 then 1 else 0 := by
    simpa using (ZMod.pow_card_sub_one a)
  calc
    (∑ i, u i) = ∑ i, if u i ≠ 0 then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hb (u i)
    _ = (weight u : ZMod 2) := by
      simpa [weight, support] using
        (Finset.sum_boole (R := ZMod 2) (fun i : V => u i ≠ 0) Finset.univ)

/-- The all-ones word lies in the binary adjacency kernel because the degree is 14. -/
theorem all_ones_kernel (h : G.IsSRGWith 99 14 1 2) :
    (adjacency G).mulVec (fun _ => (1 : ZMod 2)) = 0 := by
  ext i
  have hi := G.adjMatrix_mulVec_const_apply_of_regular
    (α := ZMod 2) (a := 1) h.regular (v := i)
  have h14 : (14 : ZMod 2) = 0 := by decide
  simpa [adjacency, h14] using hi

/-- Every word in the binary adjacency image has even Hamming weight. -/
theorem image_even (h : G.IsSRGWith 99 14 1 2) (x : V → ZMod 2) :
    (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec x = 0 := by
  let e : V → ZMod 2 := fun _ => 1
  have he : (adjacency G).mulVec e = 0 := all_ones_kernel G h
  have hsym : (adjacency G)ᵀ = adjacency G := G.transpose_adjMatrix
  calc
    (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec x =
        ∑ i, (adjacency G).mulVec x i := self_dot_eq_sum _
    _ = e ⬝ᵥ (adjacency G).mulVec x := by simp [e, dotProduct]
    _ = x ⬝ᵥ (adjacency G)ᵀ.mulVec e :=
      (Matrix.dotProduct_transpose_mulVec (adjacency G) x e).symm
    _ = 0 := by rw [hsym, he]; simp

/-- The literal Hamming weight of every image word is even. -/
theorem image_weight_even (h : G.IsSRGWith 99 14 1 2) (x : V → ZMod 2) :
    Even (weight ((adjacency G).mulVec x)) := by
  have hd := image_even G h x
  rw [self_dot_eq_sum, sum_eq_weight] at hd
  exact ZMod.natCast_eq_zero_iff_even.mp hd

private theorem bit_add (a b : ZMod 2) :
    (if a + b ≠ 0 then 1 else 0 : ℕ) +
      2 * (if a ≠ 0 then 1 else 0) * (if b ≠ 0 then 1 else 0) =
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> decide

private theorem weight_eq_bit_sum (u : V → ZMod 2) :
    weight u = ∑ i, if u i ≠ 0 then 1 else 0 := by
  simpa [weight, support] using
    (Finset.sum_boole (R := ℕ) (fun i : V => u i ≠ 0) Finset.univ).symm

private theorem intersection_eq_bit_sum (u v : V → ZMod 2) :
    (support u ∩ support v).card =
      ∑ i, (if u i ≠ 0 then 1 else 0) * (if v i ≠ 0 then 1 else 0) := by
  have hcard : (support u ∩ support v).card =
      ∑ i, if u i ≠ 0 ∧ v i ≠ 0 then (1 : ℕ) else 0 := by
    simpa [support, Finset.filter_and] using
      (Finset.sum_boole (R := ℕ)
        (fun i : V => u i ≠ 0 ∧ v i ≠ 0) Finset.univ).symm
  rw [hcard]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- The binary support-count identity, including the overlapping coordinates. -/
theorem weight_add_intersection (u v : V → ZMod 2) :
    weight (u + v) + 2 * (support u ∩ support v).card =
      weight u + weight v := by
  rw [weight_eq_bit_sum, weight_eq_bit_sum, weight_eq_bit_sum,
    intersection_eq_bit_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc, Pi.add_apply] using bit_add (u i) (v i)

private theorem intersection_eq_dot (u v : V → ZMod 2) :
    ((support u ∩ support v).card : ZMod 2) = u ⬝ᵥ v := by
  rw [dotProduct]
  have hcard : ((support u ∩ support v).card : ZMod 2) =
      ∑ i, if u i ≠ 0 ∧ v i ≠ 0 then (1 : ZMod 2) else 0 := by
    simpa [support, Finset.filter_and] using
      (Finset.sum_boole (R := ZMod 2)
        (fun i : V => u i ≠ 0 ∧ v i ≠ 0) Finset.univ).symm
  rw [hcard]
  apply Finset.sum_congr rfl
  intro i _
  have hbit (a b : ZMod 2) :
      (if a ≠ 0 ∧ b ≠ 0 then (1 : ZMod 2) else 0) = a * b := by
    fin_cases a <;> fin_cases b <;> decide
  exact hbit (u i) (v i)

/-- Half weight modulo two polarizes to the ordinary dot product on even words. -/
theorem half_weight_polarization (u v : V → ZMod 2)
    (hu : Even (weight u)) (hv : Even (weight v)) :
    (((weight (u + v) / 2 : ℕ) : ZMod 2) + u ⬝ᵥ v) =
      ((weight u / 2 : ℕ) : ZMod 2) + ((weight v / 2 : ℕ) : ZMod 2) := by
  have hsum := weight_add_intersection u v
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have heven : Even (weight (u + v)) := by
    rw [ha, hb] at hsum
    exact ⟨a + b - (support u ∩ support v).card, by omega⟩
  obtain ⟨c, hc⟩ := heven
  have hhalves : c + (support u ∩ support v).card = a + b := by
    rw [ha, hb, hc] at hsum
    omega
  have hwa : weight u / 2 = a := by omega
  have hwb : weight v / 2 = b := by omega
  have hwc : weight (u + v) / 2 = c := by omega
  rw [hwa, hwb, hwc, ← intersection_eq_dot]
  simpa only [Nat.cast_add] using
    congrArg (fun n : ℕ => (n : ZMod 2)) hhalves

/-- The adjacency image carries the graph-owned half-weight quadratic refinement. -/
theorem image_half_weight_polarization (h : G.IsSRGWith 99 14 1 2)
    (x y : V → ZMod 2) :
    (((weight ((adjacency G).mulVec (x + y)) / 2 : ℕ) : ZMod 2) +
      (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec y) =
      ((weight ((adjacency G).mulVec x) / 2 : ℕ) : ZMod 2) +
        ((weight ((adjacency G).mulVec y) / 2 : ℕ) : ZMod 2) := by
  rw [Matrix.mulVec_add]
  exact half_weight_polarization
    ((adjacency G).mulVec x) ((adjacency G).mulVec y)
    (image_weight_even G h x) (image_weight_even G h y)

/-- The idempotent, even and LCD properties in one graph-owned statement. -/
theorem solution (h : G.IsSRGWith 99 14 1 2) :
    adjacency G * adjacency G = adjacency G ∧
    (∀ x : V → ZMod 2,
      (adjacency G).mulVec x ⬝ᵥ (adjacency G).mulVec x = 0) ∧
    (∀ u : V → ZMod 2,
      (∃ x : V → ZMod 2, (adjacency G).mulVec x = u) →
      (∀ y : V → ZMod 2, u ⬝ᵥ (adjacency G).mulVec y = 0) → u = 0) := by
  exact ⟨adjacency_idempotent G h, image_even G h, image_LCD G h⟩

#print axioms adjacency_idempotent
#print axioms in_image_iff_fixed
#print axioms complementary_projection
#print axioms kernel_iff_complement_image
#print axioms complementary_rank_sum
#print axioms complementary_rank_forty_five
#print axioms orthogonal_image_iff_kernel
#print axioms image_LCD
#print axioms all_ones_kernel
#print axioms image_even
#print axioms image_weight_even
#print axioms weight_add_intersection
#print axioms half_weight_polarization
#print axioms image_half_weight_polarization
#print axioms solution

end Conway99Formal.BinaryCode

/-- A self-contained binary-code consequence for one actual SRG(99,14,1,2).
The literal adjacency matrix is idempotent, its image consists of even words,
and that image has trivial intersection with its dot-product orthogonal space. -/
theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)) * (G.adjMatrix (ZMod 2)) = G.adjMatrix (ZMod 2) ∧
    (∀ x : V → ZMod 2,
      (G.adjMatrix (ZMod 2)).mulVec x ⬝ᵥ (G.adjMatrix (ZMod 2)).mulVec x = 0) ∧
    (∀ u : V → ZMod 2,
      (∃ x : V → ZMod 2, (G.adjMatrix (ZMod 2)).mulVec x = u) →
      (∀ y : V → ZMod 2, u ⬝ᵥ (G.adjMatrix (ZMod 2)).mulVec y = 0) → u = 0) := by
  simpa [Conway99Formal.BinaryCode.adjacency] using
    Conway99Formal.BinaryCode.solution G h

#print axioms solution
