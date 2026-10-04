-- Prove2me | solution 1 for Conway99Formal.Norm16.norm16_integer_eigenvector_support
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:57:21.896841+00:00
-- url     : https://prove2.me/submissions/4e5d0584-0b9b-446e-9b86-accdf3963500

import Mathlib

set_option autoImplicit false

/-! Graph-owned integer minus-four eigenfunctions.  The source is
`proofs/INTEGER_MINUS_FOUR_MINIMUM.md` in `archive/clean-start/proof-library.zip`.
The later norm-sixteen geometry and cross-design sources use the same graph and vector. -/

namespace Conway99Formal.Norm16

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The integer minus-four eigenrelation in the actual graph's coordinates. -/
def IsMinusFourEigenfunction (a : V → ℤ) : Prop :=
  ∀ v, (∑ u : V, G.adjMatrix ℤ v u * a u) = -4 * a v

/-- Squared Euclidean length in the same vertex coordinates. -/
def normSq (a : V → ℤ) : ℤ := ∑ v : V, a v * a v

/-- Total positive integer mass, counting entries with multiplicity. -/
def positiveMass (a : V → ℤ) : ℤ := ∑ v : V, max (a v) 0

/-- Total negative integer mass, counting absolute values. -/
def negativeMass (a : V → ℤ) : ℤ := ∑ v : V, max (-a v) 0

def P (a : V → ℤ) : Finset V := Finset.univ.filter fun v => a v = 1
def M (a : V → ℤ) : Finset V := Finset.univ.filter fun v => a v = -1
def zeroSupport (a : V → ℤ) : Finset V := Finset.univ.filter fun v => a v = 0

/-- The number of positive support points seen by a vertex. -/
def positiveContacts (a : V → ℤ) (v : V) : ℕ :=
  (G.neighborFinset v ∩ P a).card

/-- The number of negative support points seen by a vertex. -/
def negativeContacts (a : V → ℤ) (v : V) : ℕ :=
  (G.neighborFinset v ∩ M a).card

def Z (a : V → ℤ) : Finset V :=
  Finset.univ.filter fun v => a v = 0 ∧ positiveContacts G a v = 0

def R (a : V → ℤ) : Finset V :=
  Finset.univ.filter fun v => a v = 0 ∧ positiveContacts G a v = 1

def T (a : V → ℤ) : Finset V :=
  Finset.univ.filter fun v => a v = 0 ∧ positiveContacts G a v = 2

/-- Signed supports are disjoint by their literal coordinate definitions. -/
theorem P_disjoint_M (a : V → ℤ) : Disjoint (P a) (M a) := by
  apply Finset.disjoint_left.mpr
  intro v hp hm
  have hp' : a v = 1 := (Finset.mem_filter.mp hp).2
  have hm' : a v = -1 := (Finset.mem_filter.mp hm).2
  omega

#print axioms Conway99Formal.Norm16.P_disjoint_M

/-- Unit coordinates partition the same graph's vertex set into the two
signed supports and the zero coordinates. -/
theorem unit_support_partition (a : V → ℤ)
    (hunit : ∀ v, a v = -1 ∨ a v = 0 ∨ a v = 1) :
    P a ∪ M a ∪ zeroSupport a = Finset.univ := by
  ext v
  simp only [P, M, zeroSupport, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    trivial
  · intro hv
    rcases hunit v with hm | hz | hp
    · exact Or.inl (Or.inr hm)
    · exact Or.inr hz
    · exact Or.inl (Or.inl hp)

#print axioms Conway99Formal.Norm16.unit_support_partition

/-- Distinct graph vertices have at most two common neighbors; adjacency
improves this bound to one. -/
theorem common_neighbors_card_le_two (h : G.IsSRGWith 99 14 1 2)
    (p q : V) (hpq : p ≠ q) : Fintype.card (G.commonNeighbors p q) ≤ 2 := by
  by_cases hadj : G.Adj p q
  · rw [h.of_adj p q hadj]
    omega
  · rw [h.of_not_adj hpq hadj]

#print axioms Conway99Formal.Norm16.common_neighbors_card_le_two

/-- Regularity and the minus-four eigenrelation force total coordinate sum zero. -/
theorem coordinate_sum_zero (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) : (∑ v : V, a v) = 0 := by
  have hrow (w : V) : (∑ v : V, G.adjMatrix ℤ w v) = 14 := by
    have hr := G.adjMatrix_mulVec_const_apply_of_regular
      (α := ℤ) (a := 1) h.regular (v := w)
    simpa [Matrix.mulVec, dotProduct, Function.const] using hr
  have hcol (w : V) : (∑ v : V, G.adjMatrix ℤ v w) = 14 := by
    have hs (v : V) : G.adjMatrix ℤ v w = G.adjMatrix ℤ w v := by
      simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
    simp_rw [hs]
    exact hrow w
  have hd : (∑ v : V, ∑ w : V, G.adjMatrix ℤ v w * a w) =
      14 * (∑ w : V, a w) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol]
    rw [Finset.mul_sum]
  have he : (∑ v : V, ∑ w : V, G.adjMatrix ℤ v w * a w) =
      -4 * (∑ v : V, a v) := by
    have ha' (v : V) : (∑ w : V, G.adjMatrix ℤ v w * a w) = -4 * a v := ha v
    simp_rw [ha']
    rw [Finset.mul_sum]
  omega

#print axioms Conway99Formal.Norm16.coordinate_sum_zero

/-- The eigenfunction has equal total positive and negative integer mass. -/
theorem mass_balance (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) : positiveMass a = negativeMass a := by
  have hp (v : V) : a v = max (a v) 0 - max (-a v) 0 := by
    rcases le_total 0 (a v) with hv | hv
    · rw [max_eq_left hv, max_eq_right (by omega)]
      omega
    · rw [max_eq_right hv, max_eq_left (by omega)]
      omega
  have hs : (∑ v : V, a v) = positiveMass a - negativeMass a := by
    calc
      (∑ v : V, a v) =
          ∑ v : V, (max (a v) 0 - max (-a v) 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hp v
      _ = positiveMass a - negativeMass a := by
        simp only [Finset.sum_sub_distrib, positiveMass, negativeMass]
  have hz := coordinate_sum_zero G h a ha
  rw [hs] at hz
  omega

#print axioms Conway99Formal.Norm16.mass_balance

/-- An integral square pays at least the absolute mass of its coordinate. -/
private theorem square_ge_mass (x : ℤ) :
    max x 0 + max (-x) 0 ≤ x * x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by omega)]
    by_cases hz : x = 0
    · simp [hz]
    · have h1 : 1 ≤ x := by omega
      have hm : 0 ≤ x * (x - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
  · rw [max_eq_right hx, max_eq_left (by omega)]
    by_cases hz : x = 0
    · simp [hz]
    · have h1 : x ≤ -1 := by omega
      have hm : 0 ≤ (-x) * (-x - 1) := mul_nonneg (by omega) (by omega)
      nlinarith

#print axioms square_ge_mass

/-- The squared norm dominates both signed masses together. -/
theorem normSq_ge_mass (a : V → ℤ) :
    positiveMass a + negativeMass a ≤ normSq a := by
  calc
    positiveMass a + negativeMass a =
        ∑ v : V, (max (a v) 0 + max (-a v) 0) := by
          simp only [positiveMass, negativeMass, Finset.sum_add_distrib]
    _ ≤ ∑ v : V, a v * a v := by
      apply Finset.sum_le_sum
      intro v hv
      exact square_ge_mass (a v)
    _ = normSq a := rfl

#print axioms Conway99Formal.Norm16.normSq_ge_mass

/-- A positive coordinate of size at least two pays its excess square cost
in addition to the mass of the full vector. -/
theorem normSq_ge_mass_plus_coordinate (a : V → ℤ) (p : V)
    (hp : 2 ≤ a p) :
    positiveMass a + negativeMass a + (a p * a p - a p) ≤ normSq a := by
  let mass : V → ℤ := fun v => max (a v) 0 + max (-a v) 0
  let rest : Finset V := Finset.univ.erase p
  have hrest : (∑ v ∈ rest, mass v) ≤ (∑ v ∈ rest, a v * a v) := by
    apply Finset.sum_le_sum
    intro v hv
    exact square_ge_mass (a v)
  have hmass : positiveMass a + negativeMass a = ∑ v : V, mass v := by
    simp only [mass, positiveMass, negativeMass, Finset.sum_add_distrib]
  have hsplit_mass : (∑ v : V, mass v) = (∑ v ∈ rest, mass v) + mass p := by
    simpa [rest] using
      (Finset.sum_erase_add Finset.univ mass (Finset.mem_univ p)).symm
  have hsplit_sq : normSq a = (∑ v ∈ rest, a v * a v) + a p * a p := by
    simpa [normSq, rest] using
      (Finset.sum_erase_add Finset.univ (fun v => a v * a v)
        (Finset.mem_univ p)).symm
  have hmp : mass p = a p := by
    dsimp [mass]
    rw [max_eq_left (by omega), max_eq_right (by omega)]
    omega
  rw [hmass, hsplit_mass, hsplit_sq, hmp]
  omega

#print axioms Conway99Formal.Norm16.normSq_ge_mass_plus_coordinate

/-- At any vertex the total negative mass pays for the required negative
neighbor score. -/
theorem negativeMass_ge_four_coordinate (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (p : V) :
    4 * a p ≤ negativeMass a := by
  have hdot : (∑ u : V, G.adjMatrix ℤ p u * a u) =
      ∑ u ∈ G.neighborFinset p, a u := by
    simpa [dotProduct] using (G.adjMatrix_dotProduct (α := ℤ) p a)
  have heig : (∑ u ∈ G.neighborFinset p, a u) = -4 * a p := by
    rw [← hdot]
    exact ha p
  have hneighbor : (∑ u ∈ G.neighborFinset p, -a u) ≤
      (∑ u ∈ G.neighborFinset p, max (-a u) 0) := by
    apply Finset.sum_le_sum
    intro u hu
    exact le_max_left _ _
  have hglobal : (∑ u ∈ G.neighborFinset p, max (-a u) 0) ≤
      negativeMass a := by
    unfold negativeMass
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro u hu hnot
    exact le_max_right _ _
  rw [Finset.sum_neg_distrib, heig] at hneighbor
  omega

#print axioms Conway99Formal.Norm16.negativeMass_ge_four_coordinate

/-- A positive integer coordinate of magnitude at least two forces squared
norm at least eighteen, without any support graph enumeration. -/
theorem normSq_ge_eighteen_of_large_positive
    (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (p : V) (hp : 2 ≤ a p) :
    18 ≤ normSq a := by
  have hbalance := mass_balance G h a ha
  have hneighbor := negativeMass_ge_four_coordinate G a ha p
  have hcost := normSq_ge_mass_plus_coordinate a p hp
  have hprod : 0 ≤ (a p - 2) * (a p + 9) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

#print axioms Conway99Formal.Norm16.normSq_ge_eighteen_of_large_positive

/-- The large-coordinate cost holds for either sign. -/
theorem normSq_ge_eighteen_of_large_coordinate
    (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (p : V)
    (hp : 2 ≤ a p ∨ a p ≤ -2) : 18 ≤ normSq a := by
  rcases hp with hp | hp
  · exact normSq_ge_eighteen_of_large_positive G h a ha p hp
  · have hneg : IsMinusFourEigenfunction G (fun v => -a v) := by
      intro v
      calc
        (∑ u : V, G.adjMatrix ℤ v u * -a u) =
            -(∑ u : V, G.adjMatrix ℤ v u * a u) := by
          simp_rw [mul_neg]
          rw [Finset.sum_neg_distrib]
        _ = -(-4 * a v) := congrArg Neg.neg (ha v)
        _ = -4 * (-a v) := by ring
    have hn := normSq_ge_eighteen_of_large_positive G h (fun v => -a v)
      hneg p (by omega)
    simpa [normSq] using hn

#print axioms Conway99Formal.Norm16.normSq_ge_eighteen_of_large_coordinate

/-- Every coordinate of a norm-sixteen integer minus-four eigenfunction is
minus one, zero, or one. -/
theorem norm16_unit_coordinates (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (v : V) : a v = -1 ∨ a v = 0 ∨ a v = 1 := by
  by_contra hunit
  have hlarge : 2 ≤ a v ∨ a v ≤ -2 := by omega
  have hcost := normSq_ge_eighteen_of_large_coordinate G h a ha v hlarge
  omega

#print axioms Conway99Formal.Norm16.norm16_unit_coordinates

/-- A norm-fourteen eigenfunction also has only unit nonzero coordinates. -/
theorem norm14_unit_coordinates (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 14)
    (v : V) : a v = -1 ∨ a v = 0 ∨ a v = 1 := by
  by_contra hunit
  have hlarge : 2 ≤ a v ∨ a v ≤ -2 := by omega
  have hcost := normSq_ge_eighteen_of_large_coordinate G h a ha v hlarge
  omega

#print axioms Conway99Formal.Norm16.norm14_unit_coordinates

/-- The squared norm of an integer minus-four eigenfunction is even. -/
theorem normSq_mod_two_zero (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) : normSq a % 2 = 0 := by
  have hpoint (x : ℤ) : (x * x) % 2 = x % 2 := by
    have hr : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hr with hr | hr <;> simp [Int.mul_emod, hr]
  have hsum (s : Finset V) :
      (∑ v ∈ s, a v * a v) % 2 = (∑ v ∈ s, a v) % 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
      simp only [Finset.sum_insert hv]
      simp only [Int.add_emod, hpoint, ih, Int.emod_emod]
  simpa [normSq, coordinate_sum_zero G h a ha] using hsum Finset.univ

#print axioms Conway99Formal.Norm16.normSq_mod_two_zero

/-- For a unit-coordinate eigenfunction, the two sign supports have equal
size and the squared norm is twice that size. -/
theorem unit_support_counts (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ v, a v = -1 ∨ a v = 0 ∨ a v = 1) :
    (P a).card = (M a).card ∧ normSq a = 2 * (P a).card := by
  have hf (v : V) : a v =
      (if v ∈ P a then (1 : ℤ) else 0) - (if v ∈ M a then (1 : ℤ) else 0) := by
    rcases hunit v with hv | hv | hv <;> simp [P, M, hv]
  have hq (v : V) : a v * a v =
      (if v ∈ P a then (1 : ℤ) else 0) + (if v ∈ M a then (1 : ℤ) else 0) := by
    rcases hunit v with hv | hv | hv <;> simp [P, M, hv]
  have hsum : (∑ v : V, a v) = (P a).card - (M a).card := by
    simp_rw [hf]
    simp [Finset.sum_sub_distrib, P, M]
  have hsq : normSq a = (P a).card + (M a).card := by
    simp only [normSq]
    simp_rw [hq]
    simp [Finset.sum_add_distrib, P, M]
  have hz := coordinate_sum_zero G h a ha
  rw [hsum] at hz
  omega

#print axioms Conway99Formal.Norm16.unit_support_counts

/-- A unit-coordinate norm-sixteen eigenfunction has eight entries of each sign. -/
theorem unit_norm16_support_card (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ v, a v = -1 ∨ a v = 0 ∨ a v = 1)
    (hnorm : normSq a = 16) : (P a).card = 8 ∧ (M a).card = 8 := by
  have hc := unit_support_counts G h a ha hunit
  omega

#print axioms Conway99Formal.Norm16.unit_norm16_support_card

/-- Equality at squared norm fourteen has seven vertices of each sign. -/
theorem norm14_support_card (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 14) :
    (P a).card = 7 ∧ (M a).card = 7 := by
  have hc := unit_support_counts G h a ha
    (norm14_unit_coordinates G h a ha hnorm)
  omega

#print axioms Conway99Formal.Norm16.norm14_support_card

/-- Every norm-sixteen integer minus-four eigenfunction has eight positive
and eight negative unit coordinates in the actual graph. -/
theorem norm16_support_card (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16) :
    (P a).card = 8 ∧ (M a).card = 8 := by
  exact unit_norm16_support_card G h a ha
    (norm16_unit_coordinates G h a ha hnorm) hnorm

#print axioms Conway99Formal.Norm16.norm16_support_card

/-- Norm sixteen leaves exactly eighty-three zero coordinates. -/
theorem norm16_zero_support_card (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16) :
    (zeroSupport a).card = 83 := by
  have hunit := norm16_unit_coordinates G h a ha hnorm
  have hPZ : Disjoint (P a) (zeroSupport a) := by
    apply Finset.disjoint_left.mpr
    intro v hp hz
    have hp' : a v = 1 := (Finset.mem_filter.mp hp).2
    have hz' : a v = 0 := (Finset.mem_filter.mp hz).2
    omega
  have hMZ : Disjoint (M a) (zeroSupport a) := by
    apply Finset.disjoint_left.mpr
    intro v hm hz
    have hm' : a v = -1 := (Finset.mem_filter.mp hm).2
    have hz' : a v = 0 := (Finset.mem_filter.mp hz).2
    omega
  have hPM := P_disjoint_M (a := a)
  have hUM : Disjoint (P a ∪ M a) (zeroSupport a) :=
    Finset.disjoint_union_left.mpr ⟨hPZ, hMZ⟩
  have hcard := congrArg Finset.card (unit_support_partition a hunit)
  rw [Finset.card_union_of_disjoint hUM,
    Finset.card_union_of_disjoint hPM, Finset.card_univ] at hcard
  have hsign := norm16_support_card G h a ha hnorm
  have htotal := h.card
  omega

#print axioms Conway99Formal.Norm16.norm16_zero_support_card

/-- The eigenrelation is the exact difference between positive and negative
contacts when all coordinates are units or zero. -/
theorem signed_contact_difference (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ u, a u = -1 ∨ a u = 0 ∨ a u = 1)
    (v : V) :
    (positiveContacts G a v : ℤ) - negativeContacts G a v = -4 * a v := by
  have hf (u : V) : a u =
      (if u ∈ P a then (1 : ℤ) else 0) - (if u ∈ M a then (1 : ℤ) else 0) := by
    rcases hunit u with hu | hu | hu <;> simp [P, M, hu]
  have hdot : (∑ u : V, G.adjMatrix ℤ v u * a u) =
      ∑ u ∈ G.neighborFinset v, a u := by
    simpa [dotProduct] using (G.adjMatrix_dotProduct (α := ℤ) v a)
  have hsum : (∑ u ∈ G.neighborFinset v, a u) =
      (positiveContacts G a v : ℤ) - negativeContacts G a v := by
    simp_rw [hf]
    simp [Finset.sum_sub_distrib, positiveContacts, negativeContacts]
  rw [← hsum, ← hdot]
  exact ha v

#print axioms Conway99Formal.Norm16.signed_contact_difference

/-- A positive signed point has four more negative than positive neighbors. -/
theorem positive_contact_equation (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ u, a u = -1 ∨ a u = 0 ∨ a u = 1)
    (v : V) (hv : v ∈ P a) :
    negativeContacts G a v = positiveContacts G a v + 4 := by
  have hc := signed_contact_difference G a ha hunit v
  have hp : a v = 1 := (Finset.mem_filter.mp hv).2
  rw [hp] at hc
  omega

#print axioms Conway99Formal.Norm16.positive_contact_equation

/-- A negative signed point has four more positive than negative neighbors. -/
theorem negative_contact_equation (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ u, a u = -1 ∨ a u = 0 ∨ a u = 1)
    (v : V) (hv : v ∈ M a) :
    positiveContacts G a v = negativeContacts G a v + 4 := by
  have hc := signed_contact_difference G a ha hunit v
  have hm : a v = -1 := (Finset.mem_filter.mp hv).2
  rw [hm] at hc
  omega

#print axioms Conway99Formal.Norm16.negative_contact_equation

/-- At a zero coordinate, the actual graph sees equally many positive and
negative unit coordinates. -/
theorem zero_contact_balance (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a)
    (hunit : ∀ u, a u = -1 ∨ a u = 0 ∨ a u = 1)
    (v : V) (hv : a v = 0) :
    positiveContacts G a v = negativeContacts G a v := by
  have h := signed_contact_difference G a ha hunit v
  rw [hv] at h
  omega

#print axioms Conway99Formal.Norm16.zero_contact_balance

/-- Zero-coordinate contact balance without a separate unit premise at norm
sixteen. -/
theorem norm16_zero_contact_balance (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (v : V) (hv : a v = 0) :
    positiveContacts G a v = negativeContacts G a v := by
  exact zero_contact_balance G a ha
    (norm16_unit_coordinates G h a ha hnorm) v hv

#print axioms Conway99Formal.Norm16.norm16_zero_contact_balance

/-- A zero-contact point has no positive signed neighbor by its actual
support definition. -/
theorem no_edge_P_Z (a : V → ℤ) (p z : V)
    (hp : p ∈ P a) (hz : z ∈ Z G a) : ¬G.Adj p z := by
  intro hpz
  have hz0 : positiveContacts G a z = 0 := (Finset.mem_filter.mp hz).2.2
  have hempty : G.neighborFinset z ∩ P a = ∅ := Finset.card_eq_zero.mp hz0
  have hmem : p ∈ G.neighborFinset z ∩ P a :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z p).mpr
      ((G.adj_comm p z).mp hpz), hp⟩
  rw [hempty] at hmem
  simpa using hmem

#print axioms Conway99Formal.Norm16.no_edge_P_Z

/-- Eigenfunction balance also excludes negative signed neighbors at Z. -/
theorem norm16_no_edge_M_Z (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (m z : V) (hm : m ∈ M a) (hz : z ∈ Z G a) : ¬G.Adj m z := by
  intro hmz
  have haz : a z = 0 := (Finset.mem_filter.mp hz).2.1
  have hpos : positiveContacts G a z = 0 := (Finset.mem_filter.mp hz).2.2
  have hbal := norm16_zero_contact_balance G h a ha hnorm z haz
  have hempty : G.neighborFinset z ∩ M a = ∅ :=
    Finset.card_eq_zero.mp (by simpa [negativeContacts, hpos] using hbal.symm)
  have hmem : m ∈ G.neighborFinset z ∩ M a :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z m).mpr
      ((G.adj_comm m z).mp hmz), hm⟩
  rw [hempty] at hmem
  simpa using hmem

#print axioms Conway99Formal.Norm16.norm16_no_edge_M_Z

/-- Each Z point has zero contacts of both signs. -/
theorem norm16_Z_contacts (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (z : V) (hz : z ∈ Z G a) :
    a z = 0 ∧ positiveContacts G a z = 0 ∧ negativeContacts G a z = 0 := by
  obtain ⟨haz, hp⟩ := (Finset.mem_filter.mp hz).2
  exact ⟨haz, hp, by rw [← norm16_zero_contact_balance G h a ha hnorm z haz]; exact hp⟩

#print axioms Conway99Formal.Norm16.norm16_Z_contacts

/-- Each R point has one contact of each sign. -/
theorem norm16_R_contacts (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (r : V) (hr : r ∈ R G a) :
    a r = 0 ∧ positiveContacts G a r = 1 ∧ negativeContacts G a r = 1 := by
  obtain ⟨har, hp⟩ := (Finset.mem_filter.mp hr).2
  exact ⟨har, hp, by rw [← norm16_zero_contact_balance G h a ha hnorm r har]; exact hp⟩

#print axioms Conway99Formal.Norm16.norm16_R_contacts

/-- Each T point has two contacts of each sign. -/
theorem norm16_T_contacts (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (t : V) (ht : t ∈ T G a) :
    a t = 0 ∧ positiveContacts G a t = 2 ∧ negativeContacts G a t = 2 := by
  obtain ⟨hat, hp⟩ := (Finset.mem_filter.mp ht).2
  exact ⟨hat, hp, by rw [← norm16_zero_contact_balance G h a ha hnorm t hat]; exact hp⟩

#print axioms Conway99Formal.Norm16.norm16_T_contacts

/-- The three zero-contact cells are pairwise disjoint by their literal
contact counts, before proving that they exhaust all zero coordinates. -/
theorem zero_cells_pairwise_disjoint (a : V → ℤ) :
    Disjoint (Z G a) (R G a) ∧
    Disjoint (Z G a) (T G a) ∧
    Disjoint (R G a) (T G a) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hz hr
    have hz0 : positiveContacts G a v = 0 := (Finset.mem_filter.mp hz).2.2
    have hr1 : positiveContacts G a v = 1 := (Finset.mem_filter.mp hr).2.2
    omega
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hz ht
    have hz0 : positiveContacts G a v = 0 := (Finset.mem_filter.mp hz).2.2
    have ht2 : positiveContacts G a v = 2 := (Finset.mem_filter.mp ht).2.2
    omega
  · apply Finset.disjoint_left.mpr
    intro v hr ht
    have hr1 : positiveContacts G a v = 1 := (Finset.mem_filter.mp hr).2.2
    have ht2 : positiveContacts G a v = 2 := (Finset.mem_filter.mp ht).2.2
    omega

#print axioms Conway99Formal.Norm16.zero_cells_pairwise_disjoint

/-- The zero cells cover all zero coordinates once the source's open
at-most-two-contact bound is supplied for this same graph and vector. -/
theorem zero_cells_cover_of_contact_le_two (a : V → ℤ)
    (hbound : ∀ v, a v = 0 → positiveContacts G a v ≤ 2) :
    Z G a ∪ R G a ∪ T G a = zeroSupport a := by
  ext v
  simp only [Z, R, T, zeroSupport, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    rcases hv with (⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩
    all_goals exact hz
  · intro hz
    have hc := hbound v hz
    have hcases : positiveContacts G a v = 0 ∨
        positiveContacts G a v = 1 ∨ positiveContacts G a v = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact Or.inl (Or.inl ⟨hz, h0⟩)
    · exact Or.inl (Or.inr ⟨hz, h1⟩)
    · exact Or.inr ⟨hz, h2⟩

#print axioms Conway99Formal.Norm16.zero_cells_cover_of_contact_le_two

/-- Every R point has exactly one positive signed neighbor. -/
theorem R_unique_P_neighbor (a : V → ℤ) (r : V) (hr : r ∈ R G a) :
    ∃! p : V, G.Adj r p ∧ p ∈ P a := by
  have hc : (G.neighborFinset r ∩ P a).card = 1 :=
    (Finset.mem_filter.mp hr).2.2
  simpa only [Finset.card_eq_one_iff_existsUnique, Finset.mem_inter,
    G.mem_neighborFinset] using hc

#print axioms Conway99Formal.Norm16.R_unique_P_neighbor

/-- The same R point has exactly one negative signed neighbor. -/
theorem norm16_R_unique_M_neighbor (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (r : V) (hr : r ∈ R G a) :
    ∃! m : V, G.Adj r m ∧ m ∈ M a := by
  have har : a r = 0 := (Finset.mem_filter.mp hr).2.1
  have hpos : positiveContacts G a r = 1 := (Finset.mem_filter.mp hr).2.2
  have hbal := norm16_zero_contact_balance G h a ha hnorm r har
  have hc : (G.neighborFinset r ∩ M a).card = 1 := by
    simpa only [negativeContacts] using hbal.symm.trans hpos
  simpa only [Finset.card_eq_one_iff_existsUnique, Finset.mem_inter,
    G.mem_neighborFinset] using hc

#print axioms Conway99Formal.Norm16.norm16_R_unique_M_neighbor

/-- The R-to-P neighbor witness has the subtype shape used by signed
attachment equations. -/
theorem R_unique_P_neighbor_subtype (a : V → ℤ)
    (r : {v : V // v ∈ R G a}) :
    ∃! p : {v : V // v ∈ P a}, G.Adj p.1 r.1 := by
  obtain ⟨p, ⟨hpr, hp⟩, huniq⟩ := R_unique_P_neighbor G a r.1 r.2
  refine ⟨⟨p, hp⟩, (G.adj_comm r.1 p).mp hpr, ?_⟩
  intro q hqr
  apply Subtype.ext
  exact huniq q.1 ⟨(G.adj_comm q.1 r.1).mp hqr, q.2⟩

#print axioms Conway99Formal.Norm16.R_unique_P_neighbor_subtype

/-- The matching R-to-M witness uses the same actual R cell. -/
theorem norm16_R_unique_M_neighbor_subtype (h : G.IsSRGWith 99 14 1 2)
    (a : V → ℤ) (ha : IsMinusFourEigenfunction G a) (hnorm : normSq a = 16)
    (r : {v : V // v ∈ R G a}) :
    ∃! m : {v : V // v ∈ M a}, G.Adj m.1 r.1 := by
  obtain ⟨m, ⟨hmr, hm⟩, huniq⟩ :=
    norm16_R_unique_M_neighbor G h a ha hnorm r.1 r.2
  refine ⟨⟨m, hm⟩, (G.adj_comm r.1 m).mp hmr, ?_⟩
  intro q hqr
  apply Subtype.ext
  exact huniq q.1 ⟨(G.adj_comm q.1 r.1).mp hqr, q.2⟩

#print axioms Conway99Formal.Norm16.norm16_R_unique_M_neighbor_subtype

end Conway99Formal.Norm16

set_option autoImplicit false

/-- The norm-sixteen support theorem for one actual Conway-parameter graph
and one integer minus-four eigenfunction on its vertex set. -/
theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : ∀ v, (∑ u : V, G.adjMatrix ℤ v u * a u) = -4 * a v)
    (hnorm : (∑ v : V, a v * a v) = 16) :
    (Finset.univ.filter (fun v => a v = 1)).card = 8 ∧
      (Finset.univ.filter (fun v => a v = -1)).card = 8 := by
  have hresult := Conway99Formal.Norm16.norm16_support_card G h a ha hnorm
  simpa [Conway99Formal.Norm16.P, Conway99Formal.Norm16.M,
    Conway99Formal.Norm16.normSq,
    Conway99Formal.Norm16.IsMinusFourEigenfunction] using hresult

#print axioms solution
