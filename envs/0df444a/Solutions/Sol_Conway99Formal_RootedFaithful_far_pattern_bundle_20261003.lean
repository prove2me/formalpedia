-- Prove2me | solution 1 for Conway99Formal.RootedFaithful.far_pattern_bundle_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:08:38.950864+00:00
-- url     : https://prove2.me/submissions/1237b656-256f-4025-a412-53198715c324

import Mathlib

set_option autoImplicit false
set_option maxErrors 5
set_option maxRecDepth 4096

/-! The fixed local matching and its nonmate-pair incidence coordinates. -/

namespace Conway99Formal.RootedFaithful

open Matrix

/-- The fourteen neighbors of a root, after choosing names for its seven mate edges. -/
abbrev Local := Fin 7 × Bool

/-- The other endpoint of a local matching edge. -/
def mate (x : Local) : Local := (x.1, !x.2)

/-- Two different matching edges, in increasing order. -/
abbrev EdgePair := {ij : Fin 7 × Fin 7 // ij.1 < ij.2}

/-- One endpoint from each of two different matching edges. -/
abbrev FarLabel := EdgePair × Bool × Bool

def leftEndpoint (p : FarLabel) : Local := ((p.1).val.1, p.2.1)
def rightEndpoint (p : FarLabel) : Local := ((p.1).val.2, p.2.2)

/-- The underlying nonmate pair, independent of the coordinate ordering. -/
def endpoints (p : FarLabel) : Finset Local := {leftEndpoint p, rightEndpoint p}

/-- The fixed far-to-local incidence matrix. -/
def incidence : Matrix FarLabel Local ℚ :=
  Matrix.of fun p i => if i ∈ endpoints p then 1 else 0

/-- The adjacency matrix of the seven local matching edges. -/
def matching : Matrix Local Local ℚ :=
  Matrix.of fun i j => if j = mate i then 1 else 0

/-- The rectangular all-ones matrix. -/
def ones (m n α : Type*) [One α] : Matrix m n α := Matrix.of fun _ _ => 1

@[simp] theorem ones_apply {m n α : Type*} [One α] (i : m) (j : n) :
    ones m n α i j = 1 := rfl

/-- There are exactly 84 nonmate pairs among the fourteen local vertices. -/
theorem farLabel_card : Fintype.card FarLabel = 84 := by
  decide

/-- Every coordinate names two distinct, nonmate local vertices. -/
theorem endpoints_valid (p : FarLabel) :
    (endpoints p).card = 2 ∧ ∀ i ∈ endpoints p, mate i ∉ endpoints p := by
  revert p
  decide

/-- The source's unordered nonmate-pair carrier. -/
abbrev UnorderedFarLabel :=
  {s : Finset Local // s.card = 2 ∧ ∀ i ∈ s, mate i ∉ s}

/-- Incidence on the source's unordered nonmate-pair carrier. -/
def unorderedIncidence : Matrix UnorderedFarLabel Local ℚ :=
  Matrix.of fun p i => if i ∈ p.val then 1 else 0

/-- Forget the ordered matching-index presentation. -/
def toUnordered (p : FarLabel) : UnorderedFarLabel :=
  ⟨endpoints p, endpoints_valid p⟩

/-- Distinct coordinate labels name distinct unordered nonmate pairs. -/
theorem toUnordered_injective : Function.Injective toUnordered := by
  intro p q
  revert p q
  decide

/-- Every unordered nonmate pair has an ordered matching-index presentation. -/
theorem toUnordered_surjective : Function.Surjective toUnordered := by
  intro s
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp s.property.1
  have ha : a ∈ s.val := by rw [hs]; simp
  have hb : b ∈ s.val := by rw [hs]; simp
  have hbase : a.1 ≠ b.1 := by
    intro he
    have hmate : mate a ≠ b := by
      exact fun e => (s.property.2 a ha) (e.symm ▸ hb)
    cases a with
    | mk ai av =>
      cases b with
      | mk bi bv =>
        cases av <;> cases bv <;> simp_all [mate]
  rcases lt_or_gt_of_ne hbase with hab' | hba'
  · refine ⟨(⟨(a.1, b.1), hab'⟩, (a.2, b.2)), ?_⟩
    apply Subtype.ext
    simpa [toUnordered, endpoints, leftEndpoint, rightEndpoint] using hs.symm
  · refine ⟨(⟨(b.1, a.1), hba'⟩, (b.2, a.2)), ?_⟩
    apply Subtype.ext
    simpa [toUnordered, endpoints, leftEndpoint, rightEndpoint,
      Finset.pair_comm] using hs.symm

/-- The explicit coordinates and the source's unordered carrier are equivalent. -/
noncomputable def farLabelEquiv : FarLabel ≃ UnorderedFarLabel :=
  Equiv.ofBijective toUnordered ⟨toUnordered_injective, toUnordered_surjective⟩

/-- The source's unordered carrier also has exactly 84 elements. -/
theorem unorderedFarLabel_card : Fintype.card UnorderedFarLabel = 84 := by
  calc
    Fintype.card UnorderedFarLabel = Fintype.card FarLabel :=
      Fintype.card_congr farLabelEquiv.symm
    _ = 84 := farLabel_card

/-- Each far coordinate has exactly two local incidences. -/
theorem incidence_row_sum (p : FarLabel) :
    (∑ i : Local, incidence p i) = 2 := by
  have hn : (∑ i : Local, if i ∈ endpoints p then (1 : ℕ) else 0) = 2 := by
    revert p
    decide
  calc
    (∑ i : Local, incidence p i) =
        ((∑ i : Local, if i ∈ endpoints p then (1 : ℕ) else 0 : ℕ) : ℚ) := by
          simp [incidence]
    _ = 2 := by exact_mod_cast hn

private theorem incidence_overlap_nat (i j : Local) :
    (∑ p : FarLabel,
      (if i ∈ endpoints p then (1 : ℕ) else 0) *
      (if j ∈ endpoints p then (1 : ℕ) else 0)) =
        (if i = j then 12 else if j = mate i then 0 else 1) := by
  revert i j
  decide

/-- No local label is its own mate. -/
theorem mate_ne_self (i : Local) : mate i ≠ i := by
  cases i with
  | mk a b => cases b <;> simp [mate]

/-- Taking the mate twice returns the original local label. -/
theorem mate_mate (i : Local) : mate (mate i) = i := by
  cases i with
  | mk a b => cases b <;> rfl

/-- The local incidence registry has the exact Gram matrix used in the rooted reduction. -/
theorem incidence_gram :
    incidenceᵀ * incidence =
      (11 : ℚ) • (1 : Matrix Local Local ℚ) + ones Local Local ℚ - matching := by
  ext i j
  have hn := incidence_overlap_nat i j
  have hq : (∑ p : FarLabel, incidence p i * incidence p j) =
      (if i = j then 12 else if j = mate i then 0 else 1 : ℚ) := by
    have hterm (p : FarLabel) : incidence p i * incidence p j =
        (((if i ∈ endpoints p then (1 : ℕ) else 0) *
          (if j ∈ endpoints p then (1 : ℕ) else 0) : ℕ) : ℚ) := by
      by_cases hi : i ∈ endpoints p <;> by_cases hj : j ∈ endpoints p <;>
        simp [incidence, hi, hj]
    calc
      (∑ p : FarLabel, incidence p i * incidence p j) =
          (∑ p : FarLabel,
            (((if i ∈ endpoints p then (1 : ℕ) else 0) *
              (if j ∈ endpoints p then (1 : ℕ) else 0) : ℕ) : ℚ)) := by
              exact Finset.sum_congr rfl (fun p _ => hterm p)
      _ = ((∑ p : FarLabel,
            (if i ∈ endpoints p then (1 : ℕ) else 0) *
            (if j ∈ endpoints p then (1 : ℕ) else 0) : ℕ) : ℚ) := by
              rw [Nat.cast_sum]
      _ = _ := by rw [hn]; split_ifs <;> norm_num
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ones_apply, matching, Matrix.of_apply] at ⊢
  rw [hq]
  have hnot : i ≠ mate i := (mate_ne_self i).symm
  by_cases hij : i = j
  · subst j
    simp [hnot]
    norm_num
  · by_cases hm : j = mate i
    · simp [hm, hnot]
    · simp [hij, hm]

/-- The same Gram identity on the unordered carrier used in the source claim. -/
theorem unorderedIncidence_gram :
    unorderedIncidenceᵀ * unorderedIncidence =
      (11 : ℚ) • (1 : Matrix Local Local ℚ) + ones Local Local ℚ - matching := by
  have htransport : unorderedIncidenceᵀ * unorderedIncidence =
      incidenceᵀ * incidence := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    symm
    apply Fintype.sum_equiv farLabelEquiv
    intro p
    rfl
  rw [htransport]
  exact incidence_gram

/-- The local matching is symmetric. -/
theorem matching_symmetric : matchingᵀ = matching := by
  decide

#print axioms Conway99Formal.RootedFaithful.farLabel_card
#print axioms Conway99Formal.RootedFaithful.ones_apply
#print axioms Conway99Formal.RootedFaithful.endpoints_valid
#print axioms Conway99Formal.RootedFaithful.toUnordered_injective
#print axioms Conway99Formal.RootedFaithful.toUnordered_surjective
#print axioms Conway99Formal.RootedFaithful.unorderedFarLabel_card
#print axioms Conway99Formal.RootedFaithful.incidence_row_sum
#print axioms incidence_overlap_nat
#print axioms Conway99Formal.RootedFaithful.incidence_gram
#print axioms Conway99Formal.RootedFaithful.unorderedIncidence_gram
#print axioms Conway99Formal.RootedFaithful.matching_symmetric
#print axioms Conway99Formal.RootedFaithful.mate_ne_self
#print axioms Conway99Formal.RootedFaithful.mate_mate

end Conway99Formal.RootedFaithful


set_option autoImplicit false

/-! The adjacent-endpoint version of the rooted common-witness claim. -/

namespace Conway99Formal.RootedFaithful

open SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices outside the root and its neighborhood. -/
def isFar (r x : V) : Prop := x ≠ r ∧ ¬ G.Adj r x

/-- The source's far layer as a finite set. -/
def farVertices [DecidableEq V] (r : V) : Finset V :=
  Finset.univ \ insert r (G.neighborFinset r)

theorem mem_farVertices_iff [DecidableEq V] (r x : V) :
    x ∈ farVertices G r ↔ isFar G r x := by
  simp [farVertices, isFar, G.mem_neighborFinset, ne_comm]

/-- Every root has exactly 84 far vertices in the same graph. -/
theorem farVertices_card [DecidableEq V] (h : G.IsSRGWith 99 14 1 2)
    (r : V) : (farVertices G r).card = 84 := by
  have hr : r ∉ G.neighborFinset r := by simp
  have hnear : (G.neighborFinset r).card = 14 := by
    simpa only [G.card_neighborFinset_eq_degree] using h.regular.degree_eq r
  have hroot : (insert r (G.neighborFinset r)).card = 15 := by
    rw [Finset.card_insert_of_notMem hr, hnear]
  have hfar : (farVertices G r).card =
      Fintype.card V - (insert r (G.neighborFinset r)).card := by
    simpa [farVertices] using
      (Finset.card_sdiff_of_subset
        (Finset.subset_univ (insert r (G.neighborFinset r))))
  rw [h.card, hroot] at hfar
  omega

/-- Every far vertex has exactly two neighbors in the root neighborhood. -/
theorem farLocalCard (h : G.IsSRGWith 99 14 1 2) (r x : V)
    (hx : isFar G r x) : Fintype.card (G.commonNeighbors r x) = 2 :=
  h.of_not_adj hx.1.symm hx.2

/-- The two local neighbors of a far vertex belong to different matching edges. -/
theorem farLocalNonadjacent (h : G.IsSRGWith 99 14 1 2)
    (r x a b : V) (hx : isFar G r x)
    (hra : G.Adj r a) (hrb : G.Adj r b)
    (hax : G.Adj a x) (hbx : G.Adj b x) : ¬ G.Adj a b := by
  intro hab
  have hrMem : r ∈ G.commonNeighbors a b :=
    G.mem_commonNeighbors.mpr ⟨hra.symm, hrb.symm⟩
  have hxMem : x ∈ G.commonNeighbors a b :=
    G.mem_commonNeighbors.mpr ⟨hax, hbx⟩
  have hcard : Fintype.card (G.commonNeighbors a b) = 1 :=
    h.of_adj a b hab
  have hsub : Subsingleton (G.commonNeighbors a b) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have e : r = x := congrArg Subtype.val
    (Subsingleton.elim (⟨r, hrMem⟩ : G.commonNeighbors a b)
      (⟨x, hxMem⟩ : G.commonNeighbors a b))
  exact hx.1 e.symm

/-- A far vertex is determined by its two actual neighbors in the root neighborhood. -/
theorem farLocalPattern_injective (h : G.IsSRGWith 99 14 1 2)
    (r x y : V) (hx : isFar G r x) (hy : isFar G r y)
    (hpattern : G.commonNeighbors r x = G.commonNeighbors r y) : x = y := by
  have hcard : (G.commonNeighbors r x).ncard = 2 := by
    simpa only [Set.fintypeCard_eq_ncard] using farLocalCard G h r x hx
  obtain ⟨a, b, hab, hpair⟩ := Set.ncard_eq_two.mp hcard
  have ha_mem : a ∈ G.commonNeighbors r x := by rw [hpair]; simp
  have hb_mem : b ∈ G.commonNeighbors r x := by rw [hpair]; simp
  obtain ⟨hra, hxa⟩ := G.mem_commonNeighbors.mp ha_mem
  obtain ⟨hrb, hxb⟩ := G.mem_commonNeighbors.mp hb_mem
  have hnot : ¬ G.Adj a b :=
    farLocalNonadjacent G h r x a b hx hra hrb hxa.symm hxb.symm
  have htwo : (G.commonNeighbors a b).ncard = 2 := by
    simpa only [Set.fintypeCard_eq_ncard] using h.of_not_adj hab hnot
  have hsubset : ({r, x} : Set V) ⊆ G.commonNeighbors a b := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact G.mem_commonNeighbors.mpr ⟨hra.symm, hrb.symm⟩
    · exact G.mem_commonNeighbors.mpr ⟨hxa.symm, hxb.symm⟩
  have hpair_ab : ({r, x} : Set V) = G.commonNeighbors a b := by
    apply Set.eq_of_subset_of_ncard_le hsubset
    rw [Set.ncard_pair hx.1.symm]
    exact htwo.le
  have ha_mem_y : a ∈ G.commonNeighbors r y := hpattern ▸ ha_mem
  have hb_mem_y : b ∈ G.commonNeighbors r y := hpattern ▸ hb_mem
  have hya := (G.mem_commonNeighbors.mp ha_mem_y).2
  have hyb := (G.mem_commonNeighbors.mp hb_mem_y).2
  have hy_mem : y ∈ G.commonNeighbors a b :=
    G.mem_commonNeighbors.mpr ⟨hya.symm, hyb.symm⟩
  have hy_pair : y = r ∨ y = x := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hpair_ab.symm ▸ hy_mem : y ∈ ({r, x} : Set V))
  exact hy_pair.resolve_left hy.1 |>.symm

/-- An adjacent pair of far vertices and their common far witness cannot share a local
neighbor with either endpoint as stated: the edge has only one common neighbor. -/
theorem commonWitnessDisjointness (h : G.IsSRGWith 99 14 1 2)
    (r x y z a : V)
    (_hx : isFar G r x) (hy : isFar G r y) (_hz : isFar G r z)
    (hxy : G.Adj x y) (hzx : G.Adj z x) (hzy : G.Adj z y)
    (ha : G.Adj r a) : ¬ (G.Adj a x ∧ G.Adj a z) := by
  rintro ⟨hax, haz⟩
  have hyMem : y ∈ G.commonNeighbors x z :=
    G.mem_commonNeighbors.mpr ⟨hxy, hzy⟩
  have haMem : a ∈ G.commonNeighbors x z :=
    G.mem_commonNeighbors.mpr ⟨hax.symm, haz.symm⟩
  have hcard : Fintype.card (G.commonNeighbors x z) = 1 :=
    h.of_adj x z hzx.symm
  have hsub : Subsingleton (G.commonNeighbors x z) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have e : y = a := congrArg Subtype.val
    (Subsingleton.elim (⟨y, hyMem⟩ : G.commonNeighbors x z)
      (⟨a, haMem⟩ : G.commonNeighbors x z))
  exact hy.2 (by simpa [e] using ha)

/-- The adjacent-endpoint claim in the source's far-set presentation. -/
theorem commonWitnessDisjointnessFarSet [DecidableEq V] (h : G.IsSRGWith 99 14 1 2)
    (r x y z a : V)
    (hx : x ∈ farVertices G r) (hy : y ∈ farVertices G r)
    (hz : z ∈ farVertices G r)
    (hxy : G.Adj x y) (hzx : G.Adj z x) (hzy : G.Adj z y)
    (ha : G.Adj r a) : ¬ (G.Adj a x ∧ G.Adj a z) :=
  commonWitnessDisjointness G h r x y z a
    ((mem_farVertices_iff G r x).mp hx)
    ((mem_farVertices_iff G r y).mp hy)
    ((mem_farVertices_iff G r z).mp hz)
    hxy hzx hzy ha

#print axioms Conway99Formal.RootedFaithful.commonWitnessDisjointness
#print axioms Conway99Formal.RootedFaithful.farLocalCard
#print axioms Conway99Formal.RootedFaithful.farLocalNonadjacent
#print axioms Conway99Formal.RootedFaithful.farLocalPattern_injective
#print axioms Conway99Formal.RootedFaithful.mem_farVertices_iff
#print axioms Conway99Formal.RootedFaithful.farVertices_card
#print axioms Conway99Formal.RootedFaithful.commonWitnessDisjointnessFarSet

end Conway99Formal.RootedFaithful

/-- A graph-owned bundle of necessary conditions for the rooted far layer. -/
theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (r : V) :
    ((Finset.univ \ insert r (G.neighborFinset r)).card = 84) ∧
    (∀ x, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      Fintype.card (G.commonNeighbors r x) = 2) ∧
    (∀ x y, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      y ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      G.commonNeighbors r x = G.commonNeighbors r y → x = y) ∧
    (∀ x a b, x ∈ (Finset.univ \ insert r (G.neighborFinset r)) →
      a ∈ G.commonNeighbors r x → b ∈ G.commonNeighbors r x →
      ¬ G.Adj a b) := by
  refine ⟨Conway99Formal.RootedFaithful.farVertices_card G h r, ?_, ?_, ?_⟩
  · intro x hx
    exact Conway99Formal.RootedFaithful.farLocalCard G h r x
      ((Conway99Formal.RootedFaithful.mem_farVertices_iff G r x).mp hx)
  · intro x y hx hy hpattern
    exact Conway99Formal.RootedFaithful.farLocalPattern_injective G h r x y
      ((Conway99Formal.RootedFaithful.mem_farVertices_iff G r x).mp hx)
      ((Conway99Formal.RootedFaithful.mem_farVertices_iff G r y).mp hy) hpattern
  · intro x a b hx ha hb
    obtain ⟨hra, hxa⟩ := G.mem_commonNeighbors.mp ha
    obtain ⟨hrb, hxb⟩ := G.mem_commonNeighbors.mp hb
    exact Conway99Formal.RootedFaithful.farLocalNonadjacent G h r x a b
      ((Conway99Formal.RootedFaithful.mem_farVertices_iff G r x).mp hx)
      hra hrb hxa.symm hxb.symm

#print axioms solution
