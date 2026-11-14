-- Prove2me | solution 1 for F3SubsetSum.proposition_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T23:12:53.152396+00:00
-- url     : https://prove2.me/submissions/9e350659-a313-4fdc-8df1-43fee66a4518

import Definitions.Def_F3SubsetSum_RelationSpace
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open F3SubsetSum MvPolynomial
open scoped BigOperators

namespace Prop49Proof

section
variable {q n m : ℕ} [Fact q.Prime]

private noncomputable def rIndex (q : ℕ) (s : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => redExp q (s j)

private lemma rIndex_apply (s : Fin n →₀ ℕ) (j : Fin n) :
    rIndex q s j = redExp q (s j) := by simp [rIndex]

private lemma redExp_le (q e : ℕ) (hq : 2 ≤ q) : redExp q e ≤ e := by
  unfold redExp
  split_ifs with h
  · exact le_rfl
  · have hh := Nat.mod_le (e - 1) (q - 1)
    omega

private lemma redExp_lt (hq : 2 ≤ q) (e : ℕ) : redExp q e < q := by
  unfold redExp
  split_ifs with h
  · exact h
  · have hh := Nat.mod_lt (e - 1) (show 0 < q - 1 by omega)
    omega

private lemma rIndex_reduced (hq : 2 ≤ q) (s : Fin n →₀ ℕ) :
    ∀ j, rIndex q s j < q := by
  intro j
  rw [rIndex_apply]
  exact redExp_lt hq _

private lemma rIndex_le (s : Fin n →₀ ℕ) : rIndex q s ≤ s := by
  intro j
  rw [rIndex_apply]
  exact redExp_le _ _ (Fact.out : q.Prime).two_le

private lemma rIndex_self (s : Fin n →₀ ℕ) (hs : ∀ j, s j < q) :
    rIndex q s = s := by
  ext j
  simp [rIndex_apply, redExp, hs j]

private noncomputable def redL (q n : ℕ) :
    MvPolynomial (Fin n) (ZMod q) →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q) :=
  (Finsupp.lsum (ZMod q) (fun s : Fin n →₀ ℕ =>
    (monomial (rIndex q s) : ZMod q →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod q)).toLinearMap

private lemma redL_apply (p : MvPolynomial (Fin n) (ZMod q)) :
    redL q n p = red q p := rfl

private lemma red_monomial (s : Fin n →₀ ℕ) (c : ZMod q) :
    red q (monomial s c) = monomial (rIndex q s) c := by
  change (Finsupp.lsum (ZMod q) (fun s : Fin n →₀ ℕ =>
    (monomial (rIndex q s) : ZMod q →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q))))
      (Finsupp.single s c) = _
  exact Finsupp.lsum_single _ _ _ _

private lemma low_mem (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q)) :
    p ∈ lowSpan q n D ↔
      ∀ s ∈ p.support, (∀ j, s j < q) ∧ ∑ j, s j < D := by
  classical
  let E : Set (Fin n →₀ ℕ) := {s | (∀ j, s j < q) ∧ ∑ j, s j < D}
  have hE : lowSpan q n D = MvPolynomial.restrictSupport (ZMod q) E := by
    rw [MvPolynomial.restrictSupport_eq_span]
    unfold lowSpan
    congr 1
    ext v
    constructor
    · rintro ⟨s, hs, hd, rfl⟩
      exact ⟨s, ⟨hs, hd⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hd⟩, rfl⟩
      exact ⟨s, hs, hd, rfl⟩
  rw [hE, MvPolynomial.mem_restrictSupport_iff]
  rfl

private lemma monomial_low (D : ℕ) (s : Fin n →₀ ℕ) (c : ZMod q)
    (hs : ∀ j, s j < q) (hd : ∑ j, s j < D) :
    monomial s c ∈ lowSpan q n D := by
  have h : monomial s (1 : ZMod q) ∈ lowSpan q n D :=
    Submodule.subset_span ⟨s, hs, hd, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (lowSpan q n D).smul_mem c h

private noncomputable def tauL (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    MvPolynomial (Fin n) (ZMod q) →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q) := by
  classical
  exact (Finsupp.lsum (ZMod q) (fun s =>
    if ∑ j, s j < D then monomial s
    else if h : (∀ j, s j < q) ∧ ∑ j, s j = D then
      LinearMap.toSpanSingleton (ZMod q) _
        (remainder A b D Q ⟨fun j => ⟨s j, h.1 j⟩, h.2⟩)
    else 0)).comp (AddMonoidAlgebra.coeffLinearEquiv (ZMod q)).toLinearMap

private lemma tauL_apply (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q)) :
    tauL A b D Q p = tau A b D Q p := by
  classical
  unfold tauL tau
  simp only [LinearMap.comp_apply, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> rfl


private lemma degree_of_support (p : MvPolynomial (Fin n) (ZMod q))
    (s : Fin n →₀ ℕ) (hs : s ∈ p.support) : ∑ j, s j ≤ p.totalDegree := by
  simpa [Finsupp.sum_fintype] using (MvPolynomial.le_totalDegree hs)

private lemma rIndex_top (s t : Fin n →₀ ℕ)
    (hdeg : ∑ j, s j ≤ ∑ j, t j) (heq : rIndex q s = t) : s = t := by
  classical
  ext j
  have hle : ∀ i, t i ≤ s i := by intro i; rw [← heq]; exact rIndex_le s i
  by_contra hj
  have hjlt : t j < s j := lt_of_le_of_ne (hle j) (Ne.symm hj)
  have hsum := Finset.sum_lt_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
    ⟨j, Finset.mem_univ _, hjlt⟩
  omega

private lemma red_supported (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p.totalDegree ≤ D) :
    red q p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D} := by
  classical
  have hexp : red q p = ∑ s ∈ p.support, red q (monomial s (coeff s p)) := by
    change redL q n p = ∑ s ∈ p.support, redL q n (monomial s (coeff s p))
    rw [← map_sum, ← as_sum p]
  rw [hexp]
  apply Submodule.sum_mem
  intro s hs
  rw [red_monomial, monomial_mem_restrictSupport]
  left
  exact ⟨rIndex_reduced (Fact.out : q.Prime).two_le s,
    (Finset.sum_le_sum (fun j _ => rIndex_le s j)).trans ((degree_of_support p s hs).trans hp)⟩

private lemma red_coeff_top (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p.totalDegree ≤ D) (t : Fin n →₀ ℕ)
    (ht : ∀ j, t j < q) (htD : ∑ j, t j = D) :
    coeff t (red q p) = coeff t p := by
  classical
  have hexp : red q p = ∑ s ∈ p.support, red q (monomial s (coeff s p)) := by
    change redL q n p = ∑ s ∈ p.support, redL q n (monomial s (coeff s p))
    rw [← map_sum, ← as_sum p]
  rw [hexp, coeff_sum]
  calc
    _ = coeff t (red q (monomial t (coeff t p))) := Finset.sum_eq_single (s := p.support)
      (f := fun s => coeff t (red q (monomial s (coeff s p)))) t (by
      intro s hs hst
      rw [red_monomial, coeff_monomial]
      have hne : rIndex q s ≠ t := by
        intro he
        exact hst (rIndex_top s t (by rw [htD]; exact (degree_of_support p s hs).trans hp) he)
      simp [hne]) (by
      intro ht'
      rw [notMem_support_iff.mp ht']
      simp [red])
    _ = coeff t p := by rw [red_monomial, rIndex_self t ht]; simp

private lemma toPoly_degree (d : ℕ) (v : Rd (ZMod q) n q d) :
    (Rd.toPoly (ZMod q) n q d v).totalDegree ≤ d := by
  classical
  simp only [Rd.toPoly, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply totalDegree_finsetSum_le
  intro α _
  have h := totalDegree_monomial_le α.toFinsupp (v α)
  simpa [ReducedMono.toFinsupp, Finsupp.sum_fintype, α.property] using h

private lemma linForm_degree (a : Fin n → ZMod q) : (linForm a).totalDegree ≤ 1 := by
  classical
  unfold linForm
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

private lemma fPoly_degree (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (i : Fin m) : (fPoly A b i).totalDegree ≤ 2 := by
  have hL := linForm_degree (cols A i)
  unfold fPoly
  apply (totalDegree_mul _ _).trans
  have h₁ := (totalDegree_sub_C_le (linForm (cols A i)) (b i)).trans hL
  have h₂ := totalDegree_add (linForm (cols A i) - C (b i)) 1
  simp only [totalDegree_one, Nat.max_zero] at h₂
  exact (Nat.add_le_add h₁ (h₂.trans h₁)).trans (by decide)

private lemma fPoly_error_degree (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (i : Fin m) :
    (fPoly A b i - linForm (cols A i) ^ 2).totalDegree ≤ 1 := by
  have he : fPoly A b i - linForm (cols A i) ^ 2 =
      (1 - C (2 * b i)) * linForm (cols A i) + C ((b i) ^ 2 - b i) := by
    unfold fPoly
    simp only [map_sub, map_mul, map_ofNat, map_pow]
    ring
  rw [he]
  apply (totalDegree_add _ _).trans
  have hc : (1 - C (2 * b i) : MvPolynomial (Fin n) (ZMod q)).totalDegree = 0 := by
    rw [← map_one C, ← map_sub, totalDegree_C]
  have hm := totalDegree_mul (1 - C (2 * b i)) (linForm (cols A i))
  rw [hc, zero_add] at hm
  exact max_le (hm.trans (linForm_degree _)) (by rw [totalDegree_C]; omega)

private lemma remainder_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (α : ReducedMono n q D) : remainder A b D Q α ∈ lowSpan q n D := by
  classical
  let p := ∑ i, fPoly A b i * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)
  let p₂ := ∑ i, linForm (cols A i) ^ 2 * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)
  have hp : p.totalDegree ≤ D := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add (fPoly_degree A b i)
      (toPoly_degree _ _)).trans (by omega))
  have herror : (p - p₂).totalDegree < D := by
    have he : p - p₂ = ∑ i, (fPoly A b i - linForm (cols A i) ^ 2) *
        Rd.toPoly (ZMod q) n q (D - 2) (Q α i) := by
      simp [p, p₂, Finset.sum_sub_distrib, sub_mul]
    rw [he]
    apply lt_of_le_of_lt (totalDegree_finsetSum_le (d := D - 1) ?_) (by omega)
    intro i _
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add (fPoly_error_degree A b i)
      (toPoly_degree _ _)).trans (by omega))
  have htop (β : ReducedMono n q D) : coeff β.toFinsupp p = (Pi.single α (1 : ZMod q) : Rd (ZMod q) n q D) β := by
    have he : coeff β.toFinsupp (p - p₂) = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by
        change (p - p₂).totalDegree < β.toFinsupp.sum (fun _ e => e)
        rw [Finsupp.sum_fintype]
        simpa [ReducedMono.toFinsupp, β.property] using herror
        intro j; rfl)
    have hh := congrFun (hQ α) β
    rw [coeff_sub] at he
    apply (sub_eq_zero.mp he).trans
    simpa [Phi, mulMap, Rd.ofPoly, p₂, coeff_sum] using hh
  apply (low_mem D _).mpr
  intro s hs
  have hsnon : coeff s (remainder A b D Q α) ≠ 0 := mem_support_iff.mp hs
  have hsr : coeff s (monomial α.toFinsupp (1 : ZMod q)) ≠ 0 ∨ coeff s (red q p) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hsnon
    change coeff s (monomial α.toFinsupp 1 - red q p) = 0
    rw [coeff_sub, hn.1, hn.2, sub_self]
  have hsbound : (∀ j, s j < q) ∧ ∑ j, s j ≤ D := by
    rcases hsr with ha | ha
    · have he : α.toFinsupp = s := by simpa only [coeff_monomial, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] using ha
      subst s
      exact ⟨fun j => by simpa [ReducedMono.toFinsupp] using (α.val j).isLt,
        by simp [ReducedMono.toFinsupp, Finsupp.sum_fintype, α.property]⟩
    · exact ((mem_restrictSupport_iff (ZMod q)).mp (red_supported D p hp)) (mem_support_iff.mpr ha)
  refine ⟨hsbound.1, lt_of_le_of_ne hsbound.2 ?_⟩
  intro hsd
  let β : ReducedMono n q D := ⟨fun j => ⟨s j, hsbound.1 j⟩, hsd⟩
  have hb : β.toFinsupp = s := by ext j; simp [β, ReducedMono.toFinsupp]
  apply hsnon
  change coeff s (monomial α.toFinsupp 1 - red q p) = 0
  rw [coeff_sub, red_coeff_top D p hp s hsbound.1 hsd, ← hb, htop β]
  have hi : α.toFinsupp = β.toFinsupp ↔ α = β := by
    constructor
    · intro h; apply Subtype.ext; funext j; apply Fin.ext
      simpa [ReducedMono.toFinsupp] using congrArg (fun t => t j) h
    · rintro rfl; rfl
  simp [coeff_monomial, Pi.single_apply, hi, eq_comm]


private lemma red_fixed (p : MvPolynomial (Fin n) (ZMod q))
    (hp : ∀ s ∈ p.support, ∀ j, s j < q) : red q p = p := by
  classical
  unfold red
  conv_rhs => rw [as_sum p]
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun t => monomial t (coeff s p)) (rIndex_self s (hp s hs))

private lemma tau_fixed (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ lowSpan q n D) : tau A b D Q p = p := by
  classical
  unfold tau
  conv_rhs => rw [as_sum p]
  apply Finset.sum_congr rfl
  intro s hs
  rw [if_pos (((low_mem D p).mp hp s hs).2)]

private lemma low_degree (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ lowSpan q n D) : p.totalDegree ≤ D - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have h := ((low_mem D p).mp hp s hs).2
  simpa [Finsupp.sum_fintype] using (show ∑ j, s j ≤ D - 1 by omega)

private lemma tau_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D}) :
    tau A b D Q p ∈ lowSpan q n D := by
  classical
  unfold tau
  apply Submodule.sum_mem
  intro s hs
  have hsp := (mem_restrictSupport_iff (ZMod q)).mp hp hs
  split_ifs with hlt heq
  · exact monomial_low D s _ hsp.1 hlt
  · exact (lowSpan q n D).smul_mem _ (remainder_low A b D hD Q hQ _)
  · exact (lowSpan q n D).zero_mem

private noncomputable def XL (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) (j : Fin n) :
    Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  (tauL A b D Q).comp ((redL q n).comp (LinearMap.mulLeft (ZMod q) (X j)))

private lemma XL_apply (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) : XL A b D Q j p = Xop A b D Q j p := by
  simp [XL, Xop, redL_apply, tauL_apply]

private lemma Xop_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D) :
    Xop A b D Q j p ∈ lowSpan q n D := by
  apply tau_low A b D hD Q hQ
  apply red_supported
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have hh := low_degree D p hp
    omega)

private lemma Xop_fixed (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : X j * p ∈ lowSpan q n D) : Xop A b D Q j p = X j * p := by
  unfold Xop
  rw [red_fixed _ (fun s hs => ((low_mem D _).mp hp s hs).1)]
  exact tau_fixed A b D Q _ hp

end

section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

private lemma field_product (j : Fin n) :
    (∏ a : K, (X j - C a : MvPolynomial (Fin n) K)) =
      X j ^ Fintype.card K - X j := by
  classical
  have hc : (1 : ℕ) < Fintype.card K := Fintype.one_lt_card
  have hp : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub (by simpa using hc)
  have hr : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).roots.card =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X]
    simp [FiniteField.X_pow_card_sub_X_natDegree_eq K hc]
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hr
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  have he := congrArg (Polynomial.aeval (X j : MvPolynomial (Fin n) K)) h
  simpa using he

-- Alon's grid Nullstellensatz identifies polynomials vanishing on the full grid.
private lemma vanishes_grid_mem (I : Ideal (MvPolynomial (Fin n) K))
    (hI : ∀ j, X j ^ Fintype.card K - X j ∈ I)
    (p : MvPolynomial (Fin n) K) (hp : ∀ u : Fin n → K, eval u p = 0) : p ∈ I := by
  classical
  obtain ⟨h, _, heq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : Fin n => (Finset.univ : Finset K)) (fun _ => Finset.univ_nonempty) p (fun u _ => hp u)
  rw [heq, Finsupp.linearCombination_apply]
  apply I.sum_mem
  intro j _
  change h j * (∏ a : K, (X j - C a)) ∈ I
  rw [field_product]
  exact I.mul_mem_left _ (hI j)

end

section
variable {q n m : ℕ} [Fact q.Prime]
variable (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q)

omit [Fact q.Prime] in
private lemma sample_mem (i : Fin m) : fPoly A b i ∈ idealJ A b :=
  Ideal.subset_span (Or.inl ⟨i, rfl⟩)

private lemma eval_zero_of_mem {u : Fin n → ZMod q} (hu : u ∈ candidates A b)
    {p : MvPolynomial (Fin n) (ZMod q)} (hp : p ∈ idealJ A b) : eval u p = 0 := by
  have h : idealJ A b ≤ RingHom.ker (eval u) := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hu i
    · simp [RingHom.mem_ker, ZMod.pow_card]
  exact h hp

private lemma grid_vanish_mem {p : MvPolynomial (Fin n) (ZMod q)}
    (hp : ∀ u, eval u p = 0) : p ∈ idealJ A b := by
  apply vanishes_grid_mem (idealJ A b) _ p hp
  intro j
  rw [ZMod.card]
  exact Ideal.subset_span (Or.inr ⟨j, rfl⟩)

private lemma interpolation_mem (p : MvPolynomial (Fin n) (ZMod q)) :
    p - ∑ u : Fin n → ZMod q, C (eval u p) * indicator u ∈ idealJ A b := by
  classical
  apply grid_vanish_mem A b
  intro u
  simp only [map_sub, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single u]
  · simp [eval_indicator_apply_eq_one]
  · intro v _ hv
    rw [eval_indicator_apply_eq_zero u v hv.symm, mul_zero]
  · simp

-- An indicator outside the candidate set is killed by one sample equation.
private lemma indicator_mem_of_not_candidate (u : Fin n → ZMod q)
    (hu : u ∉ candidates A b) : indicator u ∈ idealJ A b := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, eval u (fPoly A b i) ≠ 0 := by
    simpa only [candidates, Set.mem_ofPred_eq, not_forall] using hu
  let c := eval u (fPoly A b i)
  have h : C c * indicator u - fPoly A b i * indicator u ∈ idealJ A b := by
    apply grid_vanish_mem A b
    intro v
    by_cases hv : v = u
    · subst v
      simp [c]
    · simp [eval_indicator_apply_eq_zero v u hv]
  have hprod : C c * indicator u ∈ idealJ A b :=
    by simpa only [sub_add_cancel] using
      (idealJ A b).add_mem h ((idealJ A b).mul_mem_right (indicator u) (sample_mem A b i))
  have hc : c ≠ 0 := hi
  have hscaled := (idealJ A b).mul_mem_left (C c⁻¹) hprod
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hscaled

-- Interpolation now identifies J with the kernel of evaluation on candidates.
private lemma mem_ideal_iff (p : MvPolynomial (Fin n) (ZMod q)) :
    p ∈ idealJ A b ↔ ∀ u ∈ candidates A b, eval u p = 0 := by
  classical
  constructor
  · exact fun hp u hu => eval_zero_of_mem A b hu hp
  · intro hp
    have hsum : (∑ u : Fin n → ZMod q, C (eval u p) * indicator u) ∈ idealJ A b := by
      apply (idealJ A b).sum_mem
      intro u _
      by_cases hu : u ∈ candidates A b
      · simp [hp u hu]
      · exact (idealJ A b).mul_mem_left _ (indicator_mem_of_not_candidate A b u hu)
    have h := (idealJ A b).add_mem (interpolation_mem A b p) hsum
    simpa only [sub_add_cancel] using h



private lemma pow_redExp (x : ZMod q) (e : ℕ) : x ^ redExp q e = x ^ e := by
  unfold redExp
  split_ifs with he
  · rfl
  · have hepos : 0 < e := by have := (Fact.out : q.Prime).two_le; omega
    by_cases hx : x = 0
    · subst x
      simp [Nat.ne_of_gt hepos]
    · rw [pow_add, pow_one, ← pow_eq_pow_mod (e - 1) (ZMod.pow_card_sub_one_eq_one hx),
        pow_sub_one_mul (Nat.ne_of_gt hepos)]

private lemma eval_red (p : MvPolynomial (Fin n) (ZMod q)) (u : Fin n → ZMod q) :
    eval u (red q p) = eval u p := by
  classical
  unfold red
  rw [map_sum]
  conv_rhs => rw [as_sum p, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro j; simp),
    Finsupp.prod_fintype _ _ (by intro j; simp)]
  apply Finset.prod_congr rfl
  intro j _
  simp [pow_redExp]

private lemma red_mod (p : MvPolynomial (Fin n) (ZMod q)) :
    Ideal.Quotient.mk (idealJ A b) (red q p) = Ideal.Quotient.mk (idealJ A b) p := by
  apply (sub_eq_zero.mp ?_)
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply grid_vanish_mem A b
  intro u
  simp [eval_red]

private lemma remainder_mod (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (α : ReducedMono n q D) :
    Ideal.Quotient.mk (idealJ A b) (remainder A b D Q α) =
      Ideal.Quotient.mk (idealJ A b) (monomial α.toFinsupp 1) := by
  unfold remainder
  rw [map_sub, red_mod A b]
  have hz : (∑ i, fPoly A b i * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)) ∈ idealJ A b := by
    apply (idealJ A b).sum_mem
    intro i _
    exact (idealJ A b).mul_mem_right _ (sample_mem A b i)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, sub_zero]

private lemma tau_mod (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D}) :
    Ideal.Quotient.mk (idealJ A b) (tau A b D Q p) = Ideal.Quotient.mk (idealJ A b) p := by
  classical
  unfold tau
  rw [map_sum]
  conv_rhs => rw [as_sum p, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsp := (mem_restrictSupport_iff (ZMod q)).mp hp hs
  split_ifs with hlt heq
  · rfl
  · let α : ReducedMono n q D := ⟨fun j => ⟨s j, heq.1 j⟩, heq.2⟩
    have hi : α.toFinsupp = s := by ext j; simp [α, ReducedMono.toFinsupp]
    change Ideal.Quotient.mk (idealJ A b) (coeff s p • remainder A b D Q α) = _
    change (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) _ = _
    have hh : (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (remainder A b D Q α) =
        (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (monomial α.toFinsupp 1) := remainder_mod A b D Q α
    rw [map_smul, hh, hi, ← map_smul]
    simp only [smul_monomial, smul_eq_mul, mul_one]
    rfl
  · have hsle : ∑ j, s j ≤ D := hsp.2
    exact False.elim (heq ⟨hsp.1, by omega⟩)

private lemma Xop_mod (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D) :
    Ideal.Quotient.mk (idealJ A b) (Xop A b D Q j p) =
      Ideal.Quotient.mk (idealJ A b) (X j * p) := by
  unfold Xop
  rw [tau_mod A b D Q, red_mod A b]
  apply red_supported
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have hh := low_degree D p hp
    omega)


private lemma relSpace_le (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (T : Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q)))
    (h₀ : relN0 A b D Q ≤ T)
    (hX : ∀ j, ∀ v ∈ T, Xop A b D Q j v ∈ T) : relSpace A b D Q ≤ T := by
  apply iSup_le
  intro r
  induction r with
  | zero => exact h₀
  | succ r ih =>
    change relNr A b D Q r ⊔ _ ≤ T
    refine sup_le ih (Submodule.span_le.mpr ?_)
    rintro w ⟨j, v, hv, rfl⟩
    exact hX j v (ih hv)

private lemma relNr_mono (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    Monotone (relNr A b D Q) := by
  apply monotone_nat_of_le_succ
  intro r
  exact le_sup_left

private lemma Xop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ relSpace A b D Q) :
    Xop A b D Q j v ∈ relSpace A b D Q := by
  obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _ (relNr_mono A b D Q).directed_le).mp hv
  apply (le_iSup (relNr A b D Q) (r + 1))
  apply (show Submodule.span (ZMod q) {w | ∃ j, ∃ v ∈ relNr A b D Q r,
      w = Xop A b D Q j v} ≤ relNr A b D Q (r + 1) from le_sup_right)
  exact Submodule.subset_span ⟨j, v, hr, rfl⟩

private lemma relN0_le_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    relN0 A b D Q ≤ relSpace A b D Q := le_iSup (relNr A b D Q) 0

private lemma iterate_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (r : ℕ) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Xop A b D Q j)^[r] v ∈ lowSpan q n D := by
  induction r with
  | zero => exact hv
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact Xop_low A b D hD Q hQ j _ ih

private lemma Lop_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Lop A b D Q i v ∈ lowSpan q n D := by
  apply Submodule.sum_mem
  intro j _
  exact (lowSpan q n D).smul_mem _ (Xop_low A b D hD Q hQ j v hv)

private lemma relSpace_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    relSpace A b D Q ≤ lowSpan q n D := by
  apply relSpace_le A b D Q
  · apply Submodule.span_le.mpr
    rintro w ((⟨j, k, _, v, hv, rfl⟩ | ⟨j, v, hv, rfl⟩) | ⟨i, v, hv, rfl⟩)
    · exact (lowSpan q n D).sub_mem
        (Xop_low A b D hD Q hQ j _ (Xop_low A b D hD Q hQ k v hv))
        (Xop_low A b D hD Q hQ k _ (Xop_low A b D hD Q hQ j v hv))
    · exact (lowSpan q n D).sub_mem (iterate_low A b D hD Q hQ j q v hv)
        (Xop_low A b D hD Q hQ j v hv)
    · let w := Lop A b D Q i v - b i • v + v
      have hw : w ∈ lowSpan q n D := (lowSpan q n D).add_mem
        ((lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i v hv)
          ((lowSpan q n D).smul_mem _ hv)) hv
      exact (lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i w hw)
        ((lowSpan q n D).smul_mem _ hw)
  · exact Xop_low A b D hD Q hQ

private lemma quot_Xop (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (Xop A b D Q j v) =
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (X j) *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  change Ideal.Quotient.mk _ (Xop A b D Q j v) = _
  rw [Xop_mod A b D hD Q j v hv, map_mul]
  rfl

private lemma quot_iterate (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (r : ℕ) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) ((Xop A b D Q j)^[r] v) =
      ((Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (X j)) ^ r *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', quot_Xop A b D hD Q j _ (iterate_low A b D hD Q hQ j r v hv), ih]
    rw [pow_succ']; ring

private lemma quot_Lop (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (Lop A b D Q i v) =
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (linForm (cols A i)) *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  classical
  let f := Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)
  change f (∑ j, A j i • Xop A b D Q j v) = f (∑ j, C (A j i) * X j) * f v
  rw [map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change A j i • f (Xop A b D Q j v) = f (C (A j i) * X j) * f v
  rw [map_mul, show f (Xop A b D Q j v) = f (X j) * f v from quot_Xop A b D hD Q j v hv]
  rw [show f (C (A j i)) = algebraMap (ZMod q) _ (A j i) from f.commutes _]
  exact (Algebra.smul_def (R := ZMod q) _ _).trans (mul_assoc _ _ _).symm


private lemma relSpace_mod (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    relSpace A b D Q ≤ LinearMap.ker (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)).toLinearMap := by
  classical
  let f := Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)
  have h₀ : relN0 A b D Q ≤ LinearMap.ker f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro w ((⟨j, k, _, v, hv, rfl⟩ | ⟨j, v, hv, rfl⟩) | ⟨i, v, hv, rfl⟩)
    · change f (Cop A b D Q j k v) = 0
      simp only [Cop, map_sub]
      rw [quot_Xop A b D hD Q j _ (Xop_low A b D hD Q hQ k v hv),
        quot_Xop A b D hD Q k _ (Xop_low A b D hD Q hQ j v hv),
        quot_Xop A b D hD Q k v hv, quot_Xop A b D hD Q j v hv]
      ring
    · change f (Hop A b D Q j v) = 0
      simp only [Hop, map_sub]
      rw [quot_iterate A b D hD Q hQ j q v hv, quot_Xop A b D hD Q j v hv]
      have he : f (X j ^ q - X j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      rw [map_sub, map_pow] at he
      rw [sub_eq_zero.mp he, sub_self]
    · let w := Lop A b D Q i v - b i • v + v
      have hw : w ∈ lowSpan q n D := (lowSpan q n D).add_mem
        ((lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i v hv)
          ((lowSpan q n D).smul_mem _ hv)) hv
      change f (Lop A b D Q i w - b i • w) = 0
      have he : f (fPoly A b i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (sample_mem A b i)
      have hL (u : MvPolynomial (Fin n) (ZMod q)) (hu : u ∈ lowSpan q n D) :
          f (Lop A b D Q i u) = f (linForm (cols A i)) * f u := quot_Lop A b D hD Q i u hu
      have hc (c : ZMod q) : f (C c) = algebraMap (ZMod q) _ c := f.commutes c
      calc
        _ = f (fPoly A b i) * f v := by
          rw [map_sub, map_smul, hL w hw]
          simp only [w, map_add, map_sub, map_smul, hL v hv, fPoly, map_mul, map_one, hc]
          have hsmul (z : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) :
              b i • z = algebraMap (ZMod q) _ (b i) * z := Algebra.smul_def (b i) z
          simp only [hsmul]
          ring
        _ = 0 := by rw [he, zero_mul]
  have h : relSpace A b D Q ≤ lowSpan q n D ⊓ LinearMap.ker f.toLinearMap := by
    apply relSpace_le A b D Q
    · exact le_inf ((relN0_le_relSpace A b D Q).trans (relSpace_low A b D hD Q hQ)) h₀
    · intro j v hv
      refine ⟨Xop_low A b D hD Q hQ j v hv.1, ?_⟩
      change f (Xop A b D Q j v) = 0
      rw [quot_Xop A b D hD Q j v hv.1]
      change f (X j) * f v = 0
      rw [show f v = 0 from hv.2, mul_zero]
  exact h.trans inf_le_right

private lemma quotient_surj (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    ∀ y : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b,
      ∃ v ∈ lowSpan q n D, Ideal.Quotient.mk (idealJ A b) v = y := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨C c, ?_, rfl⟩
    exact monomial_low D 0 c (by intro j; simp; exact (Fact.out : q.Prime).pos)
      (by simp; omega)
  | add p r hp hr =>
    obtain ⟨v, hv, he⟩ := hp
    obtain ⟨w, hw, he'⟩ := hr
    exact ⟨v + w, (lowSpan q n D).add_mem hv hw, by simp only [map_add, he, he']⟩
  | mul_X p j hp =>
    obtain ⟨v, hv, he⟩ := hp
    refine ⟨Xop A b D Q j v, Xop_low A b D hD Q hQ j v hv, ?_⟩
    rw [Xop_mod A b D hD Q j v hv, map_mul, he, map_mul, mul_comm]


private lemma Cop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j k : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Cop A b D Q j k v ∈ relSpace A b D Q := by
  rcases lt_trichotomy j k with hj | rfl | hk
  · exact relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inl ⟨j, k, hj, v, hv, rfl⟩)))
  · simp only [Cop, sub_self]; exact Submodule.zero_mem _
  · have hh : Cop A b D Q k j v ∈ relSpace A b D Q :=
      relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inl ⟨k, j, hk, v, hv, rfl⟩)))
    simpa only [Cop, neg_sub] using (relSpace A b D Q).neg_mem hh

private lemma Hop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Hop A b D Q j v ∈ relSpace A b D Q :=
  relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inr ⟨j, v, hv, rfl⟩)))

private lemma Fop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Fop A b D Q i v ∈ relSpace A b D Q :=
  relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inr ⟨i, v, hv, rfl⟩))

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
open scoped IsMulCommutative in
private lemma kernel_reverse (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D)
    (hpJ : p ∈ idealJ A b) : p ∈ relSpace A b D Q := by
  classical
  let V := lowSpan q n D
  let N : Submodule (ZMod q) V := (relSpace A b D Q).comap V.subtype
  let Xv : Fin n → Module.End (ZMod q) V := fun j => (XL A b D Q j).restrict
    (fun v hv => by rw [XL_apply]; exact Xop_low A b D hD Q hQ j v hv)
  have hXval (j : Fin n) (v : V) : (Xv j v).val = Xop A b D Q j v.val := by
    change XL A b D Q j v.val = _
    exact XL_apply A b D Q j v.val
  have hNv (j : Fin n) : N ≤ N.comap (Xv j) := by
    intro v hv
    change (Xv j v).val ∈ relSpace A b D Q
    rw [hXval]
    exact Xop_relSpace A b D Q j v.val hv
  let x : Fin n → Module.End (ZMod q) (V ⧸ N) := fun j => N.mapQ N (Xv j) (hNv j)
  have hx (j : Fin n) (v : V) : x j (N.mkQ v) = N.mkQ (Xv j v) := rfl
  have hcomm (j k : Fin n) : x j * x k = x k * x j := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [Module.End.mul_apply, hx]
    apply (Submodule.Quotient.eq N).mpr
    change (Xv j (Xv k v)).val - (Xv k (Xv j v)).val ∈ relSpace A b D Q
    simp only [hXval]
    exact Cop_relSpace A b D Q j k v.val v.property
  let B := Algebra.adjoin (ZMod q) (Set.range x)
  letI : IsMulCommutative B := Algebra.isMulCommutative_adjoin (ZMod q) (by
    rintro a ⟨j, rfl⟩ b ⟨k, rfl⟩
    exact hcomm j k)
  let y : Fin n → B := fun j => ⟨x j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  let ev : MvPolynomial (Fin n) (ZMod q) →ₐ[ZMod q] Module.End (ZMod q) (V ⧸ N) :=
    B.val.comp (aeval y)
  have hevX (j : Fin n) : ev (X j) = x j := by simp [ev, y]
  have hevC (c : ZMod q) : ev (C c) = c • (1 : Module.End (ZMod q) (V ⧸ N)) := by
    exact (ev.commutes c).trans (Algebra.algebraMap_eq_smul_one c)
  have hxpow (j : Fin n) (r : ℕ) (v : V) :
      (x j ^ r) (N.mkQ v) = N.mkQ ((Xv j ^ r) v) := by
    induction r with
    | zero => rfl
    | succ r ih => simp only [pow_succ', Module.End.mul_apply, ih, hx]
  have hpowval (j : Fin n) (r : ℕ) (v : V) :
      ((Xv j ^ r) v).val = (Xop A b D Q j)^[r] v.val := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      rw [hXval, ih]
  have hfield (j : Fin n) : ev (X j ^ q - X j) = 0 := by
    rw [map_sub, map_pow, hevX]
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [LinearMap.sub_apply, hxpow, hx, LinearMap.zero_apply]
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change (((Xv j ^ q) v).val - (Xv j v).val) ∈ relSpace A b D Q
    rw [hpowval, hXval]
    exact Hop_relSpace A b D Q j v.val v.property
  have hevL (i : Fin m) : ev (linForm (cols A i)) = ∑ j, A j i • x j := by
    simp only [linForm, cols, map_sum, map_mul, hevC, hevX, smul_mul_assoc, one_mul]
  have hLmk (i : Fin m) (v : V) :
      ev (linForm (cols A i)) (N.mkQ v) = N.mkQ
        ⟨Lop A b D Q i v.val, Lop_low A b D hD Q hQ i v.val v.property⟩ := by
    rw [hevL]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, ← map_smul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hXval]
    rfl
  have hsample (i : Fin m) : ev (fPoly A b i) = 0 := by
    unfold fPoly
    rw [map_mul, map_sub, map_add, map_sub, map_one, hevC]
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    let wv : V := ⟨Lop A b D Q i v.val - b i • v.val + v.val,
      V.add_mem (V.sub_mem (Lop_low A b D hD Q hQ i v.val v.property)
        (V.smul_mem _ v.property)) v.property⟩
    have hwv : (ev (linForm (cols A i)) - b i • 1 + 1) (N.mkQ v) = N.mkQ wv := by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, hLmk, ← map_smul, ← map_sub, ← map_add]
      rfl
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply] at hwv ⊢
    rw [hwv, hLmk, ← map_smul, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change (Lop A b D Q i wv.val - b i • wv.val) ∈ relSpace A b D Q
    exact Fop_relSpace A b D Q i v.val v.property
  have hJ : idealJ A b ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro f (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hsample i
    · exact hfield j
  have hevzero : ev p = 0 := hJ hpJ
  have hone : (1 : MvPolynomial (Fin n) (ZMod q)) ∈ V := by
    simpa [V] using
      monomial_low (q := q) D 0 (1 : ZMod q) (by intro j; simpa using (Fact.out : q.Prime).pos)
        (by simp; omega)
  let v1 : V := ⟨1, hone⟩
  have hmono (d : ℕ) : ∀ (s : Fin n →₀ ℕ) (hsd : (∑ j, s j) = d)
      (hs : ∀ j, s j < q) (hd : d < D),
      ev (monomial s 1) (N.mkQ v1) = N.mkQ
        ⟨monomial s 1, monomial_low D s 1 hs (hsd.trans_lt hd)⟩ := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s hsd hs hd
      by_cases hz : s = 0
      · subst s
        simp only [monomial_zero', map_one, Module.End.one_apply]
        rfl
      · obtain ⟨j, hj⟩ : ∃ j, 0 < s j := by
          by_contra hn
          push_neg at hn
          apply hz
          ext j
          exact Nat.eq_zero_of_le_zero (hn j)
        let t := s - Finsupp.single j 1
        have hdecomp : Finsupp.single j 1 + t = s := by
          ext k
          by_cases hk : j = k
          · subst k; simp [t]; omega
          · simp [t, Finsupp.single_apply, hk]
        have hsum : 1 + (∑ k, t k) = d := by
          rw [← hsd, ← hdecomp]
          simp [Finset.sum_add_distrib]
        have ht : ∀ k, t k < q := by
          intro k
          exact lt_of_le_of_lt (by simp only [t, Finsupp.sub_apply]; exact Nat.sub_le _ _) (hs k)
        have htd : ∑ k, t k < D := by omega
        have hi := ih (∑ k, t k) (by omega) t rfl ht htd
        have hm : (monomial s 1 : MvPolynomial (Fin n) (ZMod q)) = X j * monomial t 1 := by
          rw [← hdecomp]
          simp [X, monomial_mul]
        conv_lhs => rw [hm, map_mul, hevX, Module.End.mul_apply, hi, hx]
        congr 1
        apply Subtype.ext
        rw [hXval]
        change Xop A b D Q j (monomial t 1) = monomial s 1
        rw [Xop_fixed A b D Q j (monomial t 1) (by
          rw [← hm]; exact monomial_low D s 1 hs (by omega)), ← hm]
  have hrep : ∀ (r : MvPolynomial (Fin n) (ZMod q)) (hr : r ∈ V),
      ev r (N.mkQ v1) = N.mkQ ⟨r, hr⟩ := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨s, hs, hd, rfl⟩ := hr
      exact hmono (∑ j, s j) s rfl hs hd
    | zero =>
      change ev 0 (N.mkQ v1) = N.mkQ (0 : V)
      rw [map_zero, LinearMap.zero_apply, map_zero]
    | add r s hr hs ihr ihs =>
      calc
        _ = ev r (N.mkQ v1) + ev s (N.mkQ v1) := by rw [map_add, LinearMap.add_apply]
        _ = N.mkQ ⟨r, hr⟩ + N.mkQ ⟨s, hs⟩ := congrArg₂ (· + ·) ihr ihs
        _ = N.mkQ (⟨r, hr⟩ + ⟨s, hs⟩) := (N.mkQ.map_add _ _).symm
    | smul c r hr ihr =>
      calc
        _ = c • ev r (N.mkQ v1) := by rw [map_smul, LinearMap.smul_apply]
        _ = c • N.mkQ ⟨r, hr⟩ := congrArg (c • ·) ihr
        _ = N.mkQ (c • ⟨r, hr⟩) := (N.mkQ.map_smul c _).symm
  have hz : N.mkQ ⟨p, hp⟩ = 0 := by
    rw [← hrep p hp, hevzero]
    rfl
  exact (Submodule.Quotient.mk_eq_zero N).mp hz

end
end Prop49Proof


theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    (∀ y : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b,
      ∃ v ∈ lowSpan q n D, Ideal.Quotient.mk (idealJ A b) v = y) ∧
    ∀ v : MvPolynomial (Fin n) (ZMod q), v ∈ relSpace A b D Q ↔
      (v ∈ lowSpan q n D ∧ Ideal.Quotient.mk (idealJ A b) v = 0) := by
  refine ⟨Prop49Proof.quotient_surj A b D hD Q hQ, ?_⟩
  intro v
  constructor
  · intro hv
    exact ⟨Prop49Proof.relSpace_low A b D hD Q hQ hv,
      Prop49Proof.relSpace_mod A b D hD Q hQ hv⟩
  · rintro ⟨hv, hzero⟩
    exact Prop49Proof.kernel_reverse A b D hD Q hQ v hv
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
