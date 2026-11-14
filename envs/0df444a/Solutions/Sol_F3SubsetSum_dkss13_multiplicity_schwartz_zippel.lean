-- Prove2me | solution 1 for F3SubsetSum.dkss13_multiplicity_schwartz_zippel
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T23:25:59.025637+00:00
-- url     : https://prove2.me/submissions/15859321-daf6-4abc-941f-9a6d426a4cb2

import Definitions.Def_F3SubsetSum_RootMultiplicity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open F3SubsetSum MvPolynomial
open scoped BigOperators

namespace MultSZ
section
variable {K : Type*} [CommRing K] {n : ℕ}

private noncomputable def shift (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun j => X j + C (a j)

private lemma shift_add (a b : Fin n → K) (p : MvPolynomial (Fin n) K) :
    shift a (shift b p) = shift (a + b) p := by
  have h : (shift a).comp (shift b) = shift (a + b) := by
    ext j
    simp [shift, add_assoc]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

private lemma shift_zero (p : MvPolynomial (Fin n) K) : shift 0 p = p := by
  have h : shift (0 : Fin n → K) = AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp [shift]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

private lemma shift_ne_zero (a : Fin n → K) {p : MvPolynomial (Fin n) K} (hp : p ≠ 0) :
    shift a p ≠ 0 := by
  intro h
  have hh := congrArg (shift (-a)) h
  rw [shift_add, neg_add_cancel, shift_zero, map_zero] at hh
  exact hp hh

private lemma rootMult_le (a : Fin n → K) (p : MvPolynomial (Fin n) K)
    (s : Fin n →₀ ℕ) (hs : coeff s (shift a p) ≠ 0) : rootMult a p ≤ ∑ j, s j := by
  apply Nat.sInf_le
  exact ⟨s, mem_support_iff.mpr hs, rfl⟩

private lemma exists_rootMult (a : Fin n → K) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∃ s : Fin n →₀ ℕ, coeff s (shift a p) ≠ 0 ∧ (∑ j, s j) = rootMult a p := by
  have hs : (shift a p).support.Nonempty := by
    change (MvPolynomial.support (shift a p)).Nonempty
    exact MvPolynomial.support_nonempty.mpr (shift_ne_zero a hp)
  have hn : (((fun s : Fin n →₀ ℕ => ∑ j, s j) '' ↑(shift a p).support) : Set ℕ).Nonempty := by
    obtain ⟨s, hs⟩ := hs
    exact ⟨_, s, hs, rfl⟩
  obtain ⟨s, hs, he⟩ := Nat.sInf_mem hn
  exact ⟨s, mem_support_iff.mp hs, he⟩

private noncomputable def splitR (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) (Polynomial K) :=
  (renameEquiv K (_root_.finSuccEquiv n)).trans (optionEquivRight K (Fin n))

private lemma splitR_C (c : K) : splitR n (C c) = C (Polynomial.C c) := by
  simp [splitR, optionEquivRight_C]

private lemma splitR_X_zero : splitR n (X 0 : MvPolynomial (Fin (n+1)) K) = C Polynomial.X := by
  simp [splitR, optionEquivRight_X_none]

private lemma splitR_X_succ (j : Fin n) : splitR n (X j.succ : MvPolynomial (Fin (n+1)) K) = X j := by
  simp [splitR, optionEquivRight_X_some]

private lemma splitR_apply (p : MvPolynomial (Fin (n+1)) K) :
    splitR n p = aeval (Fin.cases (C Polynomial.X) (fun j => X j)) p := by
  have h : (splitR (K := K) n).toAlgHom =
      aeval (Fin.cases (C Polynomial.X) (fun j => X j)) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [splitR_X_zero]
    · simp [splitR_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) (Polynomial K) => f p) h

private lemma splitR_monomial (t : Fin (n+1) →₀ ℕ) (c : K) :
    splitR n (monomial t c) = monomial t.tail (Polynomial.monomial (t 0) c) := by
  classical
  rw [splitR_apply, aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [monomial_eq, Finsupp.prod_pow]
  simp only [Finsupp.tail_apply]
  rw [← map_pow]
  rw [show algebraMap K (MvPolynomial (Fin n) (Polynomial K)) c = C (Polynomial.C c) from rfl,
    ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

private lemma splitR_coeff (s : Fin n →₀ ℕ) (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (splitR n p)).coeff k = coeff (s.cons k) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hr]
  | monomial t c =>
    rw [splitR_monomial, coeff_monomial]
    by_cases ht : t.tail = s
    · rw [if_pos ht, Polynomial.coeff_monomial, coeff_monomial]
      have he : t = s.cons k ↔ t 0 = k := by
        constructor
        · intro he; simpa using congrArg (fun z => z 0) he
        · intro hk
          rw [← Finsupp.cons_tail t, ht, hk]
      simp [he]
    · rw [if_neg ht, Polynomial.coeff_zero, coeff_monomial]
      have he : t ≠ s.cons k := by intro h; apply ht; rw [h]; simp
      simp [he]


private lemma splitR_shift (a : Fin n → K) (b : K)
    (p : MvPolynomial (Fin (n+1)) K) :
    splitR n (shift (Fin.cons b a) p) =
      MvPolynomial.map (Polynomial.compRingHom (Polynomial.X + Polynomial.C b))
        (shift (fun j => Polynomial.C (a j)) (splitR n p)) := by
  let f := Polynomial.compRingHom (Polynomial.X + Polynomial.C b)
  have h : (splitR (K := K) n).toRingHom.comp (shift (Fin.cons b a)).toRingHom =
      (MvPolynomial.map f).comp
        ((shift (fun j => Polynomial.C (a j))).toRingHom.comp (splitR (K := K) n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, splitR_C, f, Polynomial.coe_compRingHom]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, splitR_X_zero, splitR_C, f, Polynomial.coe_compRingHom]
      · simp [shift, splitR_X_succ, splitR_C, f, Polynomial.coe_compRingHom]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* MvPolynomial (Fin n) (Polynomial K) => h p) h

private lemma splitL_shift (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K) :
    finSuccEquiv K n (shift (Fin.cons 0 a) p) =
      Polynomial.map (shift a).toRingHom (finSuccEquiv K n p) := by
  have h : (finSuccEquiv K n).toRingHom.comp (shift (Fin.cons 0 a)).toRingHom =
      (Polynomial.mapRingHom (shift a).toRingHom).comp (finSuccEquiv K n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, finSuccEquiv_X_zero, finSuccEquiv_apply]
      · simp [shift, finSuccEquiv_X_succ, finSuccEquiv_apply]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* Polynomial (MvPolynomial (Fin n) K) => h p) h

private lemma slice_coeff (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).coeff k =
      coeff s (shift a ((finSuccEquiv K n p).coeff k)) := by
  have hr := splitR_shift a 0 p
  have hid : Polynomial.compRingHom (Polynomial.X : Polynomial K) = RingHom.id _ :=
    RingHom.ext fun _ => Polynomial.comp_X
  simp only [Polynomial.C_0, add_zero, hid, MvPolynomial.map_id] at hr
  rw [← hr, splitR_coeff, ← finSuccEquiv_coeff_coeff s (shift (Fin.cons 0 a) p) k,
    splitL_shift, Polynomial.coeff_map]
  rfl

private lemma slice_shift_coeff (a : Fin n → K) (b : K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    coeff (s.cons k) (shift (Fin.cons b a) p) =
      ((coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).comp
        (Polynomial.X + Polynomial.C b)).coeff k := by
  rw [← splitR_coeff, splitR_shift, coeff_map]
  rfl

private lemma univariate_sum [IsDomain K] [Fintype K] (p : Polynomial K) :
    ∑ a : K, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  calc
    _ = ∑ a : K, p.roots.count a := by simp only [Polynomial.count_roots]
    _ = p.roots.card := Multiset.sum_count_eq_card (by intros; exact Finset.mem_univ _)
    _ ≤ p.natDegree := Polynomial.card_roots' p



private lemma slice_degree (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).natDegree ≤
      (finSuccEquiv K n p).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [slice_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero, coeff_zero]

private lemma slice_root_bound [IsDomain K] (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K)
    (s : Fin n →₀ ℕ)
    (hs : coeff s (shift a (finSuccEquiv K n p).leadingCoeff) ≠ 0)
    (hm : (∑ j, s j) = rootMult a (finSuccEquiv K n p).leadingCoeff) (b : K) :
    rootMult (Fin.cons b a) p ≤ rootMult a (finSuccEquiv K n p).leadingCoeff +
      (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).rootMultiplicity b := by
  let r := coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))
  have hr : r ≠ 0 := by
    intro he
    have hz := congrArg (fun t : Polynomial K => t.coeff (finSuccEquiv K n p).natDegree) he
    rw [Polynomial.coeff_zero] at hz
    exact hs (by simpa only [r, slice_coeff, Polynomial.leadingCoeff] using hz)
  have hcoef : (r.comp (Polynomial.X + Polynomial.C b)).coeff (r.rootMultiplicity b) ≠ 0 := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Polynomial.comp_X_add_C_ne_zero_iff.mpr hr)
  have hb := rootMult_le (Fin.cons b a) p (s.cons (r.rootMultiplicity b)) (by
    rw [slice_shift_coeff]; exact hcoef)
  have hd : (∑ j, s.cons (r.rootMultiplicity b) j) = r.rootMultiplicity b + ∑ j, s j := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hd, hm] at hb
  exact hb.trans_eq (add_comm _ _)

private lemma sum_slices [IsDomain K] [Fintype K]
    (p : MvPolynomial (Fin (n+1)) K) (hp : p ≠ 0) (a : Fin n → K) :
    ∑ b : K, rootMult (Fin.cons b a) p ≤
      Fintype.card K * rootMult a (finSuccEquiv K n p).leadingCoeff + (finSuccEquiv K n p).natDegree := by
  have hP : finSuccEquiv K n p ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
  have hg : (finSuccEquiv K n p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  obtain ⟨s, hs, hm⟩ := exists_rootMult a _ hg
  have h := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset K)) =>
    slice_root_bound a p s hs hm b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h.trans (Nat.add_le_add_left ((univariate_sum _).trans (slice_degree a s p)) _)

private lemma finite_sum_bound [IsDomain K] [Fintype K] (n : ℕ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    (∑ a : Fin n → K, rootMult a p) * Fintype.card K ≤ p.totalDegree * (Fintype.card K) ^ n := by
  classical
  induction n with
  | zero =>
    have hm (a : Fin 0 → K) : rootMult a p = 0 := by
      obtain ⟨s, _, hs⟩ := exists_rootMult a p hp
      simpa using hs.symm
    simp only [hm, Finset.sum_const_zero, zero_mul]
    exact Nat.zero_le _
  | succ n ih =>
    let P := finSuccEquiv K n p
    have hP : P ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
    let g := P.leadingCoeff
    have hg : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hdeg : g.totalDegree + P.natDegree ≤ p.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le p P.natDegree hg
    have hrec := ih g hg
    have hs : ∑ a : Fin (n+1) → K, rootMult a p =
        ∑ a : Fin n → K, ∑ b : K, rootMult (Fin.cons b a) p := by
      have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => K))
        (fun z => rootMult (Fin.cons z.1 z.2) p) (fun a => rootMult a p) (fun _ => rfl)
      rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
    have hsum : ∑ a : Fin (n+1) → K, rootMult a p ≤
        Fintype.card K * (∑ a : Fin n → K, rootMult a g) + P.natDegree * (Fintype.card K) ^ n := by
      rw [hs]
      have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n → K))) => sum_slices p hp a)
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm] using h
    have hscaled := Nat.mul_le_mul_right (Fintype.card K) hsum
    have hi := Nat.mul_le_mul_left (Fintype.card K) hrec
    have hd := Nat.mul_le_mul_right ((Fintype.card K) ^ (n+1)) hdeg
    rw [pow_succ] at hd ⊢
    nlinarith

end
end MultSZ


theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n : ℕ)
    (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ≠ 0) :
    (∑ a : Fin n → ZMod q, (rootMult a p : ℝ)) / (q : ℝ) ^ n ≤ (p.totalDegree : ℝ) / q := by
  have h := MultSZ.finite_sum_bound n p hp
  rw [ZMod.card] at h
  have hr : (∑ a : Fin n → ZMod q, (rootMult a p : ℝ)) * (q : ℝ) ≤
      (p.totalDegree : ℝ) * (q : ℝ) ^ n := by
    exact_mod_cast h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  exact (div_le_div_iff₀ (pow_pos hqpos n) hqpos).mpr hr
