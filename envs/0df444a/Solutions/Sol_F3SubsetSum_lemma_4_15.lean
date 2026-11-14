-- Prove2me | solution 1 for F3SubsetSum.lemma_4_15
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T23:44:10.915196+00:00
-- url     : https://prove2.me/submissions/1bce3141-0fff-4978-b9c3-8aa9f6065e7f

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_F3SubsetSum_SampleImage
import Definitions.Def_F3SubsetSum_SymbolicRank
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


private theorem mult_bound (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n : ℕ)
    (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ≠ 0) :
    (∑ a : Fin n → ZMod q, (rootMult a p : ℝ)) / (q : ℝ) ^ n ≤ (p.totalDegree : ℝ) / q := by
  have h := MultSZ.finite_sum_bound n p hp
  rw [ZMod.card] at h
  have hr : (∑ a : Fin n → ZMod q, (rootMult a p : ℝ)) * (q : ℝ) ≤
      (p.totalDegree : ℝ) * (q : ℝ) ^ n := by
    exact_mod_cast h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  exact (div_le_div_iff₀ (pow_pos hqpos n) hqpos).mpr hr

private theorem increment_rank (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D) {t : ℕ}
    (a : Fin t → Fin n → ZMod q) (a' : Fin n → ZMod q) :
    (sampleImage q (Fin.snoc a a') D).dualAnnihilator =
        (LinearMap.ker ((contraction (ZMod q) n q D a').domRestrict
            (sampleImage q a D).dualAnnihilator)).map
          (sampleImage q a D).dualAnnihilator.subtype ∧
      increment q a a' D =
        Module.finrank (ZMod q) (LinearMap.range ((contraction (ZMod q) n q D a').domRestrict
          (sampleImage q a D).dualAnnihilator)) := by
  classical
  -- The linear algebra works independently of the two numerical lower bounds.
  clear hq hD
  let M := mulMap (ZMod q) n q (linForm a' ^ 2) (D - 2) D
  let V := sampleImage q a D
  let V' := sampleImage q (Fin.snoc a a') D
  let C := contraction (ZMod q) n q D a'
  let T := C.domRestrict V.dualAnnihilator

  -- Split the defining sum for Φ at the newly appended sample.
  have splitPhi (Q : Fin (t + 1) → Rd (ZMod q) n q (D - 2)) :
      Phi (ZMod q) q (Fin.snoc a a') D Q =
        Phi (ZMod q) q a D (fun i => Q i.castSucc) + M (Q (Fin.last t)) := by
    simp only [Phi, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, M]
  have imageStep : V' = V ⊔ LinearMap.range M := by
    apply le_antisymm
    · rintro _ ⟨Q, rfl⟩
      rw [splitPhi]
      exact Submodule.mem_sup.mpr
        ⟨_, ⟨fun i => Q i.castSucc, rfl⟩, _, ⟨Q (Fin.last t), rfl⟩, rfl⟩
    · intro x hx
      obtain ⟨_, ⟨Q, rfl⟩, _, ⟨R, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
      refine ⟨Fin.snoc Q R, ?_⟩
      rw [splitPhi]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

  have kernelStep : V'.dualAnnihilator =
      (LinearMap.ker T).map V.dualAnnihilator.subtype := by
    calc
      V'.dualAnnihilator = V.dualAnnihilator ⊓ (LinearMap.range M).dualAnnihilator := by
        rw [imageStep, Submodule.dualAnnihilator_sup_eq]
      _ = V.dualAnnihilator ⊓ LinearMap.ker C := by
        change _ = V.dualAnnihilator ⊓ LinearMap.ker M.dualMap
        rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
      _ = (LinearMap.ker T).map V.dualAnnihilator.subtype := by
        dsimp only [T]
        rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

  refine ⟨kernelStep, ?_⟩
  change (Module.finrank (ZMod q) (Rd (ZMod q) n q D) - Module.finrank (ZMod q) V) -
    (Module.finrank (ZMod q) (Rd (ZMod q) n q D) - Module.finrank (ZMod q) V') =
      Module.finrank (ZMod q) (LinearMap.range T)
  have oldDim := Subspace.finrank_add_finrank_dualAnnihilator_eq V
  have newDim := Subspace.finrank_add_finrank_dualAnnihilator_eq V'
  have kerDim : Module.finrank (ZMod q) V'.dualAnnihilator =
      Module.finrank (ZMod q) (LinearMap.ker T) := by
    rw [kernelStep, Submodule.finrank_map_subtype_eq]
  have rankNullity := LinearMap.finrank_range_add_finrank_ker (K := ZMod q)
    (V := ↥V.dualAnnihilator) (V₂ := Module.Dual (ZMod q) (Rd (ZMod q) n q (D - 2))) T
  omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RankProof
section
variable {K : Type*} [Field K] {n : ℕ}

private lemma mult_ge_of_mem (a : Fin n → K) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (d : ℕ) (hd : MultSZ.shift a p ∈ idealOfVars (Fin n) K ^ d) : d ≤ rootMult a p := by
  obtain ⟨s, hs, he⟩ := MultSZ.exists_rootMult a p hp
  have h := (mem_pow_idealOfVars_iff d _).mp hd s (mem_support_iff.mpr hs)
  simpa only [Finsupp.degree_eq_sum, he] using h

private lemma zero_eval_mem (p : MvPolynomial (Fin n) K) (hp : eval 0 p = 0) :
    p ∈ idealOfVars (Fin n) K ^ 1 := by
  apply (mem_pow_idealOfVars_iff' 1 p).mpr
  intro s hs
  have he : s = 0 := (Finsupp.degree_eq_zero_iff s).mp (by omega)
  subst s
  simpa only [eval_zero, constantCoeff_eq] using hp

private lemma prod_mem_pow {ι : Type*} (I : Ideal (MvPolynomial (Fin n) K))
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) K) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ I ^ d i) : ∏ i ∈ s, f i ∈ I ^ (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Ideal.mul_mem_mul (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma det_mem_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial (Fin n) K)) (d : ι → ℕ)
    (h : ∀ i j, M i j ∈ idealOfVars (Fin n) K ^ d i) :
    M.det ∈ idealOfVars (Fin n) K ^ (∑ i, d i) := by
  classical
  rw [Matrix.det_apply']
  apply Ideal.sum_mem
  intro σ _
  apply Ideal.mul_mem_left
  have hh := prod_mem_pow (idealOfVars (Fin n) K) Finset.univ
    (fun i => M (σ i) i) (fun i => d (σ i)) (fun i _ => h (σ i) i)
  simpa only [Equiv.sum_comp σ] using hh

private lemma shift_eval_zero (a : Fin n → K) (p : MvPolynomial (Fin n) K) :
    eval 0 (MultSZ.shift a p) = eval a p := by
  have h : (eval (0 : Fin n → K)).comp (MultSZ.shift a).toRingHom = eval a := by
    apply MvPolynomial.ringHom_ext <;> intros <;> simp [MultSZ.shift]
  exact congrArg (fun f : MvPolynomial (Fin n) K →+* K => f p) h

private lemma det_rank_loss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial (Fin n) K)) (hM : M.det ≠ 0) (a : Fin n → K) :
    Fintype.card ι - (M.map (eval a)).rank ≤ rootMult a M.det := by
  classical
  let A := M.map (eval a)
  obtain ⟨V, U, e, hV, hU, hnorm⟩ := A.exists_rank_normal_form
  let T : Matrix ι ι (MvPolynomial (Fin n) K) := V.map C * M.map (MultSZ.shift a) * U.map C
  have hTeval : T.map (eval 0) = V * A * U := by
    dsimp [T]
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · congr 1
      · ext i j; simp
      · ext i j; exact shift_eval_zero a (M i j)
    · ext i j; simp
  let d : ι → ℕ := fun i => Sum.elim (fun _ => 0) (fun _ => 1) (e i)
  have hd : ∑ i, d i = Fintype.card ι - A.rank := by
    rw [← Equiv.sum_comp e.symm]
    simp [d, Fintype.sum_sum_type]
  have hrows : ∀ i j, T i j ∈ idealOfVars (Fin n) K ^ d i := by
    intro i j
    cases he : e i with
    | inl k => simp [d, he]
    | inr k =>
      rw [show d i = 1 by simp [d, he]]
      apply zero_eval_mem
      have hh := congrArg (fun B : Matrix ι ι K => B i j) (hTeval.trans hnorm)
      cases he' : e j <;>
        simpa [Matrix.map_apply, Matrix.submatrix_apply, he, he', Matrix.fromBlocks] using hh
  have hpow : T.det ∈ idealOfVars (Fin n) K ^ (Fintype.card ι - A.rank) := by
    simpa only [hd] using det_mem_pow T d hrows
  have hdet : T.det = C (V.det * U.det) * MultSZ.shift a M.det := by
    have hv : (V.map (C : K →+* MvPolynomial (Fin n) K)).det = C V.det := (C.map_det V).symm
    have hu : (U.map (C : K →+* MvPolynomial (Fin n) K)).det = C U.det := (C.map_det U).symm
    have hs : (M.map (MultSZ.shift a)).det = MultSZ.shift a M.det := ((MultSZ.shift a).map_det M).symm
    dsimp [T]
    rw [Matrix.det_mul, Matrix.det_mul, hv, hu, hs, map_mul]
    ring
  have hc : V.det * U.det ≠ 0 :=
    mul_ne_zero ((Matrix.isUnit_iff_isUnit_det V).mp hV).ne_zero
      ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  rw [hdet] at hpow
  have hz := (idealOfVars (Fin n) K ^ (Fintype.card ι - A.rank)).mul_mem_left
    (C (V.det * U.det)⁻¹) hpow
  have hfinal : MultSZ.shift a M.det ∈ idealOfVars (Fin n) K ^ (Fintype.card ι - A.rank) := by
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hz
  exact mult_ge_of_mem a M.det hM _ hfinal


private lemma det_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial (Fin n) K)) (d : ι → ℕ)
    (h : ∀ i j, (M i j).totalDegree ≤ d i) : M.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  have hc : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) K)).totalDegree = 0 := by
    rw [← map_intCast (C : K →+* MvPolynomial (Fin n) K)]
    exact totalDegree_C _
  have ht := totalDegree_finsetProd Finset.univ (fun i => M (σ i) i)
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => h (σ i) i)
  apply (totalDegree_mul _ _).trans
  rw [hc, zero_add]
  simpa only [Equiv.sum_comp σ] using ht.trans hb


private lemma matrix_witness {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq τ]
    (M : Matrix ι τ (MvPolynomial (Fin n) K)) (hdegree : ∀ i j, (M i j).totalDegree ≤ 2) :
    ∃ B : Matrix τ τ (MvPolynomial (Fin n) K), B.det ≠ 0 ∧
      B.det.totalDegree ≤ 2 * (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank ∧
      ∀ a : Fin n → K,
        (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank ≤
          (M.map (eval a)).rank + rootMult a B.det := by
  classical
  let P := MvPolynomial (Fin n) K
  let F := FractionRing P
  let l : P →+* F := algebraMap P F
  let ρ := (M.map l).rank
  obtain ⟨s, hs, hsp, hsi⟩ := exists_linearIndependent F (Set.range (M.map l).row)
  let E : Set (τ → F) := Set.range (Pi.basisFun F τ)
  obtain ⟨b, hb, hsub, hspan, hbi⟩ := exists_linearIndepOn_id_extension
    (show LinearIndepOn F id s from hsi) (Set.subset_union_left : s ⊆ s ∪ E)
  have hbtop : Submodule.span F b = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun F τ).span_eq]
    exact Submodule.span_le.mpr (fun v hv => hspan (Or.inr hv))
  letI : Finite s := hsi.finite
  letI : Finite b := hbi.finite
  letI : Fintype s := Fintype.ofFinite s
  letI : Fintype b := Fintype.ofFinite b
  have hcs : Fintype.card s = ρ := by
    have hh := finrank_span_eq_card hsi
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hsp] at hh
    change Fintype.card s = (M.map l).rank
    rw [Matrix.rank_eq_finrank_span_row]
    exact hh.symm
  have hcb : Fintype.card b = Fintype.card τ := by
    have hh := finrank_span_eq_card hbi
    change Module.finrank F (Submodule.span F (Set.range (fun v : b => v.val))) = Fintype.card b at hh
    rw [show Set.range (fun v : b => v.val) = b by ext v; simp, hbtop] at hh
    simpa using hh.symm
  let e : b ≃ τ := Fintype.equivOfCardEq hcb
  have hchoose (v : b) : ∃ r : τ → P, (∀ j, l (r j) = v.val j) ∧
      ((v.val ∈ s ∧ ∃ i, r = M i) ∨ (v.val ∉ s ∧ ∃ j, r = Pi.single j 1)) := by
    by_cases hv : v.val ∈ s
    · obtain ⟨i, hi⟩ := hs hv
      exact ⟨M i, fun j => congrFun hi j, Or.inl ⟨hv, i, rfl⟩⟩
    · have hvE : v.val ∈ E := (hb v.property).resolve_left hv
      obtain ⟨j, hj⟩ := hvE
      refine ⟨Pi.single j 1, ?_, Or.inr ⟨hv, j, rfl⟩⟩
      intro k
      rw [← hj]
      simp [Pi.single_apply]
  choose R hR htype using hchoose
  let B : Matrix τ τ P := fun i j => R (e.symm i) j
  have hlift : B.map l = fun i : τ => ((e.symm i).val : τ → F) := by
    ext i j
    exact hR _ _
  have hind : LinearIndependent F (B.map l).row := by
    rw [hlift]
    exact hbi.comp e.symm e.symm.injective
  have hdetF : (B.map l).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hind)).ne_zero
  have hdet : B.det ≠ 0 := by
    intro hz
    apply hdetF
    have hh := l.map_det B
    rw [hz, map_zero] at hh
    exact hh.symm
  let good : Finset τ := Finset.univ.filter (fun i => (e.symm i).val ∈ s)
  have hcg : good.card = ρ := by
    let f : {i : τ // i ∈ good} ≃ s :=
      { toFun := fun i => ⟨(e.symm i.val).val, (Finset.mem_filter.mp i.property).2⟩
        invFun := fun v => ⟨e ⟨v.val, hsub v.property⟩, by simp [good, v.property]⟩
        left_inv := by intro i; apply Subtype.ext; simp
        right_inv := by intro v; apply Subtype.ext; simp }
    rw [← hcs, ← Fintype.card_coe good]
    exact Fintype.card_congr f
  have hdeg : B.det.totalDegree ≤ 2 * ρ := by
    have hh := det_degree B (fun i => if i ∈ good then 2 else 0) (by
      intro i j
      rcases htype (e.symm i) with ⟨hi, k, hk⟩ | ⟨hi, k, hk⟩
      · simp only [B, hk]
        rw [if_pos (by simp [good, hi])]
        exact hdegree k j
      · simp only [B, hk]
        rw [if_neg (by simpa [good] using hi)]
        simp only [Pi.single_apply]
        split_ifs <;> simp [totalDegree_one, totalDegree_zero])
    simpa [hcg, mul_comm] using hh
  refine ⟨B, hdet, hdeg, ?_⟩
  intro a
  have hbound : (B.map (eval a)).rank ≤ (M.map (eval a)).rank + (Fintype.card τ - ρ) := by
    let bad : Finset τ := Finset.univ \ good
    let extra : Finset (τ → K) := bad.image (B.map (eval a)).row
    let O : Submodule K (τ → K) := Submodule.span K (Set.range (M.map (eval a)).row)
    let E' : Submodule K (τ → K) := Submodule.span K (extra : Set (τ → K))
    have hE : Module.finrank K E' ≤ bad.card :=
      (finrank_span_finset_le_card extra).trans (Finset.card_image_le)
    have hspanB : Submodule.span K (Set.range (B.map (eval a)).row) ≤ O ⊔ E' := by
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      by_cases hi : i ∈ good
      · have his : (e.symm i).val ∈ s := (Finset.mem_filter.mp hi).2
        rcases htype (e.symm i) with ⟨_, k, hk⟩ | ⟨hn, _⟩
        · apply (show O ≤ O ⊔ E' from le_sup_left)
          apply Submodule.subset_span
          refine ⟨k, ?_⟩
          ext j
          change eval a (M k j) = eval a (R (e.symm i) j)
          rw [hk]
        · exact False.elim (hn his)
      · apply (show E' ≤ O ⊔ E' from le_sup_right)
        apply Submodule.subset_span
        exact Finset.mem_image.mpr ⟨i, by simp [bad, hi], rfl⟩
    have hdim := (Submodule.finrank_mono hspanB).trans
      ((Submodule.finrank_add_le_finrank_add_finrank O E').trans (Nat.add_le_add_left hE _))
    have hbad : bad.card = Fintype.card τ - ρ := by
      dsimp only [bad]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcg]
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank K (Submodule.span K (Set.range (B.map (eval a)).row)) ≤ _
    rw [Matrix.rank_eq_finrank_span_row, ← hbad]
    exact hdim
  have hdrop := det_rank_loss B hdet a
  have hrank := (B.map (eval a)).rank_le_card_height
  have hρ := (M.map l).rank_le_card_height
  have hρ' := (M.map l).rank_le_card_width
  change ρ ≤ _
  omega


private lemma matrix_mean (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n : ℕ)
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq τ]
    (M : Matrix ι τ (MvPolynomial (Fin n) (ZMod q)))
    (hdegree : ∀ i j, (M i j).totalDegree ≤ 2) :
    ((M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) (ZMod q))))).rank : ℝ) / 3 ≤
      (∑ a : Fin n → ZMod q, ((M.map (eval a)).rank : ℝ)) / (q : ℝ)^n := by
  classical
  obtain ⟨B, hB, hdeg, hdrop⟩ := matrix_witness M hdegree
  let ρ := (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) (ZMod q))))).rank
  have hbound : (ρ : ℝ) ≤
      (∑ a : Fin n → ZMod q, ((M.map (eval a)).rank : ℝ)) / (q : ℝ)^n +
      (∑ a : Fin n → ZMod q, (rootMult a B.det : ℝ)) / (q : ℝ)^n := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n → ZMod q))) => hdrop a)
    have hr : (ρ : ℝ) * (q : ℝ)^n ≤
        (∑ a : Fin n → ZMod q, ((M.map (eval a)).rank : ℝ)) +
        (∑ a : Fin n → ZMod q, (rootMult a B.det : ℝ)) := by
      have he : Fintype.card (Fin n → ZMod q) = q^n := by simp
      simp only [Finset.sum_const, Finset.card_univ, he, smul_eq_mul, Finset.sum_add_distrib] at h
      have h' : ρ * q^n ≤ (∑ a : Fin n → ZMod q, (M.map (eval a)).rank) +
          (∑ a : Fin n → ZMod q, rootMult a B.det) := by simpa only [mul_comm] using h
      exact_mod_cast h'
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    rw [← add_div]
    exact (le_div_iff₀ (pow_pos hqpos n)).mpr hr
  have hm := mult_bound q hq n B.det hB
  have hd : (B.det.totalDegree : ℝ) / (q : ℝ) ≤ 2 * (ρ : ℝ) / 3 := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    calc
      _ ≤ 2 * (ρ : ℝ) / (q : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hdeg) hqpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast hq)
  have hh := hm.trans hd
  change (ρ : ℝ) / 3 ≤ _
  linarith


private noncomputable def dualCoords (J : Type*) [Fintype J] [DecidableEq J] :
    Module.Dual K (J → K) →ₗ[K] (J → K) where
  toFun ℓ j := ℓ (Pi.single j 1)
  map_add' := by intro ℓ η; rfl
  map_smul' := by intro c ℓ; rfl

private lemma dualCoords_injective (J : Type*) [Fintype J] [DecidableEq J] :
    Function.Injective (dualCoords (K := K) J) := by
  classical
  intro ℓ η h
  apply (Pi.basisFun K J).ext
  intro j
  have hh := congrFun h j
  change ℓ (Pi.single j 1) = η (Pi.single j 1) at hh
  simpa only [Pi.basisFun_apply] using hh

private lemma coords_rank {J W : Type*} [Fintype J] [DecidableEq J]
    [AddCommMonoid W] [Module K W] [Fintype W]
    (T : W →ₗ[K] Module.Dual K (J → K)) :
    (Matrix.of (fun v : W => fun j : J => T v (Pi.single j 1))).rank =
      Module.finrank K (LinearMap.range T) := by
  let E := dualCoords (K := K) J
  let S := E.comp T
  have hspan : Submodule.span K (Set.range (fun v : W => fun j : J => T v (Pi.single j 1))) =
      LinearMap.range S := by
    change Submodule.span K (LinearMap.range S : Set (J → K)) = _
    exact Submodule.span_eq _
  calc
    _ = Module.finrank K (Submodule.span K (Set.range (fun v : W => fun j : J => T v (Pi.single j 1)))) :=
      Matrix.rank_eq_finrank_span_row (Matrix.of (fun v : W => fun j : J => T v (Pi.single j 1)))
    _ = Module.finrank K (LinearMap.range S) :=
      congrArg (fun U : Submodule K (J → K) => Module.finrank K U) hspan
    _ = Module.finrank K (LinearMap.range T) := by
      change Module.finrank K (LinearMap.range (E.comp T)) = _
      rw [LinearMap.range_comp]
      exact (Submodule.equivMapOfInjective E (dualCoords_injective J) (LinearMap.range T)).finrank_eq.symm

private lemma generic_degree (q n D : ℕ) (ℓ : Module.Dual K (Rd K n q D))
    (β : ReducedMono n q (D-2)) : (genericEntry K n q D ℓ β).totalDegree ≤ 2 := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_mul _ _).trans
  simp

private lemma eval_generic (q n D : ℕ) (a : Fin n → K)
    (ℓ : Module.Dual K (Rd K n q D)) (β : ReducedMono n q (D-2)) :
    eval a (genericEntry K n q D ℓ β) = contraction K n q D a ℓ (Pi.single β 1) := by
  classical
  let w := Rd.toPoly K n q (D-2) (Pi.single β 1)
  let G : MvPolynomial (Fin n) K →ₗ[K] K :=
    ℓ.comp ((Rd.ofPoly K n q D).comp (LinearMap.mulRight K w))
  have hlin : linForm a ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (a i * a j) • (X i * X j) := by
    unfold linForm
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Algebra.smul_def, algebraMap_eq]
    rw [map_mul]
    ring
  have hG : contraction K n q D a ℓ (Pi.single β 1) = G (linForm a ^ 2) := rfl
  rw [hG, hlin]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold genericEntry
  simp only [map_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _ = (a i * a j) * ℓ (mulMap K n q (X i * X j) (D-2) D (Pi.single β 1))
  ring

end
end RankProof


theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D) {t : ℕ}
    (a : Fin t → Fin n → ZMod q) :
    (symbolicRank (ZMod q) n q D (sampleImage q a D).dualAnnihilator : ℝ) / 3 ≤
      (∑ a' : Fin n → ZMod q, (increment q a a' D : ℝ)) / (q : ℝ)^n := by
  classical
  let W := (sampleImage q a D).dualAnnihilator
  let emb : W → (Rd (ZMod q) n q D → ZMod q) := fun ℓ => ℓ.val
  have hemb : Function.Injective emb := by
    intro ℓ η h
    apply Subtype.ext
    exact DFunLike.coe_injective h
  letI : Finite W := Finite.of_injective emb hemb
  letI : Fintype W := Fintype.ofFinite W
  let M : Matrix W (ReducedMono n q (D-2)) (MvPolynomial (Fin n) (ZMod q)) :=
    fun ℓ β => genericEntry (ZMod q) n q D ℓ.val β
  have h := RankProof.matrix_mean q hq n M (fun ℓ β => RankProof.generic_degree q n D ℓ.val β)
  have hrho : (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) (ZMod q))))).rank =
      symbolicRank (ZMod q) n q D W := by
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hspecial (a' : Fin n → ZMod q) : (M.map (eval a')).rank = increment q a a' D := by
    let T := (contraction (ZMod q) n q D a').domRestrict W
    have he : M.map (eval a') =
        Matrix.of (fun ℓ : W => fun β : ReducedMono n q (D-2) => T ℓ (Pi.single β 1)) := by
      ext ℓ β
      exact RankProof.eval_generic q n D a' ℓ.val β
    rw [he]
    exact (RankProof.coords_rank (K := ZMod q) (J := ReducedMono n q (D-2)) (W := W) T).trans
      (increment_rank q hq n D hD a a').2.symm
  simpa only [hrho, hspecial] using h
