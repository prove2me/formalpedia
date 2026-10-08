-- Prove2me | solution 1 for Dvir.kakeya_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T13:23:41.056741+00:00
-- url     : https://prove2.me/submissions/fcd1e553-811e-45c7-8ba3-84e630918670

import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Dvir's finite-field Kakeya theorem (basic bound)

If `K ⊆ F^n` (F a finite field of cardinality `q`) contains a line in every
direction, then `|K| ≥ (q + n - 1 choose n)`.

Proof (Dvir 2008): if `|K|` is smaller than the number `C(q-1+n, n)` of monomials
of total degree `≤ q-1` in `n` variables, linear algebra produces a nonzero
polynomial `P` of total degree `≤ q-1` vanishing on `K`.  Restricting `P` to a line
of direction `b` gives a univariate polynomial of degree `≤ q-1 < q` with `q` roots,
hence the zero polynomial; its top coefficient is the value of the top homogeneous
part `H` of `P` at `b`.  Since `H` has per-variable degrees `< q`, `funext` forces
`H = 0` once it vanishes everywhere, contradicting `P ≠ 0`.
-/

namespace Dvir

open Finset Finsupp MvPolynomial Polynomial

/-! ### Stage 0: small helpers -/

theorem funsum_eq (n : ℕ) (d : Fin n →₀ ℕ) : ∑ j, d j = d.sum (fun _ e => e) := by
  classical
  rw [Finsupp.sum]
  exact (Finset.sum_subset (Finset.subset_univ d.support) (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.1 hj])).symm

/-- Hockey stick, in the descending form used below. -/
theorem hockey (n m : ℕ) : ∑ k ∈ Finset.range (m + 1), Nat.choose (m - k + n) n
    = Nat.choose (m + n + 1) (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have hreind : ∑ k ∈ Finset.range (m + 1), Nat.choose (m + 1 - (k + 1) + n) n
        = ∑ k ∈ Finset.range (m + 1), Nat.choose (m - k + n) n :=
      Finset.sum_congr rfl fun k _ => by congr 1; omega
    rw [hreind, ih]
    have h0 : m + 1 - 0 + n = m + 1 + n := by omega
    rw [h0]
    have h := Nat.choose_succ_succ' (m + n + 1) n
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at h ⊢
    exact h.symm

/-! ### Stage 1: counting monomials of bounded total degree -/

/-- Functions `Fin n → ℕ` with coordinate sum `≤ m`. -/
def funLe : (n m : ℕ) → Finset (Fin n → ℕ)
  | 0, _ => Finset.univ
  | n + 1, m => Finset.biUnion (Finset.range (m + 1)) fun k =>
      (funLe n (m - k)).image (fun f => (Fin.cons k f : Fin (n + 1) → ℕ))

theorem mem_funLe : ∀ (n m : ℕ) (f : Fin n → ℕ), f ∈ funLe n m ↔ ∑ j, f j ≤ m := by
  intro n
  induction n with
  | zero =>
    intro m f
    constructor
    · intro _; simp
    · intro _; exact Finset.mem_univ _
  | succ n ih =>
    intro m f
    constructor
    · intro hf
      simp only [funLe, Finset.mem_biUnion, Finset.mem_image] at hf
      obtain ⟨k, hkkm, f', hf'mem, rfl⟩ := hf
      have hsum : ∑ j : Fin (n + 1), Fin.cons k f' j = k + ∑ j, f' j := by
        rw [Fin.sum_univ_succ]
        simp
      have h2 := (ih (m - k) f').1 hf'mem
      have hkm : k ≤ m := by simpa [Finset.mem_range] using hkkm
      simp only [hsum]
      omega
    · intro hsum
      have hle : f 0 ≤ ∑ j, f j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hk : f 0 ∈ Finset.range (m + 1) := by
        simp only [Finset.mem_range]
        omega
      refine Finset.mem_biUnion.mpr ⟨f 0, hk, ?_⟩
      have hsplit : ∑ j : Fin (n + 1), f j = f 0 + ∑ j : Fin n, f (Fin.succ j) := by
        rw [Fin.sum_univ_succ]
      have hsub : ∑ j : Fin n, f (Fin.succ j) ≤ m - f 0 := by omega
      refine Finset.mem_image.mpr ⟨fun j => f (Fin.succ j), (ih (m - f 0) _).2 hsub, ?_⟩
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp
      · simp

theorem card_funLe (n m : ℕ) : (funLe n m).card = Nat.choose (m + n) n := by
  induction n generalizing m with
  | zero => simp [funLe]
  | succ n ih =>
    have hconsinj : ∀ k : ℕ,
        Function.Injective (fun f : Fin n → ℕ => (Fin.cons k f : Fin (n + 1) → ℕ)) := by
      intro k f₁ f₂ h
      have h' : (Fin.cons k f₁ : Fin (n + 1) → ℕ) = (Fin.cons k f₂ : Fin (n + 1) → ℕ) := h
      funext j
      have e1 : (Fin.cons k f₁ : Fin (n + 1) → ℕ) (Fin.succ j) = f₁ j := by simp
      have e2 : (Fin.cons k f₂ : Fin (n + 1) → ℕ) (Fin.succ j) = f₂ j := by simp
      have hc := congrFun h' (Fin.succ j)
      rw [e1, e2] at hc
      exact hc
    have hdisj : (Finset.range (m + 1) : Set ℕ).PairwiseDisjoint fun k =>
        (funLe n (m - k)).image (fun f => (Fin.cons k f : Fin (n + 1) → ℕ)) := by
      intro k _ l _ hkl
      refine Finset.disjoint_right.mpr fun g hg => ?_
      obtain ⟨f₂, _, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_image]
      intro hmem
      obtain ⟨f₁, _, hfg⟩ := hmem
      exact hkl (by
        have h0 := congrFun hfg 0
        simpa using h0)
    rw [funLe, Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun k _ =>
      card_image_of_injective _ (hconsinj k)), Finset.sum_congr rfl (fun k _ => by rw [ih])]
    exact hockey n m

/-- Monomials of total degree `≤ m` in `n` variables, as finsupps. -/
noncomputable def monoLe (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  (funLe n m).image Finsupp.equivFunOnFinite.symm

theorem card_monoLe (n m : ℕ) : (monoLe n m).card = Nat.choose (m + n) n := by
  simp only [monoLe]
  rw [Finset.card_image_of_injective _ (Equiv.injective _), card_funLe]

theorem mem_monoLe {n m : ℕ} (d : Fin n →₀ ℕ) :
    d ∈ monoLe n m ↔ d.sum (fun _ e => e) ≤ m := by
  rw [monoLe, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hpoint : ∑ j, (Finsupp.equivFunOnFinite.symm f) j = ∑ j, f j :=
      Finset.sum_congr rfl fun j _ => rfl
    rw [← funsum_eq n (Finsupp.equivFunOnFinite.symm f), hpoint]
    exact (mem_funLe n m f).1 hf
  · intro h
    refine ⟨Finsupp.equivFunOnFinite d, ?_, Finsupp.equivFunOnFinite.symm_apply_apply d⟩
    refine (mem_funLe n m _).2 ?_
    have hpoint : ∑ j, Finsupp.equivFunOnFinite d j = ∑ j, d j :=
      Finset.sum_congr rfl fun j _ => rfl
    rw [hpoint, funsum_eq n d]
    exact h


/-! ### Stage 2: the bounded-degree space, its dimension, and the vanishing polynomial -/

section Field

variable {F : Type*} [Field F] [Fintype F]

theorem monoLe_monomials_independent (n m : ℕ) :
    LinearIndependent F (fun d : {d : Fin n →₀ ℕ // d ∈ monoLe n m} =>
      MvPolynomial.monomial (d : Fin n →₀ ℕ) (1 : F)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum j
  have h1 : MvPolynomial.coeff (j : Fin n →₀ ℕ)
      (∑ d, g d • MvPolynomial.monomial (d : Fin n →₀ ℕ) (1 : F)) = 0 := by
    rw [hsum]
    rfl
  rw [MvPolynomial.coeff_sum] at h1
  rw [Finset.sum_eq_single j
    (fun b _ hb => by
      rw [← MvPolynomial.lcoeff_apply (σ := Fin n) (R := F) (m := (j : Fin n →₀ ℕ)), map_smul, MvPolynomial.lcoeff_apply,
          MvPolynomial.coeff_monomial, if_neg (fun h => hb (Subtype.ext h)), smul_zero])
    (fun hb => absurd (Finset.mem_univ j) hb)] at h1
  rw [← MvPolynomial.lcoeff_apply (σ := Fin n) (R := F) (m := (j : Fin n →₀ ℕ)), map_smul, MvPolynomial.lcoeff_apply,
      MvPolynomial.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one] at h1
  exact h1

theorem monoLe_monomial_mem (n m : ℕ) {d : Fin n →₀ ℕ} (hd : d ∈ monoLe n m) :
    MvPolynomial.monomial d (1 : F) ∈ (restrictTotalDegree (σ := Fin n) (R := F) m) := by
  rw [mem_restrictTotalDegree]
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (mem_monoLe d |>.1 hd)

theorem span_monoLe (n m : ℕ) :
    Submodule.span F (Set.range fun d : {d : Fin n →₀ ℕ // d ∈ monoLe n m} =>
      MvPolynomial.monomial (d : Fin n →₀ ℕ) (1 : F)) = (restrictTotalDegree (σ := Fin n) (R := F) m) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨d, rfl⟩
    exact monoLe_monomial_mem n m d.2
  · intro p hp
    rw [mem_restrictTotalDegree] at hp
    have hsum : p = ∑ d ∈ p.support, MvPolynomial.monomial d (coeff d p) := p.as_sum
    rw [hsum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdle : d.sum (fun _ e => e) ≤ m :=
      (MvPolynomial.le_totalDegree hd).trans hp
    have hdmono : d ∈ monoLe n m := (mem_monoLe d).2 hdle
    have : MvPolynomial.monomial d (coeff d p)
        = (coeff d p) • MvPolynomial.monomial d (1 : F) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨d, hdmono⟩, rfl⟩)

theorem card_le_finrank (n m : ℕ) :
    (monoLe n m).card ≤ Module.finrank F ↥(restrictTotalDegree (σ := Fin n) (R := F) m) := by
  have hli := monoLe_monomials_independent (F := F) n m
  have hcard := (linearIndependent_iff_card_le_finrank_span (R := F)
    (b := fun d : {d : Fin n →₀ ℕ // d ∈ monoLe n m} =>
      MvPolynomial.monomial (d : Fin n →₀ ℕ) (1 : F))).1 hli
  simp only [Set.finrank] at hcard
  rw [span_monoLe n m, Fintype.card_coe, card_monoLe] at hcard
  rw [card_monoLe]
  exact hcard

theorem exists_vanishing (n m : ℕ) (K : Set (Fin n → F)) [DecidablePred (· ∈ K)]
    [Fintype ↥K] (hcard : Fintype.card ↥K < Nat.choose (m + n) n) :
    ∃ P : MvPolynomial (Fin n) F, P ≠ 0 ∧ P ∈ (restrictTotalDegree (σ := Fin n) (R := F) m) ∧
      ∀ x ∈ K, eval x P = 0 := by
  classical
  let L : (restrictTotalDegree (σ := Fin n) (R := F) m) →ₗ[F] (↥K → F) :=
    { toFun := fun p x => MvPolynomial.eval (x : Fin n → F) (p : MvPolynomial (Fin n) F)
      map_add' := by intro p q; funext x; exact MvPolynomial.eval_add
      map_smul' := by
        intro c p
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, Submodule.coe_smul_of_tower, Algebra.smul_def,
          MvPolynomial.eval_mul, MvPolynomial.eval_C, RingHom.id_apply,
          MvPolynomial.algebraMap_eq] }
  have hLapp : ∀ (p : (restrictTotalDegree (σ := Fin n) (R := F) m)) (x : ↥K),
      L p x = MvPolynomial.eval (x : Fin n → F) (p : MvPolynomial (Fin n) F) := fun p x => rfl
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hcod : Module.finrank F (↥K → F) = Fintype.card ↥K := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank F ↥(LinearMap.range L) ≤ Module.finrank F (↥K → F) :=
    Submodule.finrank_le (LinearMap.range L)
  by_contra hcon
  push_neg at hcon
  have hker : LinearMap.ker L = ⊥ := by
    by_contra hne
    obtain ⟨P, hPker, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨x, hxK, hxe⟩ := hcon P.1 (by simpa using hP0) P.2
    have h0 : MvPolynomial.eval (x : Fin n → F) (P : MvPolynomial (Fin n) F) = 0 := by
      rw [← hLapp P ⟨x, hxK⟩]
      exact congrFun (LinearMap.mem_ker.1 hPker) ⟨x, hxK⟩
    exact hxe h0
  rw [hker] at hrank
  simp at hrank
  have hv := card_le_finrank (F := F) n m
  rw [card_monoLe] at hv
  rw [hcod] at hle
  omega


/-! ### Stage 3: restriction to a line -/

/-- The univariate polynomial `t ↦ P(a + t • b)`. -/
noncomputable def linePoly {n : ℕ} (a b : Fin n → F) (P : MvPolynomial (Fin n) F) :
    Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) P

theorem linePoly_monomial {n : ℕ} (a b : Fin n → F) (d : Fin n →₀ ℕ) (r : F) :
    linePoly a b (MvPolynomial.monomial d r)
      = Polynomial.C r * d.prod (fun j k => (Polynomial.C (a j)
          + Polynomial.X * Polynomial.C (b j)) ^ k) := by
  rw [linePoly, MvPolynomial.eval₂Hom_monomial]

theorem eval_linePoly {n : ℕ} (a b : Fin n → F) (P : MvPolynomial (Fin n) F) (t : F) :
    Polynomial.eval t (linePoly a b P)
      = MvPolynomial.eval (fun j => a j + t * b j) P := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    have hsplit : linePoly a b (p + q) = linePoly a b p + linePoly a b q := by
      conv_lhs => rw [linePoly]
      rw [map_add, ← linePoly, ← linePoly]
    rw [hsplit, Polynomial.eval_add, hp, hq, map_add]
  | monomial d r =>
    have hL : Polynomial.eval t (linePoly a b (MvPolynomial.monomial d r))
        = r * ∏ j ∈ d.support, (a j + t * b j) ^ (d j) := by
      have key : ∀ j ∈ d.support,
          Polynomial.eval t ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ d j)
            = (a j + t * b j) ^ d j := by
        intro j _
        rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        simp
      rw [linePoly_monomial, Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod,
        Polynomial.eval_prod]
      exact congrArg (HMul.hMul r) (Finset.prod_congr rfl key)
    rw [hL, MvPolynomial.eval_monomial, Finsupp.prod]

theorem natDegree_monomial_linePoly_le {n : ℕ} (a b : Fin n → F) (d : Fin n →₀ ℕ) (r : F) :
    (linePoly a b (MvPolynomial.monomial d r)).natDegree ≤ d.sum (fun _ e => e) := by
  have haff : ∀ j : Fin n,
      (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)).natDegree ≤ 1 := by
    intro j
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    have hC : (Polynomial.C (a j)).natDegree = 0 := Polynomial.natDegree_C _
    have hX : (Polynomial.C (b j) * Polynomial.X).natDegree ≤ 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      simp
    rw [hC]
    simpa using hX
  rw [linePoly_monomial]
  have h1 : (Polynomial.C r).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
  have h2 : (d.prod fun j k => (Polynomial.C (a j)
      + Polynomial.X * Polynomial.C (b j)) ^ k).natDegree ≤ d.sum (fun _ e => e) := by
    rw [Finsupp.prod]
    refine le_trans (Polynomial.natDegree_prod_le d.support
      (fun j => (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ d j)) ?_
    simp only [Finsupp.sum]
    exact Finset.sum_le_sum fun j _ =>
      le_trans Polynomial.natDegree_pow_le
        ((Nat.mul_le_mul_left (d j) (haff j)).trans_eq (Nat.mul_one _))
  refine le_trans Polynomial.natDegree_mul_le ?_
  simpa using add_le_add h1 h2

theorem natDegree_linePoly_le {n : ℕ} (a b : Fin n → F) (P : MvPolynomial (Fin n) F) :
    (linePoly a b P).natDegree ≤ P.totalDegree := by
  have hsum : linePoly a b P
      = ∑ d ∈ P.support, linePoly a b (MvPolynomial.monomial d (MvPolynomial.coeff d P)) := by
    conv_lhs => rw [P.as_sum, linePoly]
    rw [map_sum]
    rfl
  rw [hsum]
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le fun d hd => ?_)
  exact (natDegree_monomial_linePoly_le a b d _).trans (MvPolynomial.le_totalDegree hd)

theorem linePoly_eq_zero {n : ℕ} (a b : Fin n → F) (P : MvPolynomial (Fin n) F)
    (hdeg : P.totalDegree < Fintype.card F)
    (hroots : ∀ t : F, MvPolynomial.eval (fun j => a j + t * b j) P = 0) :
    linePoly a b P = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (linePoly a b P)
    Function.injective_id
    (fun t => by
      show Polynomial.eval t (linePoly a b P) = 0
      rw [eval_linePoly a b P t]
      exact hroots t)
    ((natDegree_linePoly_le a b P).trans_lt hdeg)


/-! ### Stage 4: the top coefficient along a line -/

theorem totalDegree_homogeneousComponent_le {n : ℕ} (P : MvPolynomial (Fin n) F) (k : ℕ) :
    (MvPolynomial.homogeneousComponent k P).totalDegree ≤ k := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun d hd => ?_
  have hc : MvPolynomial.coeff d (MvPolynomial.homogeneousComponent k P) ≠ 0 :=
    MvPolynomial.mem_support_iff.1 hd
  rw [MvPolynomial.coeff_homogeneousComponent] at hc
  by_cases hdk : d.degree = k
  · rw [if_pos hdk] at hc
    have hdeg : d.sum (fun _ e => e) = d.degree := rfl
    rw [hdeg, hdk]
  · rw [if_neg hdk] at hc
    exact absurd rfl hc

theorem coeff_linePoly_monomial_top {n : ℕ} (a b : Fin n → F) (d : Fin n →₀ ℕ) (c : F) :
    (linePoly a b (MvPolynomial.monomial d c)).coeff (d.sum (fun _ e => e))
      = c * ∏ j ∈ d.support, b j ^ (d j) := by
  classical
  have hndle : ∀ j : Fin n,
      (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)).natDegree ≤ 1 := by
    intro j
    have hC : (Polynomial.C (a j)).natDegree = 0 := Polynomial.natDegree_C _
    have hX : (Polynomial.C (b j) * Polynomial.X).natDegree ≤ 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X]
      simp
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    rw [hC]
    simpa using hX
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : linePoly a b (MvPolynomial.monomial d 0) = 0 := by
      rw [linePoly]
      simp
    rw [h0]
    simp
  · by_cases hb : ∀ j ∈ d.support, b j ≠ 0
    · have key1 : ∀ j ∈ d.support,
        (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)).coeff 1 = b j := by
        intro j _
        rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg one_ne_zero,
          Polynomial.coeff_X_mul, Polynomial.coeff_C]
        simp
      have hne : ∀ j ∈ d.support,
          (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ≠ 0 := by
        intro j hj h0
        have h1 := key1 j hj
        rw [h0, Polynomial.coeff_zero] at h1
        exact hb j hj h1.symm
      have hnd : ∀ j ∈ d.support,
          (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)).natDegree = 1 := by
        intro j hj
        refine le_antisymm (hndle j) ?_
        exact Polynomial.le_natDegree_of_ne_zero (by rw [key1 j hj]; exact hb j hj)
      have hlc : ∀ j ∈ d.support,
          (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)).leadingCoeff = b j := by
        intro j hj
        rw [Polynomial.leadingCoeff, hnd j hj]
        exact key1 j hj
      have hlcpow : ∀ j ∈ d.support,
          ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j)).leadingCoeff
            = b j ^ (d j) := by
        intro j hj
        rw [Polynomial.leadingCoeff_pow'
          (by rw [hlc j hj]; exact pow_ne_zero _ (hb j hj)), hlc j hj]
      have hndpow : ∀ j ∈ d.support,
          ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j)).natDegree
            = d j := by
        intro j hj
        rw [Polynomial.natDegree_pow'
          (by rw [hlc j hj]; exact pow_ne_zero _ (hb j hj)), hnd j hj]
        exact Nat.mul_one _
      have hcond : (∏ j ∈ d.support,
          ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j)).leadingCoeff)
            ≠ 0 := by
        rw [Finset.prod_congr rfl (fun j hj => hlcpow j hj)]
        exact Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hb j hj)
      rw [linePoly_monomial, Finsupp.prod]
      have hprodne : (∏ j ∈ d.support,
          ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hne j hj)
      have hndall : (Polynomial.C c * ∏ j ∈ d.support,
          ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j))).natDegree
            = ∑ j ∈ d.support, d j := by
        rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.2 hc) hprodne,
          Polynomial.natDegree_C, zero_add]
        rw [Polynomial.natDegree_prod' d.support
          (fun j => (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j)) hcond]
        exact Finset.sum_congr rfl (fun j hj => hndpow j hj)
      simp only [Finsupp.sum] at hndall ⊢
      rw [← hndall, ← Polynomial.leadingCoeff,
        Polynomial.leadingCoeff_mul (Polynomial.C c)
          (∏ j ∈ d.support, ((Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j))),
        Polynomial.leadingCoeff_C]
      rw [Polynomial.leadingCoeff_prod' d.support
        (fun j => (Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) ^ (d j)) hcond]
      exact congrArg (HMul.hMul c) (Finset.prod_congr rfl fun j hj => hlcpow j hj)
    · push_neg at hb
      obtain ⟨j, hjmem, hjb⟩ := hb
      have hdj : 0 < d j := by
        have := Finsupp.mem_support_iff.1 hjmem
        omega
      have hins : insert j (d.support.erase j) = d.support :=
        Finset.insert_erase hjmem
      have hkey : ∑ j' ∈ d.support, d j' = d j + ∑ j' ∈ d.support.erase j, d j' := by
        conv_lhs => rw [← hins]
        rw [Finset.sum_insert (Finset.notMem_erase j d.support)]
      have hper : ∀ j' ∈ d.support,
          ((Polynomial.C (a j') + Polynomial.X * Polynomial.C (b j')) ^ (d j')).natDegree
            ≤ if j' = j then 0 else d j' := by
        intro j' hj'
        by_cases hj'j : j' = j
        · subst hj'j
          rw [hjb]
          simp
        · rw [if_neg hj'j]
          exact le_trans Polynomial.natDegree_pow_le
            ((Nat.mul_le_mul_left (d j') (hndle j')).trans_eq (Nat.mul_one (d j')))
      have hsumif : ∑ j' ∈ d.support, (if j' = j then 0 else d j')
          = (∑ j' ∈ d.support, d j') - d j := by
        conv_lhs => rw [← hins]
        rw [Finset.sum_insert (Finset.notMem_erase j d.support), if_pos rfl, zero_add]
        have hcongr : ∑ j' ∈ d.support.erase j, (if j' = j then 0 else d j')
            = ∑ j' ∈ d.support.erase j, d j' :=
          Finset.sum_congr rfl fun j' hj' => if_neg fun h => (Finset.mem_erase.1 hj').1 h
        rw [hcongr, hkey]
        omega
      have hble : (Polynomial.C c * ∏ j' ∈ d.support,
          ((Polynomial.C (a j') + Polynomial.X * Polynomial.C (b j')) ^ (d j'))).natDegree
          ≤ (∑ j' ∈ d.support, d j') - d j := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h2 : (∏ j' ∈ d.support,
            ((Polynomial.C (a j') + Polynomial.X * Polynomial.C (b j')) ^ (d j'))).natDegree
            ≤ (∑ j' ∈ d.support, d j') - d j := by
          refine le_trans (Polynomial.natDegree_prod_le d.support
            (fun j' => (Polynomial.C (a j') + Polynomial.X * Polynomial.C (b j')) ^ (d j')))
            ?_
          exact (Finset.sum_le_sum hper).trans (le_of_eq hsumif)
        rw [Polynomial.natDegree_C, Nat.zero_add]
        exact h2
      have hlt : (linePoly a b (MvPolynomial.monomial d c)).natDegree
          < d.sum (fun _ e => e) := by
        rw [linePoly_monomial, Finsupp.prod]
        refine lt_of_le_of_lt hble ?_
        simp only [Finsupp.sum]
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      rw [show (∏ j ∈ d.support, b j ^ d j) = 0 from
        Finset.prod_eq_zero hjmem (by rw [hjb, zero_pow hdj.ne'])]
      ring



theorem coeff_linePoly_top {n : ℕ} (a b : Fin n → F) (P : MvPolynomial (Fin n) F) :
    (linePoly a b P).coeff P.totalDegree
      = MvPolynomial.eval b (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  have hsumc : (∑ k ∈ Finset.range (P.totalDegree + 1),
      MvPolynomial.homogeneousComponent k P) = P := P.sum_homogeneousComponent
  have hLP : linePoly a b P = ∑ k ∈ Finset.range (P.totalDegree + 1),
      linePoly a b (MvPolynomial.homogeneousComponent k P) := by
    conv_lhs => rw [← hsumc, linePoly, map_sum]
    rfl
  rw [hLP, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  rw [Finset.sum_eq_single P.totalDegree
    (fun k hk hkne => by
      have hklt : k < P.totalDegree := by
        rcases Nat.lt_or_ge k P.totalDegree with h | h
        · exact h
        · exact absurd (Nat.le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h) hkne
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      exact lt_of_le_of_lt (natDegree_linePoly_le _ _ _)
        (lt_of_le_of_lt (totalDegree_homogeneousComponent_le _ _) hklt))
    (fun hmem => absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) hmem)]
  -- the surviving term: decompose the top homogeneous component into monomials
  have hcomp := MvPolynomial.homogeneousComponent_apply P.totalDegree P
  have hLPD : linePoly a b (MvPolynomial.homogeneousComponent P.totalDegree P)
      = ∑ d ∈ P.support.filter (fun d => d.degree = P.totalDegree),
          linePoly a b (MvPolynomial.monomial d (MvPolynomial.coeff d P)) := by
    conv_lhs => rw [hcomp, linePoly, map_sum]
    rfl
  have hRHS : MvPolynomial.eval b (MvPolynomial.homogeneousComponent P.totalDegree P)
      = ∑ d ∈ P.support.filter (fun d => d.degree = P.totalDegree),
          MvPolynomial.coeff d P * ∏ j ∈ d.support, b j ^ (d j) := by
    conv_lhs => rw [hcomp, map_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [MvPolynomial.eval_monomial]
      rfl
  rw [hLPD, hRHS, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  exact Finset.sum_congr rfl fun d hd => by
    have hdeg : d.degree = P.totalDegree := (Finset.mem_filter.1 hd).2
    rw [show P.totalDegree = d.sum (fun _ e => e) from by
      rw [show d.sum (fun _ e => e) = d.degree from rfl, hdeg],
      coeff_linePoly_monomial_top]

/-! ### Stage 5: assembly -/

/-- **Dvir's finite-field Kakeya theorem** (basic bound). -/
theorem dvir_kakeya {n : ℕ} (hn : 1 ≤ n) (K : Set (Fin n → F))
    [DecidablePred (· ∈ K)] [Fintype ↥K]
    (hK : ∀ b : Fin n → F, b ≠ 0 → ∃ a : Fin n → F, ∀ t : F, (fun j => a j + t * b j) ∈ K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ Fintype.card ↥K := by
  classical
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card (α := F)
  by_contra hcon
  push_neg at hcon
  have hlt : Fintype.card ↥K < Nat.choose (Fintype.card F - 1 + n) n := by
    have := hcon
    rwa [show Nat.choose (Fintype.card F + n - 1) n
        = Nat.choose (Fintype.card F - 1 + n) n from by
      congr 1
      omega] at this
  obtain ⟨P, hP0, hPdeg, hPvan⟩ := exists_vanishing n (Fintype.card F - 1) K hlt
  have hPtd : P.totalDegree ≤ Fintype.card F - 1 :=
    (MvPolynomial.mem_restrictTotalDegree (Fin n) (Fintype.card F - 1) P).1 hPdeg
  -- the top homogeneous component is nonzero
  have hHne : MvPolynomial.homogeneousComponent P.totalDegree P ≠ 0 := by
    intro h0
    apply hP0
    rcases P.support.eq_empty_or_nonempty with hempty | hne2
    · refine (MvPolynomial.ext_iff (σ := Fin n) (R := F)).2 fun d => ?_
      have hd : d ∉ P.support := by rw [hempty]; exact Finset.notMem_empty d
      rw [MvPolynomial.notMem_support_iff.1 hd, MvPolynomial.coeff_zero]
    · obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup P.support hne2
        (fun s => s.sum fun _ e => e)
      have hD : P.totalDegree = d.sum (fun _ e => e) := hdeq
      have hc1 : MvPolynomial.coeff d P ≠ 0 := MvPolynomial.mem_support_iff.1 hd
      have hc2 : MvPolynomial.coeff d (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
        rw [MvPolynomial.coeff_homogeneousComponent,
          if_pos (by rw [show Finsupp.degree d = d.sum (fun _ e => e) from rfl, hD])]
        exact hc1
      rw [h0, MvPolynomial.coeff_zero] at hc2
      exact absurd rfl hc2
  -- its degreeOf are < q, so if it vanished everywhere it would be zero
  have hexb : ∃ b : Fin n → F, b ≠ 0 ∧
      MvPolynomial.eval b (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
    rcases eq_or_ne P.totalDegree 0 with hD0 | hDpos
    · -- degree zero: P is a nonzero constant, so it cannot vanish on the (nonempty) K
      exfalso
      obtain ⟨a, haline⟩ := hK (fun _ => 1) (fun h => one_ne_zero (congrFun h ⟨0, hn⟩))
      -- every support element is 0
      have hsupp0 : ∀ d ∈ P.support, d.sum (fun _ e => e) = 0 := fun d hd =>
        Nat.le_zero.1 ((MvPolynomial.le_totalDegree hd).trans hD0.le)
      have hd0 : ∀ d ∈ P.support, d = 0 := by
        intro d hd
        refine Finsupp.ext fun j => ?_
        rcases eq_or_ne (d j) 0 with h | hne
        · rw [h]
          rfl
        · have hjmem : j ∈ d.support := Finsupp.mem_support_iff.2 hne
          have h1 : d j ≤ ∑ i ∈ d.support, d i :=
            Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hjmem
          have h2 := hsupp0 d hd
          simp only [Finsupp.sum] at h2
          omega
      have hc0 : MvPolynomial.coeff 0 P ≠ 0 := by
        intro hcz
        apply hP0
        refine (MvPolynomial.ext_iff (σ := Fin n) (R := F)).2 fun d => ?_
        have hd : d ∉ P.support := by
          intro hmem
          rw [hd0 d hmem] at hmem
          exact (MvPolynomial.mem_support_iff.1 hmem) hcz
        rw [MvPolynomial.notMem_support_iff.1 hd, MvPolynomial.coeff_zero]
      have hPC : MvPolynomial.eval (fun j => a j + (0 : F) * 1) P
          = MvPolynomial.coeff 0 P := by
        rw [P.as_sum, Finset.sum_eq_single_of_mem (0 : Fin n →₀ ℕ)
          ((MvPolynomial.mem_support_iff.2 hc0) : 0 ∈ P.support)
          (fun d hd hdne => absurd (hd0 d hd) hdne), MvPolynomial.eval_monomial]
        simp
      rw [hPvan _ (haline 0)] at hPC
      exact absurd hPC.symm hc0
    · by_contra hall
      push_neg at hall
      apply hHne
      refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => Finset.univ) ?_ ?_
      · intro j
        have h1 := totalDegree_homogeneousComponent_le P P.totalDegree
        have h2 : MvPolynomial.degreeOf j
            (MvPolynomial.homogeneousComponent P.totalDegree P)
            ≤ P.totalDegree :=
          (MvPolynomial.degreeOf_le_totalDegree _ j).trans h1
        have h3 : P.totalDegree ≤ Fintype.card F - 1 :=
          (MvPolynomial.mem_restrictTotalDegree (Fin n) (Fintype.card F - 1) P).1 hPdeg
        rw [Finset.card_univ]
        exact lt_of_le_of_lt (h2.trans h3) (by have := hq2; omega)
      · intro x _
        rcases eq_or_ne x 0 with rfl | hx
        · rw [show MvPolynomial.eval 0
              (MvPolynomial.homogeneousComponent P.totalDegree P) = 0 from by
            have hcomp := MvPolynomial.homogeneousComponent_apply P.totalDegree P
            conv_lhs => rw [hcomp, map_sum]
            refine Finset.sum_eq_zero fun d hd => ?_
            rw [MvPolynomial.eval_monomial]
            refine mul_eq_zero.2 (Or.inr ?_)
            have hdeq : d.sum (fun _ e => e) = P.totalDegree := (Finset.mem_filter.1 hd).2
            by_cases hex : ∃ j, d j ≠ 0
            · obtain ⟨j, hj⟩ := hex
              rw [Finsupp.prod]
              refine Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hj) ?_
              rw [Pi.zero_apply, zero_pow hj]
            · push_neg at hex
              exfalso
              have hzero : d.sum (fun _ e => e) = 0 := by
                rw [Finsupp.sum]
                exact Finset.sum_eq_zero fun j _ => by rw [hex j]
              omega]
        · exact hall x hx
  obtain ⟨b, hb0, hbev⟩ := hexb
  obtain ⟨a, haline⟩ := hK b hb0
  have hLP0 := linePoly_eq_zero a b P
    (by have := hPtd; have := hq2; omega)
    (fun t => hPvan _ (haline t))
  have hc := coeff_linePoly_top a b P
  rw [hLP0] at hc
  rw [Polynomial.coeff_zero] at hc
  exact hbev hc.symm

end Field

end Dvir

open Classical in
/-- Solution wrapper: Dvir's finite-field Kakeya theorem. -/
theorem solution {F : Type*} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (K : Set (Fin n → F)) [DecidablePred (· ∈ K)] [Fintype ↥K]
    (hK : ∀ b : Fin n → F, b ≠ 0 → ∃ a : Fin n → F, ∀ t : F, (fun j => a j + t * b j) ∈ K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ Fintype.card ↥K :=
  Dvir.dvir_kakeya hn K hK
