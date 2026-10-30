-- Prove2me | solution 1 for DiazModulus.iteratedDeriv_det_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:23:39.394987+00:00
-- url     : https://prove2.me/submissions/dcac64fe-571b-42e1-8e64-770745882ab1

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Leibniz rule for the determinant of entire functions

Write `det (g l μ x) = Σ_π sign π · Π_μ g (π μ) μ x` (`Matrix.det_apply'`). The `j`-th derivative is
linear, so it is enough to differentiate each product `Π_μ h μ`. For a product over `Fin L` of
entire functions we prove the general Leibniz rule
`(Π_μ h μ)^{(j)} = Σ_{Σ q = j} multinomial(q) · Π_μ h μ^{(q μ)}` by induction on `L`: split off
the factor `μ = 0` (`Fin.prod_univ_succ`), apply the binomial Leibniz rule
`iteratedDeriv_fun_mul`, use the induction hypothesis on the remaining product, and reindex the
double sum `Σ_{i ≤ j} Σ_{q' ∈ antidiagonalTuple L (j - i)}` as the sum over
`antidiagonalTuple (L+1) j` through `q ↦ (q 0, Fin.tail q)`; the coefficients match by
`multinomial (cons i q') = choose (i + Σ q') i · multinomial q'` (`Nat.multinomial_cons`).
Exchanging the sums over permutations and over `q` and folding `Matrix.det_apply'` back gives
the statement. Complex differentiability supplies all the smoothness (`Differentiable.contDiff`).
-/

namespace C14_A2
open DiazModulus

lemma multinomial_fin_cons {L : ℕ} (i : ℕ) (q : Fin L → ℕ) :
    Nat.multinomial Finset.univ (Fin.cons i q : Fin (L + 1) → ℕ) =
      (i + ∑ μ, q μ).choose i * Nat.multinomial Finset.univ q := by
  rw [Fin.univ_succ, Nat.multinomial_cons]
  simp [Nat.multinomial, Finset.sum_map, Finset.prod_map]

lemma leibniz_prod : ∀ (L : ℕ) (h : Fin L → ℂ → ℂ), (∀ μ, Differentiable ℂ (h μ)) →
    ∀ (j : ℕ) (z : ℂ), iteratedDeriv j (fun x => ∏ μ, h μ x) z =
      ∑ q ∈ Finset.Nat.antidiagonalTuple L j, (Nat.multinomial Finset.univ q : ℂ) *
        ∏ μ, iteratedDeriv (q μ) (h μ) z
  | 0, h, _, j, z => by
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | L + 1, h, hh, j, z => by
    have hprod : (fun x => ∏ μ : Fin (L + 1), h μ x) =
        fun x => h 0 x * ∏ μ : Fin L, h μ.succ x := by
      funext x; exact Fin.prod_univ_succ _
    have htail : Differentiable ℂ (fun x => ∏ μ : Fin L, h μ.succ x) := by
      intro x; exact DifferentiableAt.fun_finsetProd (fun μ _ => hh μ.succ x)
    rw [hprod, iteratedDeriv_fun_mul (hh 0).contDiff.contDiffAt htail.contDiff.contDiffAt]
    set G : (Fin (L + 1) → ℕ) → ℂ := fun q =>
      (Nat.multinomial Finset.univ q : ℂ) * ∏ μ, iteratedDeriv (q μ) (h μ) z with hG
    have key : ∑ q ∈ Finset.Nat.antidiagonalTuple (L + 1) j, G q =
        ∑ x ∈ (Finset.range (j + 1)).sigma (fun i => Finset.Nat.antidiagonalTuple L (j - i)),
          G (Fin.cons x.1 x.2) := by
      refine Finset.sum_nbij' (fun q => ⟨q 0, Fin.tail q⟩) (fun x => Fin.cons x.1 x.2)
        ?_ ?_ ?_ ?_ ?_
      · intro q hq
        simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hq
        simp only [Finset.mem_sigma, Finset.mem_range,
          Finset.Nat.mem_antidiagonalTuple, Fin.tail]
        omega
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_range,
          Finset.Nat.mem_antidiagonalTuple] at hx
        simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
        omega
      · intro q _; simp
      · intro x _; simp
      · intro q _; simp
    show _ = ∑ q ∈ Finset.Nat.antidiagonalTuple (L + 1) j, G q
    rw [key, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [leibniz_prod L (fun μ => h μ.succ) (fun μ => hh μ.succ) (j - i) z, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hsum : ∑ μ, q μ = j - i := Finset.Nat.mem_antidiagonalTuple.mp hq
    simp only [hG, multinomial_fin_cons, hsum, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Nat.add_sub_cancel' hij]
    push_cast
    ring

end C14_A2

open DiazModulus C14_A2 in
theorem solution {L : ℕ} (g : Fin L → Fin L → ℂ → ℂ) (hg : ∀ l μ, Differentiable ℂ (g l μ))
    (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun x => (Matrix.of fun l μ => g l μ x).det) z =
      ∑ q ∈ Finset.Nat.antidiagonalTuple L j, (Nat.multinomial Finset.univ q : ℂ) *
        (Matrix.of fun l μ => iteratedDeriv (q μ) (g l μ) z).det := by
  have hdet : (fun x => (Matrix.of fun l μ => g l μ x).det) = fun x =>
      ∑ π : Equiv.Perm (Fin L), ((Equiv.Perm.sign π : ℤ) : ℂ) * ∏ μ, g (π μ) μ x := by
    funext x; rw [Matrix.det_apply']; rfl
  have hP : ∀ π : Equiv.Perm (Fin L), Differentiable ℂ (fun x => ∏ μ, g (π μ) μ x) :=
    fun π x => DifferentiableAt.fun_finsetProd (fun μ _ => hg (π μ) μ x)
  rw [hdet, iteratedDeriv_fun_sum (fun π _ =>
    ((hP π).const_mul ((Equiv.Perm.sign π : ℤ) : ℂ)).contDiff.contDiffAt)]
  simp_rw [iteratedDeriv_const_mul _ (hP _).contDiff.contDiffAt]
  simp_rw [leibniz_prod L _ (fun μ => hg _ μ), Finset.mul_sum, Matrix.det_apply', Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  ring
