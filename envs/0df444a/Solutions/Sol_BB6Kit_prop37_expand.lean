-- Prove2me | solution 1 for BB6Kit.prop37_expand
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T06:50:15.871705+00:00
-- url     : https://prove2.me/submissions/6d6d438c-184b-4c43-8da5-bc7a7c64d83e

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi

open Finset

namespace PE

/-! ### Step A: multilinear expansion over subsets of rows -/

lemma prod_expand {N : ℕ} (c : ℝ) (u v : Fin N → ℝ) :
    ∏ i, (1 + c * u i) * v i =
      ∑ I ∈ (univ : Finset (Fin N)).powerset, c ^ (N - I.card) * ∏ i, (if i ∈ I then 1 else u i) * v i := by
  have h1 : ∏ i, (1 + c * u i) * v i = ∏ i, (v i + c * u i * v i) := by
    apply prod_congr rfl; intro i _; ring
  rw [h1, prod_add]
  apply sum_congr rfl
  intro I _
  rw [← prod_mul_prod_compl I (fun i => (if i ∈ I then 1 else u i) * v i)]
  have e1 : ∏ i ∈ I, (if i ∈ I then (1:ℝ) else u i) * v i = ∏ i ∈ I, v i := by
    apply prod_congr rfl; intro i hi; rw [if_pos hi, one_mul]
  have e2 : ∏ i ∈ Iᶜ, (if i ∈ I then (1:ℝ) else u i) * v i = ∏ i ∈ Iᶜ, u i * v i := by
    apply prod_congr rfl; intro i hi; rw [mem_compl] at hi; rw [if_neg hi]
  have e3 : ∏ i ∈ univ \ I, c * u i * v i = c ^ (N - I.card) * ∏ i ∈ Iᶜ, u i * v i := by
    rw [← compl_eq_univ_sdiff]
    have : ∏ i ∈ Iᶜ, c * u i * v i = ∏ i ∈ Iᶜ, (c * (u i * v i)) := prod_congr rfl (fun i _ => by ring)
    rw [this, prod_mul_distrib, prod_const, card_compl, Fintype.card_fin]
  rw [e1, e2, e3]
  ring

lemma multilin {N : ℕ} (c : ℝ) (θ φ : Fin N → Fin N → ℝ) :
    (Matrix.of fun i j => (1 + c * θ i j) * φ i j).det =
      ∑ I ∈ (univ : Finset (Fin N)).powerset, c ^ (N - I.card) *
        (Matrix.of fun i j => (if i ∈ I then (1:ℝ) else θ i j) * φ i j).det := by
  have h : ∀ I : Finset (Fin N), (Matrix.of fun i j => (if i ∈ I then (1:ℝ) else θ i j) * φ i j).det =
      ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i, (if i ∈ I then (1:ℝ) else θ i (σ i)) * φ i (σ i) := by
    intro I
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [h, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hp := prod_expand c (fun i => θ i (σ i)) (fun i => φ i (σ i))
  beta_reduce at hp
  rw [hp, smul_sum]
  apply sum_congr rfl
  intro I _
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

lemma mem_rowSet {K L : ℕ} (p : ℕ × ℕ × ℕ) :
    p ∈ BB6Kit.rowSet K L ↔ p.1 < K ∧ p.2.1 < K ∧ p.2.2 < L ∧ p.1 + p.2.1 ≤ K - 1 := by
  unfold BB6Kit.rowSet
  simp only [mem_filter, mem_product, mem_range]
  tauto

/-! ### Step B: triangular row operations -/

lemma tri {N K L : ℕ} (kml : Fin N → ℕ × ℕ × ℕ) (hinj : Function.Injective kml)
    (hmem : ∀ i, kml i ∈ BB6Kit.rowSet K L) (hsurj : ∀ p ∈ BB6Kit.rowSet K L, ∃ i, kml i = p)
    (a b : ℕ → ℕ → ℝ) (x y : Fin N → ℝ) (W : ℕ → Fin N → ℝ) :
    (Matrix.of fun i j => (∑ k' ∈ range ((kml i).1 + 1), a (kml i).1 k' * x j ^ k') *
        (∑ m' ∈ range ((kml i).2.1 + 1), b (kml i).2.1 m' * y j ^ m') * W (kml i).2.2 j).det =
    (Matrix.of fun i j => a (kml i).1 (kml i).1 * b (kml i).2.1 (kml i).2.1 * x j ^ (kml i).1 *
        y j ^ (kml i).2.1 * W (kml i).2.2 j).det := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin N) (Fin N) ℝ,
      P = Matrix.of fun i j => x j ^ (kml i).1 * y j ^ (kml i).2.1 * W (kml i).2.2 j := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℝ, U = Matrix.of fun i i' =>
      if (kml i').2.2 = (kml i).2.2 ∧ (kml i').1 ≤ (kml i).1 ∧ (kml i').2.1 ≤ (kml i).2.1 then
        a (kml i).1 (kml i').1 * b (kml i).2.1 (kml i').2.1 else 0 := ⟨_, rfl⟩
  -- the left matrix is U * P
  have hUP : (Matrix.of fun i j => (∑ k' ∈ range ((kml i).1 + 1), a (kml i).1 k' * x j ^ k') *
        (∑ m' ∈ range ((kml i).2.1 + 1), b (kml i).2.1 m' * y j ^ m') * W (kml i).2.2 j) = U * P := by
    ext i j
    rw [Matrix.mul_apply, hU, hP]
    simp only [Matrix.of_apply, ite_mul, zero_mul]
    rw [← sum_filter]
    have hR : (∑ k' ∈ range ((kml i).1 + 1), a (kml i).1 k' * x j ^ k') *
        (∑ m' ∈ range ((kml i).2.1 + 1), b (kml i).2.1 m' * y j ^ m') * W (kml i).2.2 j =
        ∑ q ∈ range ((kml i).1 + 1) ×ˢ range ((kml i).2.1 + 1),
          a (kml i).1 q.1 * x j ^ q.1 * (b (kml i).2.1 q.2 * y j ^ q.2) * W (kml i).2.2 j := by
      rw [sum_mul_sum, sum_mul]
      simp only [sum_product, sum_mul]
    rw [hR]
    symm
    apply sum_bij (fun i' _ => ((kml i').1, (kml i').2.1))
    · intro i' hi'
      simp only [mem_filter, mem_univ, true_and] at hi'
      simp only [mem_product, mem_range]
      omega
    · intro i1 h1 i2 h2 he
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      simp only [Prod.mk.injEq] at he
      apply hinj
      exact Prod.ext he.1 (Prod.ext he.2 (h1.1.trans h2.1.symm))
    · intro q hq
      simp only [mem_product, mem_range] at hq
      have hi := (mem_rowSet (kml i)).mp (hmem i)
      obtain ⟨i', hi'⟩ := hsurj (q.1, q.2, (kml i).2.2) (by
        rw [mem_rowSet]
        dsimp only
        omega)
      refine ⟨i', ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        rw [hi']
        refine ⟨rfl, ?_, ?_⟩
        · show q.1 ≤ (kml i).1
          omega
        · show q.2 ≤ (kml i).2.1
          omega
      · rw [hi']
    · intro i' hi'
      simp only [mem_filter, mem_univ, true_and] at hi'
      rw [hi'.1]
      ring
  -- det U is the product of its diagonal (U is triangular after sorting rows by k + m)
  have hdetU : U.det = ∏ i, a (kml i).1 (kml i).1 * b (kml i).2.1 (kml i).2.1 := by
    have hmono : Monotone ((fun i => (kml i).1 + (kml i).2.1) ∘ Tuple.sort (fun i => (kml i).1 + (kml i).2.1)) :=
      Tuple.monotone_sort _
    rw [← Matrix.det_submatrix_equiv_self (Tuple.sort (fun i => (kml i).1 + (kml i).2.1)) U]
    rw [Matrix.det_of_lowerTriangular]
    · calc ∏ i, (U.submatrix (Tuple.sort (fun i => (kml i).1 + (kml i).2.1))
              (Tuple.sort (fun i => (kml i).1 + (kml i).2.1))) i i
            = ∏ i, U (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) i)
                (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) i) := rfl
        _ = ∏ i, U i i := Equiv.prod_comp (Tuple.sort (fun i => (kml i).1 + (kml i).2.1)) (fun i => U i i)
        _ = ∏ i, a (kml i).1 (kml i).1 * b (kml i).2.1 (kml i).2.1 := by
            apply prod_congr rfl
            intro i _
            rw [hU]
            simp
    · intro i j hij
      rw [OrderDual.toDual_lt_toDual] at hij
      simp only [Matrix.submatrix_apply]
      rw [hU]
      simp only [Matrix.of_apply]
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      have hk : (kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) i)).1 +
          (kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) i)).2.1 ≤
          (kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) j)).1 +
          (kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) j)).2.1 := hmono hij.le
      have he : kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) j) =
          kml (Tuple.sort (fun i => (kml i).1 + (kml i).2.1) i) :=
        Prod.ext (by omega) (Prod.ext (by omega) h1)
      have := (Tuple.sort (fun i => (kml i).1 + (kml i).2.1)).injective (hinj he)
      exact absurd this (ne_of_gt hij)
  -- right matrix is diag(a b) * P
  have hD : (Matrix.of fun i j => a (kml i).1 (kml i).1 * b (kml i).2.1 (kml i).2.1 * x j ^ (kml i).1 *
        y j ^ (kml i).2.1 * W (kml i).2.2 j) =
      Matrix.diagonal (fun i => a (kml i).1 (kml i).1 * b (kml i).2.1 (kml i).2.1) * P := by
    ext i j
    rw [Matrix.diagonal_mul, hP]
    simp only [Matrix.of_apply]
    ring
  rw [hUP, hD, Matrix.det_mul, Matrix.det_mul, hdetU, Matrix.det_diagonal]

/-! ### Binomials as polynomials -/

noncomputable def coefP (c d : ℝ) (k k' : ℕ) : ℝ :=
  (Polynomial.C ((k.factorial : ℝ)⁻¹) *
    (descPochhammer ℝ k).comp (Polynomial.C c * Polynomial.X + Polynomial.C (c * d))).coeff k'

lemma coefP_natDegree (c d : ℝ) (hc : c ≠ 0) (k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      (descPochhammer ℝ k).comp (Polynomial.C c * Polynomial.X + Polynomial.C (c * d))).natDegree ≤ k := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree, Polynomial.natDegree_linear hc, mul_one]

lemma coefP_diag (c d : ℝ) (hc : c ≠ 0) (k : ℕ) : coefP c d k k = c ^ k / (k.factorial : ℝ) := by
  unfold coefP
  rw [Polynomial.coeff_C_mul]
  have h := Polynomial.coeff_comp_degree_mul_degree (p := descPochhammer ℝ k)
    (q := Polynomial.C c * Polynomial.X + Polynomial.C (c * d)) (by rw [Polynomial.natDegree_linear hc]; norm_num)
  rw [descPochhammer_natDegree, Polynomial.natDegree_linear hc, mul_one, (monic_descPochhammer ℝ k).leadingCoeff,
    Polynomial.leadingCoeff_linear hc, one_mul] at h
  rw [h]
  ring

lemma coefP_eval (c d : ℝ) (hc : c ≠ 0) (k n : ℕ) (η : ℝ) (hn : (n : ℝ) = c * (η + d)) :
    ((n.choose k : ℕ) : ℝ) = ∑ k' ∈ range (k + 1), coefP c d k k' * η ^ k' := by
  unfold coefP
  rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (coefP_natDegree c d hc k))]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  rw [show c * η + c * d = (n : ℝ) by rw [hn]; ring, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]

/-! ### Row set sums -/

lemma tri_sum (q : ℕ) : ∑ v ∈ range q, ((q - v : ℕ) : ℝ) = (q:ℝ) * ((q:ℝ) + 1) / 2 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∑ v ∈ range n, ((n + 1 - v : ℕ) : ℝ) = ∑ v ∈ range n, (((n - v : ℕ) : ℝ) + 1) := by
      apply sum_congr rfl
      intro v hv
      rw [mem_range] at hv
      rw [show n + 1 - v = (n - v) + 1 by omega, Nat.cast_add, Nat.cast_one]
    rw [h, sum_add_distrib, ih, show n + 1 - n = 1 by omega]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

lemma gauss (L : ℕ) : ∑ v ∈ range L, (v : ℝ) = (L : ℝ) * ((L : ℝ) - 1) / 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma rowsum (K L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ BB6Kit.rowSet K L, f p.2.2 = ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v := by
  unfold BB6Kit.rowSet
  rw [sum_filter, sum_product]
  trans ∑ k ∈ range K, ((K - k : ℕ) : ℝ) * ∑ v ∈ range L, f v
  · apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [sum_product]
    try dsimp only
    have h2 : ∀ mm ∈ range K, ∑ v ∈ range L, (if k + mm ≤ K - 1 then f v else 0) =
        (if mm < K - k then (1:ℝ) else 0) * ∑ v ∈ range L, f v := by
      intro mm hmm
      rw [mem_range] at hmm
      by_cases hc : mm < K - k
      · rw [if_pos hc, one_mul]
        apply sum_congr rfl
        intro v _
        rw [if_pos (show k + mm ≤ K - 1 by omega)]
      · rw [if_neg hc, zero_mul]
        apply sum_eq_zero
        intro v _
        rw [if_neg (show ¬ (k + mm ≤ K - 1) by omega)]
    rw [sum_congr rfl h2, ← sum_mul, sum_boole]
    congr 1
    have hf2 : (range K).filter (fun mm => mm < K - k) = range (K - k) := by
      ext mm
      simp only [mem_filter, mem_range]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    rw [hf2, card_range]
  · rw [← sum_mul, tri_sum K]

end PE

namespace PE

lemma pw (x : ℝ) (n : ℕ) (hx : 0 < x) : x ^ n = Real.exp (n * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

lemma exp3 (C A B D X Y Z W : ℝ) (h : A + B + D = X + (Y + Z) + W) :
    C * Real.exp A * Real.exp B * Real.exp D = Real.exp X * (C * (Real.exp Y * Real.exp Z)) * Real.exp W := by
  have e1 : Real.exp A * Real.exp B * Real.exp D = Real.exp (A + B + D) := by rw [Real.exp_add, Real.exp_add]
  have e2 : Real.exp X * (Real.exp Y * Real.exp Z) * Real.exp W = Real.exp (X + (Y + Z) + W) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  calc C * Real.exp A * Real.exp B * Real.exp D = C * (Real.exp A * Real.exp B * Real.exp D) := by ring
    _ = C * (Real.exp X * (Real.exp Y * Real.exp Z) * Real.exp W) := by rw [e1, e2, h]
    _ = Real.exp X * (C * (Real.exp Y * Real.exp Z)) * Real.exp W := by ring

/-- Entry identity: `Δ_{ij} = rowfactor_i · (binomials · α^{λη} α^{λζ} (1 + Λ′θ)) · colfactor_j`. -/
lemma entry (L R S T b1 b2 b3 c1 c2 c3 c4 α1 α2 α3 k m ℓ r s t : ℕ) (Λ Lp : ℝ)
    (hΛ : Λ = (b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ))
    (hLpdef : Lp = BB6Kit.lamPrime L T b3 Λ) (hLp : Lp ≠ 0)
    (hα1 : 0 < α1) (hα2 : 0 < α2) (hα3 : 0 < α3) (hb3 : 0 < b3) (hc2 : 0 < c2) (hc4 : 0 < c4)
    (hβ1 : (c1 : ℝ) / c2 = (b1 : ℝ) / b3) (hβ2 : (c3 : ℝ) / c4 = (b2 : ℝ) / b3) :
    (Nat.choose (r * c2 + t * c1) k : ℝ) * (Nat.choose (s * c4 + t * c3) m : ℝ) *
        (α1 : ℝ) ^ (ℓ * r) * (α2 : ℝ) ^ (ℓ * s) * (α3 : ℝ) ^ (ℓ * t) =
      Real.exp (BB6Psi.lam L (k, m, ℓ) * ((((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2)) * Real.log (α1 : ℝ) +
          (((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2)) * Real.log (α2 : ℝ))) *
        ((Nat.choose (r * c2 + t * c1) k : ℝ) * (Nat.choose (s * c4 + t * c3) m : ℝ) *
          (Real.exp (BB6Psi.lam L (k, m, ℓ) * (BB6Psi.eta R T c1 c2 (r, s, t) * Real.log (α1 : ℝ) +
              BB6Psi.zeta S T c3 c4 (r, s, t) * Real.log (α2 : ℝ))) *
            (1 + Lp * BB6Psi.theta L T b3 Λ (k, m, ℓ) (r, s, t)))) *
        Real.exp (((L : ℝ) - 1) / 2 * ((r : ℝ) * Real.log (α1 : ℝ) + (s : ℝ) * Real.log (α2 : ℝ) +
          (t : ℝ) * Real.log (α3 : ℝ))) := by
  have hb3r : (b3 : ℝ) ≠ 0 := by exact_mod_cast hb3.ne'
  have hc2r : (c2 : ℝ) ≠ 0 := by exact_mod_cast hc2.ne'
  have hc4r : (c4 : ℝ) ≠ 0 := by exact_mod_cast hc4.ne'
  rw [pw _ _ (by exact_mod_cast hα1), pw _ _ (by exact_mod_cast hα2), pw _ _ (by exact_mod_cast hα3)]
  have hθ : 1 + Lp * BB6Psi.theta L T b3 Λ (k, m, ℓ) (r, s, t) =
      Real.exp (-(BB6Psi.lam L (k, m, ℓ) * ((r, s, t) : ℕ × ℕ × ℕ).2.2 * Λ / (b3 : ℝ))) := by
    unfold BB6Psi.theta
    rw [← hLpdef]
    first
    | (field_simp; ring)
    | field_simp
    | ring
  rw [hθ]
  apply exp3
  unfold BB6Psi.lam BB6Psi.eta BB6Psi.zeta
  dsimp only
  rw [hβ1, hβ2, hΛ]
  push_cast
  first
  | (field_simp; ring)
  | field_simp
  | ring

end PE

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) :
    ((BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst : ℝ) : ℂ) =
      (((α1 : ℝ) ^ (BB6Kit.MK L N rst Prod.fst) * (α2 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.1)) *
          (α3 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.2)) : ℝ) : ℂ) *
        ∑ I ∈ (Finset.univ : Finset (Fin N)).powerset,
          ((BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) : ℝ) : ℂ) * BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I 1 := by
  -- reduced coefficients
  have hg13 : 0 < Nat.gcd b1 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hg23 : 0 < Nat.gcd b2 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hc2 : 0 < b3 / Nat.gcd b1 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg13
  have hc4 : 0 < b3 / Nat.gcd b2 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg23
  have hb3r : (b3 : ℝ) ≠ 0 := by exact_mod_cast hb3.ne'
  have hβ1 : ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) = (b1 : ℝ) / b3 := by
    have hg : ((Nat.gcd b1 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg13.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b1 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b1 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  have hβ2 : ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) = (b2 : ℝ) / b3 := by
    have hg : ((Nat.gcd b2 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg23.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b2 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b2 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  generalize b1 / Nat.gcd b1 b3 = c1 at hβ1 ⊢
  generalize b3 / Nat.gcd b1 b3 = c2 at hβ1 hc2 ⊢
  generalize b2 / Nat.gcd b2 b3 = c3 at hβ2 ⊢
  generalize b3 / Nat.gcd b2 b3 = c4 at hβ2 hc4 ⊢
  have hc2r : (c2 : ℝ) ≠ 0 := by exact_mod_cast hc2.ne'
  have hc4r : (c4 : ℝ) ≠ 0 := by exact_mod_cast hc4.ne'
  -- Λ and Λ′
  generalize hΛdef : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) = Λ at hΛ ⊢
  have hNpos : 0 < N := by
    rw [hN]
    refine Nat.div_pos ?_ (by norm_num)
    have : 3 * 4 * 5 ≤ K * (K + 1) * L := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) hL
    omega
  have hprod : 0 < R * S * T := lt_of_lt_of_le hNpos hRST
  have hT : 0 < T := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hLpos : 0 < BB6Kit.lamPrime L T b3 Λ := by
    unfold BB6Kit.lamPrime
    have hLr : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hTr : (0:ℝ) < T := by exact_mod_cast hT
    have hb3p : (0:ℝ) < b3 := by exact_mod_cast hb3
    exact div_pos (mul_pos (abs_pos.mpr hΛ) (mul_pos (mul_pos hLr hTr) (Real.exp_pos _))) (by linarith)
  generalize hLpdef : BB6Kit.lamPrime L T b3 Λ = Lp at hLpos ⊢
  have hLp : Lp ≠ 0 := hLpos.ne'
  -- the rows enumerate the row set
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  have hcardR : ((BB6Kit.rowSet K L).card : ℝ) = N := by
    rw [hNA]
    have := PE.rowsum K L (fun _ => (1:ℝ))
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this
  have hcard : (BB6Kit.rowSet K L).card = N := by exact_mod_cast hcardR
  have himg : univ.image kml = BB6Kit.rowSet K L := by
    apply eq_of_subset_of_card_le
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨i, _, rfl⟩ := hp
      exact hrows.2 i
    · rw [card_image_of_injective _ hrows.1, card_univ, Fintype.card_fin, hcard]
  have hsurj : ∀ p ∈ BB6Kit.rowSet K L, ∃ i, kml i = p := by
    intro p hp
    rw [← himg, mem_image] at hp
    obtain ⟨i, _, h⟩ := hp
    exact ⟨i, h⟩
  have hsumℓ : ∑ i, BB6Psi.lam L (kml i) = 0 := by
    have e : ∑ i, ((kml i).2.2 : ℝ) = ∑ p ∈ BB6Kit.rowSet K L, (p.2.2 : ℝ) := by
      rw [← himg, sum_image (by intro x _ y _ h; exact hrows.1 h)]
    unfold BB6Psi.lam
    rw [sum_sub_distrib, e, PE.rowsum K L (fun v => (v : ℝ)), PE.gauss, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, hNA]
    ring
  -- notation
  have hα1r : (0:ℝ) < α1 := by exact_mod_cast (show 0 < α1 by omega)
  have hα2r : (0:ℝ) < α2 := by exact_mod_cast (show 0 < α2 by omega)
  have hα3r : (0:ℝ) < α3 := by exact_mod_cast (show 0 < α3 by omega)
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ, η0 = ((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ0 : ℝ, ζ0 = ((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  -- real-valued φ and Ψ
  obtain ⟨φR, hφR⟩ : ∃ φR : Fin N → Fin N → ℝ, φR = fun i j =>
      ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ))) *
        BB6Psi.eta R T c1 c2 (rst j) ^ (kml i).1 * BB6Psi.zeta S T c3 c4 (rst j) ^ (kml i).2.1 *
        Real.exp (BB6Psi.lam L (kml i) * (BB6Psi.eta R T c1 c2 (rst j) * Real.log (α1 : ℝ) +
          BB6Psi.zeta S T c3 c4 (rst j) * Real.log (α2 : ℝ))) := ⟨_, rfl⟩
  have hΨ : ∀ I : Finset (Fin N), BB6Psi.psi N L R S T c1 c2 c3 c4 b3 α1 α2 Λ kml rst I 1 =
      (((Matrix.of fun i j => (if i ∈ I then (1:ℝ) else BB6Psi.theta L T b3 Λ (kml i) (rst j)) * φR i j).det : ℝ) : ℂ) := by
    intro I
    rw [show (((Matrix.of fun i j => (if i ∈ I then (1:ℝ) else BB6Psi.theta L T b3 Λ (kml i) (rst j)) * φR i j).det : ℝ) : ℂ)
        = Complex.ofRealHom ((Matrix.of fun i j => (if i ∈ I then (1:ℝ) else BB6Psi.theta L T b3 Λ (kml i) (rst j)) * φR i j).det)
        from rfl, RingHom.map_det]
    unfold BB6Psi.psi
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hφR]
    simp only [Matrix.of_apply, BB6Psi.phi, one_mul, Complex.ofRealHom_eq_coe]
    split_ifs <;> push_cast <;> ring_nf
  -- the real identity
  have hreal : BB6Delta.deltaR N c1 c2 c3 c4 α1 α2 α3 kml rst =
      ((α1 : ℝ) ^ (BB6Kit.MK L N rst Prod.fst) * (α2 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.1)) *
          (α3 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.2))) *
        ∑ I ∈ (univ : Finset (Fin N)).powerset, Lp ^ (N - I.card) *
          (Matrix.of fun i j => (if i ∈ I then (1:ℝ) else BB6Psi.theta L T b3 Λ (kml i) (rst j)) * φR i j).det := by
    obtain ⟨W, hW⟩ : ∃ W : ℕ → Fin N → ℝ, W = fun ℓ j =>
        Real.exp (BB6Psi.lam L (0, 0, ℓ) * (BB6Psi.eta R T c1 c2 (rst j) * Real.log (α1 : ℝ) +
          BB6Psi.zeta S T c3 c4 (rst j) * Real.log (α2 : ℝ))) *
          (1 + Lp * BB6Psi.theta L T b3 Λ (0, 0, ℓ) (rst j)) := ⟨_, rfl⟩
    -- step 1: factor rows and columns
    have hA : (Matrix.of fun i j =>
        (Nat.choose ((rst j).1 * c2 + (rst j).2.2 * c1) (kml i).1 : ℝ) *
          (Nat.choose ((rst j).2.1 * c4 + (rst j).2.2 * c3) (kml i).2.1 : ℝ) *
          (α1 : ℝ) ^ ((kml i).2.2 * (rst j).1) * (α2 : ℝ) ^ ((kml i).2.2 * (rst j).2.1) *
          (α3 : ℝ) ^ ((kml i).2.2 * (rst j).2.2)) =
        Matrix.diagonal (fun i => Real.exp (BB6Psi.lam L (kml i) * (η0 * Real.log (α1 : ℝ) + ζ0 * Real.log (α2 : ℝ)))) *
          (Matrix.of fun i j =>
            (Nat.choose ((rst j).1 * c2 + (rst j).2.2 * c1) (kml i).1 : ℝ) *
              (Nat.choose ((rst j).2.1 * c4 + (rst j).2.2 * c3) (kml i).2.1 : ℝ) * W (kml i).2.2 j) *
          Matrix.diagonal (fun j => Real.exp (((L : ℝ) - 1) / 2 * (((rst j).1 : ℝ) * Real.log (α1 : ℝ) +
            ((rst j).2.1 : ℝ) * Real.log (α2 : ℝ) + ((rst j).2.2 : ℝ) * Real.log (α3 : ℝ)))) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hη0, hζ0, hW]
      simp only [Matrix.of_apply]
      exact PE.entry L R S T b1 b2 b3 c1 c2 c3 c4 α1 α2 α3 (kml i).1 (kml i).2.1 (kml i).2.2
        (rst j).1 (rst j).2.1 (rst j).2.2 Λ Lp hΛdef.symm hLpdef.symm hLp (by omega) (by omega) (by omega)
        hb3 hc2 hc4 hβ1 hβ2
    -- step 2: binomials are polynomials in η, ζ; triangular reduction
    have hB : (Matrix.of fun i j =>
        (Nat.choose ((rst j).1 * c2 + (rst j).2.2 * c1) (kml i).1 : ℝ) *
          (Nat.choose ((rst j).2.1 * c4 + (rst j).2.2 * c3) (kml i).2.1 : ℝ) * W (kml i).2.2 j) =
        Matrix.of fun i j =>
          (∑ k' ∈ range ((kml i).1 + 1), PE.coefP (c2 : ℝ) η0 (kml i).1 k' * BB6Psi.eta R T c1 c2 (rst j) ^ k') *
          (∑ m' ∈ range ((kml i).2.1 + 1), PE.coefP (c4 : ℝ) ζ0 (kml i).2.1 m' * BB6Psi.zeta S T c3 c4 (rst j) ^ m') *
          W (kml i).2.2 j := by
      ext i j
      simp only [Matrix.of_apply]
      rw [PE.coefP_eval (c2 : ℝ) η0 hc2r (kml i).1 _ (BB6Psi.eta R T c1 c2 (rst j)) (by
            rw [hη0]; unfold BB6Psi.eta; push_cast; first | (field_simp; ring) | field_simp | ring),
        PE.coefP_eval (c4 : ℝ) ζ0 hc4r (kml i).2.1 _ (BB6Psi.zeta S T c3 c4 (rst j)) (by
            rw [hζ0]; unfold BB6Psi.zeta; push_cast; first | (field_simp; ring) | field_simp | ring)]
    have hC : (Matrix.of fun i j => PE.coefP (c2 : ℝ) η0 (kml i).1 (kml i).1 * PE.coefP (c4 : ℝ) ζ0 (kml i).2.1 (kml i).2.1 *
          BB6Psi.eta R T c1 c2 (rst j) ^ (kml i).1 * BB6Psi.zeta S T c3 c4 (rst j) ^ (kml i).2.1 * W (kml i).2.2 j) =
        Matrix.of fun i j => (1 + Lp * BB6Psi.theta L T b3 Λ (kml i) (rst j)) * φR i j := by
      ext i j
      simp only [Matrix.of_apply]
      rw [PE.coefP_diag _ _ hc2r, PE.coefP_diag _ _ hc4r, hW, hφR]
      unfold BB6Psi.theta BB6Psi.lam
      dsimp only
      ring
    have hdetB := PE.tri kml hrows.1 hrows.2 hsurj (fun k k' => PE.coefP (c2 : ℝ) η0 k k')
      (fun m m' => PE.coefP (c4 : ℝ) ζ0 m m') (fun j => BB6Psi.eta R T c1 c2 (rst j))
      (fun j => BB6Psi.zeta S T c3 c4 (rst j)) W
    beta_reduce at hdetB
    -- assemble
    unfold BB6Delta.deltaR
    rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hdetB, hC,
      PE.multilin Lp (fun i j => BB6Psi.theta L T b3 Λ (kml i) (rst j)) φR]
    try beta_reduce
    rw [← Real.exp_sum, ← Real.exp_sum]
    have hrow0 : ∑ i, BB6Psi.lam L (kml i) * (η0 * Real.log (α1 : ℝ) + ζ0 * Real.log (α2 : ℝ)) = 0 := by
      rw [← sum_mul, hsumℓ, zero_mul]
    rw [hrow0, Real.exp_zero, one_mul]
    have hcol : Real.exp (∑ j, ((L : ℝ) - 1) / 2 * (((rst j).1 : ℝ) * Real.log (α1 : ℝ) +
            ((rst j).2.1 : ℝ) * Real.log (α2 : ℝ) + ((rst j).2.2 : ℝ) * Real.log (α3 : ℝ))) =
        (α1 : ℝ) ^ (BB6Kit.MK L N rst Prod.fst) * (α2 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.1)) *
          (α3 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.2)) := by
      rw [Real.rpow_def_of_pos hα1r, Real.rpow_def_of_pos hα2r, Real.rpow_def_of_pos hα3r, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      unfold BB6Kit.MK
      simp only [mul_sum, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    rw [hcol]
    try beta_reduce
    ring
  rw [hreal, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  apply sum_congr rfl
  intro I _
  rw [Complex.ofReal_mul, hΨ I]
