-- Prove2me | solution 1 for FourExp.exists_int_norm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:44:40.538594+00:00
-- url     : https://prove2.me/submissions/8d3c8cdd-5930-41e7-b189-ca171767d5e7

import Mathlib

/-!
# The norm of `Pol(ω, ω₁)` down to `ℚ(ω)`, with its size

`Q ∈ ℤ[X][Y]` is monic in `Y` of degree `d`, vanishes at `(ω, ω₁)`, and no nonzero polynomial of
`Y`-degree below `d` vanishes there. For `Pol` of `Y`-degree below `d` with `Pol(ω, ω₁) ≠ 0`, `P`
is the determinant of the matrix `M` of multiplication by `Pol` on `ℤ[X][Y]/(Q)` in the basis
`1, Y, …, Y^(d-1)`: column `k` holds the `Y`-coefficients of `Pol · Y^k mod Q`. It is the norm of
`Pol(ω, ω₁)` from `ℚ(ω, ω₁)` down to `ℚ(ω)` (Waldschmidt 1973, Lemma 7).

* With `ψ` the evaluation at `ω` and `v = (1, ω₁, …, ω₁^(d-1))`, `v ψ(M) = Pol(ω, ω₁) v`.
* `P ≠ 0`: a kernel vector `u` of `M` gives `U = ∑ u_k Y^k` with
  `Pol(ω, ω₁) U(ω, ω₁) = v ψ(M) ψ(u) = 0`, so `U = 0` by minimality.
* Size: `Pol · Y^k mod Q = ∑_n Pol_n (Y^(n+k) mod Q)` involves only the `Y^m mod Q` with `m < 2d`,
  whose coefficients have length and degree at most some `C`. The entries of `M` have length at
  most `b C` and degree at most `e + C`; expanding the determinant over permutations gives length
  at most `d! (b C)^d` and degree at most `d (e + C)`.
* Value: since `v₀ = 1`, `P(ω) = det ψ(M) = Pol(ω, ω₁) ∑_j ω₁^j adj(ψ(M))_{j0}`, and each cofactor
  is at most `d! t^d` with `t = b C max(1, |ω|)^(e+C)`.
-/

open Polynomial

namespace S7W3_exists_int_norm

/-- Size of `p ∈ ℤ[X]`: some `ph ∈ ℕ[X]` majorizes `p` coefficientwise, with `ph(1) ≤ b` and
`deg ph ≤ D`. -/
def Sz1 (p : ℤ[X]) (b D : ℕ) : Prop :=
  ∃ ph : ℕ[X], (∀ i, (p.coeff i).natAbs ≤ ph.coeff i) ∧ ph.eval 1 ≤ b ∧ ph.natDegree ≤ D

lemma sz1_mono {p : ℤ[X]} {b b' D D' : ℕ} (h : Sz1 p b D) (hb : b ≤ b') (hD : D ≤ D') :
    Sz1 p b' D' := by
  obtain ⟨ph, h1, h2, h3⟩ := h
  exact ⟨ph, h1, h2.trans hb, h3.trans hD⟩

lemma sz1_neg {p : ℤ[X]} {b D : ℕ} (h : Sz1 p b D) : Sz1 (-p) b D := by
  obtain ⟨ph, h1, h2, h3⟩ := h
  exact ⟨ph, fun i => by rw [coeff_neg, Int.natAbs_neg]; exact h1 i, h2, h3⟩

lemma sz1_add {p q : ℤ[X]} {b₁ b₂ D : ℕ} (hp : Sz1 p b₁ D) (hq : Sz1 q b₂ D) :
    Sz1 (p + q) (b₁ + b₂) D := by
  obtain ⟨ph, h1, h2, h3⟩ := hp
  obtain ⟨qh, g1, g2, g3⟩ := hq
  refine ⟨ph + qh, fun i => ?_, by rw [eval_add]; exact add_le_add h2 g2,
    (natDegree_add_le _ _).trans (max_le h3 g3)⟩
  rw [coeff_add, coeff_add]
  exact (Int.natAbs_add_le _ _).trans (add_le_add (h1 i) (g1 i))

lemma sz1_mul {p q : ℤ[X]} {b₁ b₂ D₁ D₂ : ℕ} (hp : Sz1 p b₁ D₁) (hq : Sz1 q b₂ D₂) :
    Sz1 (p * q) (b₁ * b₂) (D₁ + D₂) := by
  obtain ⟨ph, h1, h2, h3⟩ := hp
  obtain ⟨qh, g1, g2, g3⟩ := hq
  refine ⟨ph * qh, fun n => ?_, by rw [eval_mul]; exact Nat.mul_le_mul h2 g2,
    natDegree_mul_le.trans (add_le_add h3 g3)⟩
  rw [coeff_mul, coeff_mul]
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (h1 _) (g1 _)

lemma sz1_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (b : ι → ℕ) {D : ℕ}
    (h : ∀ i ∈ s, Sz1 (f i) (b i) D) : Sz1 (∑ i ∈ s, f i) (∑ i ∈ s, b i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i => by simp, by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact sz1_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sz1_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (b D : ι → ℕ)
    (h : ∀ i ∈ s, Sz1 (f i) (b i) (D i)) :
    Sz1 (∏ i ∈ s, f i) (∏ i ∈ s, b i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Finset.sum_empty]
    exact ⟨1, fun i => by rw [coeff_one, coeff_one]; split_ifs <;> simp, by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    exact sz1_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The coefficientwise absolute value is a majorant; its value at `1` is the length. -/
lemma sz1_self (p : ℤ[X]) : Sz1 p (∑ i ∈ p.support, (p.coeff i).natAbs) p.natDegree := by
  refine ⟨∑ i ∈ p.support, monomial i (p.coeff i).natAbs, fun n => ?_, ?_,
    natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (natDegree_monomial_le _).trans (le_natDegree_of_mem_supp i hi)⟩
  · rw [finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · exact le_rfl
    · rw [notMem_support_iff.1 h, Int.natAbs_zero]
  · rw [eval_finsetSum]
    simp only [eval_monomial, one_pow, mul_one, le_refl]

/-- Finitely many polynomials have a common size bound. -/
lemma exists_sz1_bound {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ i ∈ s, Sz1 (f i) C C := by
  refine ⟨1 + ∑ i ∈ s, ((∑ n ∈ (f i).support, ((f i).coeff n).natAbs) + (f i).natDegree),
    Nat.le_add_right 1 _, fun i hi => ?_⟩
  have h := Finset.single_le_sum
    (fun j _ => Nat.zero_le ((∑ n ∈ (f j).support, ((f j).coeff n).natAbs) + (f j).natDegree)) hi
  exact sz1_mono (sz1_self (f i)) (by omega) (by omega)

lemma length_le_of_sz1 {p : ℤ[X]} {b D : ℕ} (h : Sz1 p b D) :
    ∑ i ∈ p.support, (p.coeff i).natAbs ≤ b := by
  obtain ⟨ph, h1, h2, -⟩ := h
  refine le_trans ?_ h2
  rw [eval_eq_sum, sum_def]
  simp only [one_pow, mul_one]
  refine (Finset.sum_le_sum fun i _ => h1 i).trans (Finset.sum_le_sum_of_subset fun i hi => ?_)
  rw [mem_support_iff] at hi ⊢
  intro h0
  have := h1 i
  rw [h0] at this
  exact hi (Int.natAbs_eq_zero.1 (Nat.le_zero.1 this))

lemma natDegree_le_of_sz1 {p : ℤ[X]} {b D : ℕ} (h : Sz1 p b D) : p.natDegree ≤ D := by
  obtain ⟨ph, h1, -, h3⟩ := h
  refine (natDegree_le_iff_coeff_eq_zero.2 fun i hi => ?_).trans h3
  have := h1 i
  rw [coeff_eq_zero_of_natDegree_lt hi] at this
  exact Int.natAbs_eq_zero.1 (Nat.le_zero.1 this)

/-- The value at `ω`: `|p(ω)| ≤ b max(1, |ω|)^D`. -/
lemma norm_aeval_le_of_sz1 {p : ℤ[X]} {b D : ℕ} (h : Sz1 p b D) (ω : ℂ) :
    ‖aeval ω p‖ ≤ b * max 1 ‖ω‖ ^ D := by
  have hpD : p.natDegree < D + 1 := Nat.lt_succ_of_le (natDegree_le_of_sz1 h)
  obtain ⟨ph, h1, h2, h3⟩ := h
  rw [aeval_eq_sum_range' hpD]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (D + 1), ‖p.coeff i • ω ^ i‖
      ≤ ∑ i ∈ Finset.range (D + 1), (ph.coeff i : ℝ) * max 1 ‖ω‖ ^ D := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [zsmul_eq_mul, norm_mul, norm_pow, Complex.norm_intCast, ← Int.cast_abs,
          ← Nat.cast_natAbs]
        exact mul_le_mul (Nat.cast_le.2 (h1 i))
          ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans
            (pow_le_pow_right₀ (le_max_left _ _) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))))
          (by positivity) (by positivity)
    _ = ((ph.eval 1 : ℕ) : ℝ) * max 1 ‖ω‖ ^ D := by
        rw [← Finset.sum_mul, eval_eq_sum_range' (Nat.lt_succ_of_le h3)]
        simp only [one_pow, mul_one, Nat.cast_sum]
    _ ≤ b * max 1 ‖ω‖ ^ D := mul_le_mul_of_nonneg_right (Nat.cast_le.2 h2) (by positivity)

/-- A complex determinant with entries bounded by `t`. -/
lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ t) :
    ‖A.det‖ ≤ n.factorial * t ^ n := by
  have h := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ) hA
  rw [Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-- A polynomial of `Y`-degree below `d`, evaluated as a sum over `Fin d`. -/
lemma eval₂_eq_sum_fin (ψ : ℤ[X] →+* ℂ) (ω₁ : ℂ) {B : ℤ[X][X]} {d : ℕ} (hB : B.natDegree < d) :
    eval₂ ψ ω₁ B = ∑ j : Fin d, ψ (B.coeff j) * ω₁ ^ (j : ℕ) := by
  rw [eval₂_eq_sum_range' ψ hB, Finset.sum_range]

/-- If `v A = γ v` and `v₀ = 1`, then `det A = γ (v adj A)₀`. -/
lemma det_factor {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (γ : ℂ)
    (hv : Matrix.vecMul v A = γ • v) (hv0 : v ⟨0, hd⟩ = 1) :
    A.det = γ * (Matrix.vecMul v A.adjugate) ⟨0, hd⟩ := by
  have h1 := Matrix.vecMul_vecMul v A A.adjugate
  rw [hv, Matrix.mul_adjugate] at h1
  have h2 := congrFun h1 ⟨0, hd⟩
  simp only [Matrix.smul_vecMul, Matrix.vecMul_smul, Matrix.vecMul_one, Pi.smul_apply,
    smul_eq_mul, hv0, mul_one] at h2
  exact h2.symm

end S7W3_exists_int_norm

open Polynomial S7W3_exists_int_norm

theorem solution (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) :
    ∃ c : ℕ, ∀ (Pol : Polynomial (Polynomial ℤ)) (b e : ℕ), Pol.natDegree < Q.natDegree →
      ∑ k ∈ Pol.support, ∑ i ∈ (Pol.coeff k).support, ((Pol.coeff k).coeff i).natAbs ≤ b →
      (∀ k, (Pol.coeff k).natDegree ≤ e) →
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Pol ≠ 0 →
      ∃ P : Polynomial ℤ, P ≠ 0 ∧
        ∑ i ∈ P.support, (P.coeff i).natAbs ≤ (c * b) ^ Q.natDegree ∧
        P.natDegree ≤ Q.natDegree * (e + c) ∧
        ‖Polynomial.aeval ω P‖ ≤
          ‖Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Pol‖ *
            (((c * b : ℕ) : ℝ) * max 1 ‖ω‖ ^ e) ^ Q.natDegree := by
  classical
  have hQ1 : Q ≠ 1 := by
    rintro rfl
    rw [eval₂_one] at hQroot
    exact one_ne_zero hQroot
  have hd0 : 0 < Q.natDegree := Nat.pos_of_ne_zero fun h => hQ1 (hQm.natDegree_eq_zero.1 h)
  set d := Q.natDegree
  set ψ : ℤ[X] →+* ℂ := eval₂RingHom (Int.castRingHom ℂ) ω
  -- a common size bound for the coefficients of `Y^m mod Q`, `m < 2d`
  obtain ⟨C, hC1, hC⟩ := exists_sz1_bound (Finset.range (2 * d) ×ˢ Finset.range d)
    fun mj : ℕ × ℕ => (X ^ mj.1 %ₘ Q).coeff mj.2
  obtain ⟨c, hcK, hcC⟩ : ∃ c : ℕ,
      (d * d.factorial : ℝ) * max 1 ‖ω₁‖ * (C * max 1 ‖ω‖ ^ C) ≤ c ∧ d.factorial * C ≤ c :=
    ⟨⌈(d * d.factorial : ℝ) * max 1 ‖ω₁‖ * (C * max 1 ‖ω‖ ^ C)⌉₊ + d.factorial * C,
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_right _ _), Nat.le_add_left _ _⟩
  refine ⟨c, fun Pol b e hPd hlen he hPol => ?_⟩
  -- the matrix of multiplication by `Pol` modulo `Q`
  set M : Matrix (Fin d) (Fin d) ℤ[X] := fun j k => ((Pol * X ^ (k : ℕ)) %ₘ Q).coeff j
  have hMe : ∀ j k : ℕ, ((Pol * X ^ k) %ₘ Q).coeff j =
      ∑ n ∈ Pol.support, Pol.coeff n * (X ^ (n + k) %ₘ Q).coeff j := by
    intro j k
    conv_lhs => rw [Pol.as_sum_support_C_mul_X_pow, Finset.sum_mul, ← modByMonicHom_apply, map_sum]
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← pow_add, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul,
      modByMonicHom_apply]
  have hMsz : ∀ j k : Fin d, Sz1 (M j k) (b * C) (e + C) := by
    intro j k
    show Sz1 (((Pol * X ^ (k : ℕ)) %ₘ Q).coeff j) (b * C) (e + C)
    rw [hMe]
    refine sz1_mono (sz1_sum _ _
      (fun n => (∑ i ∈ (Pol.coeff n).support, ((Pol.coeff n).coeff i).natAbs) * C)
      fun n hn => sz1_mul (sz1_mono (sz1_self _) le_rfl (he n)) (hC (n + k, j) ?_)) ?_ le_rfl
    · have := le_natDegree_of_mem_supp n hn
      exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 j.2⟩
    · rw [← Finset.sum_mul]
      exact Nat.mul_le_mul hlen le_rfl
  -- the determinant: length and degree
  have hdet : Sz1 M.det (d.factorial * (b * C) ^ d) (d * (e + C)) := by
    rw [Matrix.det_apply]
    refine sz1_mono (sz1_sum _ _ (fun _ => (b * C) ^ d) fun σ _ => ?_) (le_of_eq ?_) le_rfl
    · have hp := sz1_prod Finset.univ (fun i => M (σ i) i) (fun _ => b * C) (fun _ => e + C)
        fun i _ => hMsz _ _
      rw [Finset.prod_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul] at hp
      obtain h | h := Int.units_eq_one_or (Equiv.Perm.sign σ)
      · rw [h, one_smul]; exact hp
      · rw [h, Units.neg_smul, one_smul]; exact sz1_neg hp
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  -- `(1, ω₁, …, ω₁^(d-1))` is a left eigenvector of `ψ(M)`, with eigenvalue `Pol(ω, ω₁)`
  set v : Fin d → ℂ := fun j => ω₁ ^ (j : ℕ)
  have hvec : Matrix.vecMul v (M.map ψ) = eval₂ ψ ω₁ Pol • v := by
    funext k
    have h1 := eval₂_eq_sum_fin ψ ω₁ (d := d)
      (natDegree_modByMonic_lt (Pol * X ^ (k : ℕ)) hQm hQ1)
    rw [eval₂_modByMonic_eq_self_of_root hQroot, eval₂_mul, eval₂_X_pow] at h1
    show Matrix.vecMul v (M.map ψ) k = eval₂ ψ ω₁ Pol * ω₁ ^ (k : ℕ)
    rw [h1]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hP0 : Pol ≠ 0 := by rintro rfl; exact hPol (eval₂_zero _ _)
  have hb : 1 ≤ b := by
    show 0 < b
    refine lt_of_lt_of_le ?_ hlen
    refine Finset.sum_pos (fun k hk => ?_) (nonempty_support_iff.2 hP0)
    exact Finset.sum_pos (fun i hi => Int.natAbs_pos.2 (mem_support_iff.1 hi))
      (nonempty_support_iff.2 (mem_support_iff.1 hk))
  refine ⟨M.det, fun h0 => ?_, (length_le_of_sz1 hdet).trans ?_,
    (natDegree_le_of_sz1 hdet).trans ?_, ?_⟩
  · -- `P ≠ 0`
    obtain ⟨u, hu, hMu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : (M.map ψ).mulVec (ψ ∘ u) = 0 := funext fun i => by
      rw [← RingHom.map_mulVec, hMu, Pi.zero_apply, map_zero, Pi.zero_apply]
    have h2 := Matrix.dotProduct_mulVec v (M.map ψ) (ψ ∘ u)
    rw [h1, dotProduct_zero, hvec, smul_dotProduct, smul_eq_mul] at h2
    have hU : eval₂ ψ ω₁ (Polynomial.ofFn d u) = dotProduct v (ψ ∘ u) := by
      rw [eval₂_eq_sum_fin ψ ω₁ (ofFn_natDegree_lt hd0 u), dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [ofFn_coeff_eq_val_of_lt u j.2, mul_comm]; rfl
    rw [← hU] at h2
    have hU0 := hQmin _ (ofFn_natDegree_lt hd0 u) ((mul_eq_zero.1 h2.symm).resolve_left hPol)
    exact hu (injective_ofFn d (hU0.trans (map_zero _).symm))
  · -- the length
    calc d.factorial * (b * C) ^ d ≤ d.factorial ^ d * (b * C) ^ d :=
          Nat.mul_le_mul (Nat.le_self_pow hd0.ne' _) le_rfl
      _ = (d.factorial * C * b) ^ d := by ring
      _ ≤ (c * b) ^ d := Nat.pow_le_pow_left (Nat.mul_le_mul hcC le_rfl) _
  · -- the degree
    exact Nat.mul_le_mul le_rfl
      (Nat.add_le_add_left ((Nat.le_mul_of_pos_left C (Nat.factorial_pos d)).trans hcC) e)
  · -- the value
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((b * C : ℕ) : ℝ) * max 1 ‖ω‖ ^ (e + C) := ⟨_, rfl⟩
    have ht1 : 1 ≤ t := ht ▸ one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.mul_le_mul hb hC1) (one_le_pow₀ (le_max_left _ _))
    have hent : ∀ j k, ‖(M.map ψ) j k‖ ≤ t := fun j k => ht ▸ norm_aeval_le_of_sz1 (hMsz j k) ω
    have hadj : ∀ j, ‖(M.map ψ).adjugate j ⟨0, hd0⟩‖ ≤ d.factorial * t ^ d := by
      intro j
      rw [Matrix.adjugate_apply]
      refine norm_det_le _ _ fun i k => ?_
      rw [Matrix.updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]
        split_ifs
        · rw [norm_one]; exact ht1
        · rw [norm_zero]; exact zero_le_one.trans ht1
      · exact hent i k
    have hsum : ‖Matrix.vecMul v (M.map ψ).adjugate ⟨0, hd0⟩‖ ≤
        d * (max 1 ‖ω₁‖ ^ d * (d.factorial * t ^ d)) := by
      simp only [Matrix.vecMul, dotProduct]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖v j * (M.map ψ).adjugate j ⟨0, hd0⟩‖
          ≤ ∑ _j : Fin d, max 1 ‖ω₁‖ ^ d * (d.factorial * t ^ d) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul]
            refine mul_le_mul ?_ (hadj j) (norm_nonneg _)
              (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
            show ‖ω₁ ^ (j : ℕ)‖ ≤ _
            rw [norm_pow]
            exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
              (pow_le_pow_right₀ (le_max_left _ _) j.2.le)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show aeval ω M.det = (M.map ψ).det from RingHom.map_det ψ M,
      det_factor hd0 _ v _ hvec (pow_zero ω₁), norm_mul]
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ d * d.factorial := by
      exact_mod_cast Nat.mul_pos hd0 (Nat.factorial_pos d)
    have ht0 : 0 ≤ max 1 ‖ω₁‖ * t := mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans ht1)
    calc (d : ℝ) * (max 1 ‖ω₁‖ ^ d * (d.factorial * t ^ d))
        = (d * d.factorial : ℝ) * (max 1 ‖ω₁‖ * t) ^ d := by ring
      _ ≤ (d * d.factorial : ℝ) ^ d * (max 1 ‖ω₁‖ * t) ^ d :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ h1 hd0.ne') (pow_nonneg ht0 _)
      _ = ((d * d.factorial : ℝ) * max 1 ‖ω₁‖ * (C * max 1 ‖ω‖ ^ C) *
            (b * max 1 ‖ω‖ ^ e)) ^ d := by
          rw [ht]; push_cast; ring
      _ ≤ (((c * b : ℕ) : ℝ) * max 1 ‖ω‖ ^ e) ^ d := by
          refine pow_le_pow_left₀ (by positivity) ?_ d
          rw [Nat.cast_mul, mul_assoc (c : ℝ)]
          exact mul_le_mul_of_nonneg_right hcK (by positivity)

#print axioms solution
