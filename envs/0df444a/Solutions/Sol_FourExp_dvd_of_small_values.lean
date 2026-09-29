-- Prove2me | solution 1 for FourExp.dvd_of_small_values
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T07:05:49.508596+00:00
-- url     : https://prove2.me/submissions/34c4fce2-9043-4c82-ae43-7a4168acf7ea

import Mathlib

open Polynomial Finset

namespace FourExpRes

/-- Leibniz bound: `|det A| ≤ N! · ∏ⱼ cⱼ` when column `j` is bounded by `cⱼ`. -/
lemma abs_det_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (c : Fin N → ℝ)
    (hc : ∀ i j, |(A i j : ℝ)| ≤ c j) :
    |((A.det : ℤ) : ℝ)| ≤ (N.factorial : ℝ) * ∏ j, c j := by
  have hdet : ((A.det : ℤ) : ℝ) =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (A (σ i) i : ℝ) := by
    rw [Matrix.det_apply]
    simp only [Int.cast_sum, Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_prod]
  rw [hdet]
  calc |∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (A (σ i) i : ℝ)|
      ≤ ∑ σ : Equiv.Perm (Fin N), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (A (σ i) i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∏ j, c j := by
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul, Finset.abs_prod]
        have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hs, one_mul]
        exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hc (σ i) i)
    _ = (N.factorial : ℝ) * ∏ j, c j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma factorial_le_pow_pred (n : ℕ) (hn : 1 ≤ n) : n.factorial ≤ n ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Nat.factorial_succ, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    have h1 : n ^ (n - 1) ≤ (n + 1) ^ (n - 1) := Nat.pow_le_pow_left (by omega) _
    have h2 : n.factorial ≤ (n + 1) ^ (n - 1) := ih.trans h1
    nlinarith [Nat.zero_le (n.factorial)]

end FourExpRes

theorem solution
    (P Q : Polynomial ℤ) (hQ : Irreducible Q) (α : ℂ) (H h : ℝ) (hH : 1 ≤ H) (hh : 1 ≤ h)
    (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H) (hQh : ∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ h)
    (hsmall : ((1 + ‖α‖) * ((P.natDegree + Q.natDegree : ℕ) : ℝ)) ^ (P.natDegree + Q.natDegree)
        * H ^ Q.natDegree * h ^ P.natDegree
        * (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) < 1) :
    Q ∣ P := by
  classical
  by_contra hndvd
  have hα0 : 0 ≤ ‖α‖ := norm_nonneg α
  -- the constant case: `|Q(α)| ≥ 2` contradicts the hypothesis
  by_cases hδ0 : Q.natDegree = 0
  · have hQC := eq_C_of_natDegree_eq_zero hδ0
    have hc0 : Q.coeff 0 ≠ 0 := by
      intro h0; apply hQ.ne_zero; rw [hQC, h0, map_zero]
    have hcu : ¬ IsUnit (Q.coeff 0) := fun hu => hQ.not_isUnit (by rw [hQC]; exact isUnit_C.mpr hu)
    have hc2 : (2 : ℤ) ≤ |Q.coeff 0| := by
      have h1 : |Q.coeff 0| ≠ 0 := abs_ne_zero.mpr hc0
      have h2 : |Q.coeff 0| ≠ 1 := fun h => hcu (Int.isUnit_iff_abs_eq.mpr h)
      have := abs_nonneg (Q.coeff 0)
      omega
    have hQα : (2 : ℝ) ≤ ‖Polynomial.aeval α Q‖ := by
      rw [hQC, aeval_C, algebraMap_int_eq, eq_intCast, Complex.norm_intCast]
      exact_mod_cast hc2
    have hf1 : (1 : ℝ) ≤ ((1 + ‖α‖) * ((P.natDegree + Q.natDegree : ℕ) : ℝ)) ^ (P.natDegree + Q.natDegree) := by
      rcases Nat.eq_zero_or_pos (P.natDegree + Q.natDegree) with h0 | hpos
      · rw [h0, pow_zero]
      · apply one_le_pow₀
        have : (1 : ℝ) ≤ ((P.natDegree + Q.natDegree : ℕ) : ℝ) := by exact_mod_cast hpos
        nlinarith
    have hh1 : (1 : ℝ) ≤ h ^ P.natDegree := one_le_pow₀ hh
    rw [hδ0, pow_zero, mul_one] at hsmall
    have hS : (2 : ℝ) ≤ ‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖ := by
      linarith [norm_nonneg (Polynomial.aeval α P)]
    have hlow : (2 : ℝ) ≤ ((1 + ‖α‖) * ((P.natDegree + 0 : ℕ) : ℝ)) ^ (P.natDegree + 0)
        * h ^ P.natDegree * (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) := by
      rw [hδ0] at hf1
      have h12 : (1 : ℝ) ≤ ((1 + ‖α‖) * ((P.natDegree + 0 : ℕ) : ℝ)) ^ (P.natDegree + 0)
          * h ^ P.natDegree := by nlinarith
      nlinarith
    linarith
  -- the non-constant case: a non-zero integer resultant
  set d := P.natDegree with hd
  set δ := Q.natDegree with hδ
  have hδpos : 0 < δ := Nat.pos_of_ne_zero hδ0
  have hNpos : 0 < d + δ := by omega
  have hprim : Q.IsPrimitive := hQ.isPrimitive hδ0
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφ
  have hinj : Function.Injective φ := Int.cast_injective
  have hQ'irr : Irreducible (Q.map φ) := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ
  have hndvd' : ¬ Q.map φ ∣ P.map φ :=
    fun hdiv => hndvd ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q P hprim).mpr hdiv)
  have hcop : IsCoprime (P.map φ) (Q.map φ) := ((hQ'irr.coprime_iff_not_dvd).mpr hndvd').symm
  have hres' := resultant_ne_zero (P.map φ) (Q.map φ) hcop
  have hPdeg : (P.map φ).natDegree = d := natDegree_map_eq_of_injective hinj P
  have hQdeg : (Q.map φ).natDegree = δ := natDegree_map_eq_of_injective hinj Q
  have hresZ : P.resultant Q d δ ≠ 0 := by
    intro h0
    apply hres'
    rw [hPdeg, hQdeg, resultant_map_map, h0, map_zero]
  have hRes1 : (1 : ℝ) ≤ |((P.resultant Q d δ : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hresZ
  -- the Bézout identity `P·A + Q·B = Res`, read off the adjugate of the Sylvester matrix
  set N : ℕ := d + δ with hNdef
  have hv : (1 : ℤ[X]) ∈ degreeLT ℤ N := by
    rw [mem_degreeLT, degree_one]; exact_mod_cast hNpos
  set v : degreeLT ℤ N := ⟨1, hv⟩ with hvdef
  set X := adjSylvester (m := d) (n := δ) P Q v with hXdef
  have hX : P * (X.2 : ℤ[X]) + Q * (X.1 : ℤ[X]) = C (P.resultant Q d δ) := by
    have := congr(($(sylveserMap_comp_adjSylvester P Q (le_refl d) (le_refl δ)) v).1)
    simpa [Algebra.smul_def, hvdef] using this
  set A := P.sylvester Q d δ with hAdef
  -- column bounds for the Sylvester matrix
  set c : Fin N → ℝ := fun j => Fin.addCases (fun _ => h) (fun _ => H) j with hcdef
  have hc1 : ∀ s, 1 ≤ c s := by
    intro s
    refine Fin.addCases (fun s₁ => ?_) (fun s₁ => ?_) s
    · simp only [hcdef, Fin.addCases_left]; exact hh
    · simp only [hcdef, Fin.addCases_right]; exact hH
  have hcol : ∀ i j, |(A i j : ℝ)| ≤ c j := by
    intro i j
    refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j
    · simp only [hAdef, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, hcdef]
      split_ifs
      · exact hQh _
      · simp; linarith
    · simp only [hAdef, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, hcdef]
      split_ifs
      · exact hPH _
      · simp; linarith
  have hprod : ∏ j, c j = h ^ d * H ^ δ := by
    rw [Fin.prod_univ_add]
    simp [hcdef]
  set B : ℝ := (N.factorial : ℝ) * (h ^ d * H ^ δ) with hBdef
  have hadj : ∀ i j, |(A.adjugate i j : ℝ)| ≤ B := by
    intro i j
    rw [Matrix.adjugate_apply]
    have hb := FourExpRes.abs_det_le (A.updateRow j (Pi.single i 1)) c (by
      intro r t
      by_cases hr : r = j
      · subst hr
        rw [Matrix.updateRow_self]
        by_cases ht : t = i
        · subst ht; simp; exact hc1 _
        · simp [Pi.single_apply, ht]; linarith [hc1 t]
      · rw [Matrix.updateRow_ne hr]; exact hcol r t)
    rwa [hprod] at hb
  -- coordinates of `X` are entries of the adjugate
  have hrepr : ∀ j, (((degreeLT.basis ℤ d).prod (degreeLT.basis ℤ δ)).reindex finSumFinEquiv).repr X j
      = A.adjugate j ⟨0, hNpos⟩ := by
    intro j
    rw [hXdef, adjSylvester, Matrix.toLin_apply, Module.Basis.repr_sum_self]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single ⟨0, hNpos⟩]
    · simp [hvdef, hAdef]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h0 => hb (Fin.ext h0)
      simp [hvdef, coeff_one, this]
    · simp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hadj ⟨0, hNpos⟩ ⟨0, hNpos⟩)
  have hX1 : ∀ k, |((X.1 : ℤ[X]).coeff k : ℝ)| ≤ B := by
    intro k
    by_cases hk : k < d
    · have := hrepr (Fin.castAdd δ ⟨k, hk⟩)
      simp only [Module.Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl,
        degreeLT.basis_repr] at this
      rw [this]; exact hadj _ _
    · have hdeg : (X.1 : ℤ[X]).degree < d := mem_degreeLT.mp X.1.2
      rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.mp hk))]
      simpa using hB0
  have hX2 : ∀ k, |((X.2 : ℤ[X]).coeff k : ℝ)| ≤ B := by
    intro k
    by_cases hk : k < δ
    · have := hrepr (Fin.natAdd d ⟨k, hk⟩)
      simp only [Module.Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_repr_inr,
        degreeLT.basis_repr] at this
      rw [this]; exact hadj _ _
    · have hdeg : (X.2 : ℤ[X]).degree < δ := mem_degreeLT.mp X.2.2
      rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.mp hk))]
      simpa using hB0
  -- a polynomial of degree below `n ≤ N` with coefficients at most `B` is small at `α`
  have heval : ∀ (p : ℤ[X]) (n : ℕ), n ≤ N → p.degree < n → (∀ k, |(p.coeff k : ℝ)| ≤ B) →
      ‖Polynomial.aeval α p‖ ≤ N * B * (1 + ‖α‖) ^ N := by
    intro p n hn hp hB
    by_cases hp0 : p = 0
    · subst hp0; simp only [map_zero, norm_zero]; positivity
    have hnat : p.natDegree < N :=
      lt_of_lt_of_le ((natDegree_lt_iff_degree_lt hp0).mpr hp) hn
    rw [aeval_eq_sum_range' hnat]
    calc ‖∑ i ∈ Finset.range N, p.coeff i • α ^ i‖
        ≤ ∑ i ∈ Finset.range N, ‖p.coeff i • α ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range N, B * (1 + ‖α‖) ^ N := by
          apply Finset.sum_le_sum
          intro i hi
          rw [zsmul_eq_mul, norm_mul, norm_pow, Complex.norm_intCast]
          have h1 : ‖α‖ ^ i ≤ (1 + ‖α‖) ^ N :=
            (pow_le_pow_left₀ hα0 (by linarith) i).trans
              (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le)
          exact mul_le_mul (hB i) h1 (by positivity) hB0
      _ = N * B * (1 + ‖α‖) ^ N := by simp [Finset.sum_const]; ring
  have hA1 := heval (X.1 : ℤ[X]) d (by omega) (mem_degreeLT.mp X.1.2) hX1
  have hA2 := heval (X.2 : ℤ[X]) δ (by omega) (mem_degreeLT.mp X.2.2) hX2
  -- evaluate the identity at `α`
  have hev : ((P.resultant Q d δ : ℤ) : ℂ)
      = Polynomial.aeval α P * Polynomial.aeval α (X.2 : ℤ[X])
        + Polynomial.aeval α Q * Polynomial.aeval α (X.1 : ℤ[X]) := by
    have := congrArg (Polynomial.aeval α) hX
    simp only [map_add, map_mul, aeval_C, algebraMap_int_eq, eq_intCast, map_intCast] at this
    exact this.symm
  have hRnorm : (1 : ℝ) ≤ ‖((P.resultant Q d δ : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]; exact hRes1
  set K : ℝ := N * B * (1 + ‖α‖) ^ N with hKdef
  have hup : ‖((P.resultant Q d δ : ℤ) : ℂ)‖
      ≤ (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) * K := by
    rw [hev]
    calc ‖Polynomial.aeval α P * Polynomial.aeval α (X.2 : ℤ[X])
          + Polynomial.aeval α Q * Polynomial.aeval α (X.1 : ℤ[X])‖
        ≤ ‖Polynomial.aeval α P‖ * ‖Polynomial.aeval α (X.2 : ℤ[X])‖
          + ‖Polynomial.aeval α Q‖ * ‖Polynomial.aeval α (X.1 : ℤ[X])‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖Polynomial.aeval α P‖ * K + ‖Polynomial.aeval α Q‖ * K := by
          gcongr
      _ = (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) * K := by ring
  -- `K ≤ ((1 + |α|) N)^N · H^δ · h^d`
  have hNfac : (N : ℝ) * (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
    have h1 := FourExpRes.factorial_le_pow_pred N (by omega)
    have h2 : N * N.factorial ≤ N * N ^ (N - 1) := Nat.mul_le_mul_left _ h1
    have h3 : N * N ^ (N - 1) = N ^ N := by
      rw [← pow_succ']; congr 1; omega
    exact_mod_cast h2.trans h3.le
  have hK : K ≤ ((1 + ‖α‖) * ((N : ℕ) : ℝ)) ^ N * H ^ δ * h ^ d := by
    rw [hKdef, hBdef, mul_pow]
    have hpos : 0 ≤ h ^ d * H ^ δ * (1 + ‖α‖) ^ N := by positivity
    calc (N : ℝ) * ((N.factorial : ℝ) * (h ^ d * H ^ δ)) * (1 + ‖α‖) ^ N
        = ((N : ℝ) * (N.factorial : ℝ)) * (h ^ d * H ^ δ * (1 + ‖α‖) ^ N) := by ring
      _ ≤ (N : ℝ) ^ N * (h ^ d * H ^ δ * (1 + ‖α‖) ^ N) := mul_le_mul_of_nonneg_right hNfac hpos
      _ = (1 + ‖α‖) ^ N * ((N : ℕ) : ℝ) ^ N * H ^ δ * h ^ d := by ring
  have hS0 : 0 ≤ ‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖ := by positivity
  have := mul_le_mul_of_nonneg_left hK hS0
  have hfinal : (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) * K
      ≤ ((1 + ‖α‖) * ((N : ℕ) : ℝ)) ^ N * H ^ δ * h ^ d
        * (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) := by
    calc _ ≤ (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖)
            * (((1 + ‖α‖) * ((N : ℕ) : ℝ)) ^ N * H ^ δ * h ^ d) := this
      _ = _ := by ring
  linarith
