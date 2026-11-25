-- Prove2me | solution 1 for DetDLP.lemma_4_2_newton_binomial_filter
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T09:57:24.875268+00:00
-- url     : https://prove2.me/submissions/fa4080de-3090-4e1e-86b4-aa6a39e3edf4

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

open DetDLP

private lemma filterPoly_nonneg (w Mlab : ℕ) (d : ℤ) :
    0 ≤ (filterPoly w Mlab).eval d := by
  unfold filterPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_nonneg fun j _ => by
    rw [Polynomial.eval_pow]
    exact sq_nonneg _

private lemma filterPoly_eval_eq_zero_iff (w Mlab : ℕ) (hw : 4 ≤ w) (hM : 2 ≤ Mlab)
    (d : ℤ) (hlo : -((w : ℤ) * ((Mlab : ℤ) - 1)) ≤ d)
    (hhi : d ≤ (w : ℤ) * ((Mlab : ℤ) - 1)) :
    (filterPoly w Mlab).eval d = 0 ↔ d ≡ 1 [ZMOD (Mlab : ℤ)] := by
  unfold filterPoly
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, _, hj⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sq_eq_zero_iff, sub_eq_zero] at hj
    rw [Int.modEq_iff_dvd]
    refine ⟨-j, ?_⟩
    linarith
  · intro hmod
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hmod
    refine ⟨-k, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have hMpos : (0 : ℤ) < Mlab := by omega
      have hdk : d = 1 + (-k) * (Mlab : ℤ) := by linarith
      constructor
      · by_contra hlt
        push Not at hlt
        have hle : (-k) ≤ -(w : ℤ) - 1 := by omega
        have hmul : (-k) * (Mlab : ℤ) ≤ (-(w : ℤ) - 1) * (Mlab : ℤ) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hMpos)
        nlinarith
      · by_contra hlt
        push Not at hlt
        have hge : (w : ℤ) + 1 ≤ -k := by omega
        have hmul : ((w : ℤ) + 1) * (Mlab : ℤ) ≤ (-k) * (Mlab : ℤ) :=
          mul_le_mul_of_nonneg_right hge (le_of_lt hMpos)
        nlinarith
    · simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sq_eq_zero_iff]
      linarith

private lemma filterPoly_natDegree_le (w Mlab : ℕ) :
    (filterPoly w Mlab).natDegree ≤ dFilt w := by
  unfold filterPoly dFilt
  calc (∏ j ∈ Finset.Icc (-(w : ℤ)) (w : ℤ),
          (Polynomial.X - Polynomial.C (1 + j * (Mlab : ℤ))) ^ 2).natDegree
      ≤ ∑ j ∈ Finset.Icc (-(w : ℤ)) (w : ℤ),
          ((Polynomial.X - Polynomial.C (1 + j * (Mlab : ℤ))) ^ 2).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc (-(w : ℤ)) (w : ℤ), 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ((Polynomial.X - Polynomial.C (1 + j * (Mlab : ℤ))) ^ 2).natDegree
            ≤ 2 * (Polynomial.X - Polynomial.C (1 + j * (Mlab : ℤ))).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ 2 * 1 := by
              gcongr
              exact Polynomial.natDegree_X_sub_C_le _
          _ = 2 := by norm_num
    _ = (Finset.Icc (-(w : ℤ)) (w : ℤ)).card * 2 := by simp
    _ = 4 * w + 2 := by
        rw [Int.card_Icc]
        omega

private lemma newton_expansion_nat (P : Polynomial ℤ) (D : ℕ) (k : ℕ) (hk : k ≤ D) :
    ∑ j ∈ Finset.range (D + 1),
      (∑ t ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - t) * (Nat.choose j t : ℤ) * P.eval (t : ℤ)) *
        (Nat.choose k j : ℤ) = P.eval (k : ℤ) := by
  have hsplit :
      ∑ j ∈ Finset.range (D + 1),
        (∑ t ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - t) * (Nat.choose j t : ℤ) * P.eval (t : ℤ)) *
          (Nat.choose k j : ℤ) =
      ∑ j ∈ Finset.range (k + 1),
        (∑ t ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - t) * (Nat.choose j t : ℤ) * P.eval (t : ℤ)) *
          (Nat.choose k j : ℤ) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    have hkj : k < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hkj]
  rw [hsplit]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma']
  let S := (Finset.range (k + 1)).sigma (fun j => Finset.range (j + 1))
  let T := (Finset.range (k + 1)).sigma (fun t => Finset.range (k - t + 1))
  have hbij :
      ∑ x ∈ S, (-1 : ℤ) ^ (x.1 - x.2) * (Nat.choose x.1 x.2 : ℤ) * P.eval (x.2 : ℤ) *
        (Nat.choose k x.1 : ℤ) =
      ∑ y ∈ T, P.eval (y.1 : ℤ) * (Nat.choose k y.1 : ℤ) *
        ((-1 : ℤ) ^ y.2 * (Nat.choose (k - y.1) y.2 : ℤ)) := by
    refine Finset.sum_nbij (fun x => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [S, T, Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · intro x₁ hx₁ x₂ hx₂ heq
      cases x₁ with | mk j₁ t₁ =>
      cases x₂ with | mk j₂ t₂ =>
      simp only [S, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨rfl, hd⟩ := heq
      have hj : j₁ = j₂ := by omega
      subst hj
      rfl
    · intro y hy
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hy
      refine ⟨⟨y.1 + y.2, y.1⟩, ?_, ?_⟩
      · simp only [S, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]
        omega
      · ext <;> simp
    · intro x hx
      simp only [S, Finset.mem_sigma, Finset.mem_range] at hx
      have hch : Nat.choose k x.1 * Nat.choose x.1 x.2 =
          Nat.choose k x.2 * Nat.choose (k - x.2) (x.1 - x.2) :=
        Nat.choose_mul (n := k) (k := x.1) (s := x.2) (by omega)
      have hchZ : (Nat.choose k x.1 : ℤ) * (Nat.choose x.1 x.2 : ℤ) =
          (Nat.choose k x.2 : ℤ) * (Nat.choose (k - x.2) (x.1 - x.2) : ℤ) := by
        exact_mod_cast hch
      calc (-1 : ℤ) ^ (x.1 - x.2) * (Nat.choose x.1 x.2 : ℤ) * P.eval (x.2 : ℤ) *
              (Nat.choose k x.1 : ℤ)
          = P.eval (x.2 : ℤ) * ((Nat.choose k x.1 : ℤ) * (Nat.choose x.1 x.2 : ℤ)) *
              (-1 : ℤ) ^ (x.1 - x.2) := by ring
        _ = P.eval (x.2 : ℤ) * ((Nat.choose k x.2 : ℤ) * (Nat.choose (k - x.2) (x.1 - x.2) : ℤ)) *
              (-1 : ℤ) ^ (x.1 - x.2) := by rw [hchZ]
        _ = P.eval (x.2 : ℤ) * (Nat.choose k x.2 : ℤ) *
              ((-1 : ℤ) ^ (x.1 - x.2) * (Nat.choose (k - x.2) (x.1 - x.2) : ℤ)) := by ring
  rw [hbij]
  change ∑ y ∈ (Finset.range (k + 1)).sigma (fun t => Finset.range (k - t + 1)), _ = _
  rw [Finset.sum_sigma]
  have hinner : ∀ t ∈ Finset.range (k + 1),
      (∑ r ∈ Finset.range (k - t + 1),
        P.eval (t : ℤ) * (Nat.choose k t : ℤ) * ((-1 : ℤ) ^ r * (Nat.choose (k - t) r : ℤ))) =
      if t = k then P.eval (k : ℤ) else 0 := by
    intro t ht
    rw [← Finset.mul_sum]
    have halt : ∑ r ∈ Finset.range (k - t + 1), (-1 : ℤ) ^ r * (Nat.choose (k - t) r : ℤ) =
        if k - t = 0 then 1 else 0 := Int.alternating_sum_range_choose
    rw [halt]
    simp only [Finset.mem_range] at ht
    by_cases htk : t = k
    · subst htk
      simp
    · have hne : k - t ≠ 0 := by omega
      simp [htk, hne]
  rw [Finset.sum_congr rfl hinner]
  simp

private lemma filterPoly_newton_expansion (w Mlab : ℕ) (d : ℤ) :
    (filterPoly w Mlab).eval d =
      ∑ j ∈ Finset.range (dFilt w + 1), newtonCoeff w Mlab j * intBinom d j := by
  let D := dFilt w
  let P := filterPoly w Mlab
  let Pq : Polynomial ℚ := P.map (Int.castRingHom ℚ)
  let Rq : Polynomial ℚ :=
    ∑ j ∈ Finset.range (D + 1),
      Polynomial.C ((newtonCoeff w Mlab j : ℚ) / (j.factorial : ℚ)) *
        (descPochhammer ℤ j).map (Int.castRingHom ℚ)
  have hdegP : Pq.natDegree ≤ D := by
    calc Pq.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
      _ ≤ D := filterPoly_natDegree_le w Mlab
  have hdegR : Rq.natDegree ≤ D := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun j hj => ?_⟩
    simp only [Finset.mem_range] at hj
    calc (Polynomial.C ((newtonCoeff w Mlab j : ℚ) / (j.factorial : ℚ)) *
            (descPochhammer ℤ j).map (Int.castRingHom ℚ)).natDegree
        ≤ ((descPochhammer ℤ j).map (Int.castRingHom ℚ)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ (descPochhammer ℤ j).natDegree := Polynomial.natDegree_map_le
      _ = j := descPochhammer_natDegree ℤ j
      _ ≤ D := by omega
  have heval_Rq : ∀ z : ℤ,
      Rq.eval (z : ℚ) =
        ((∑ j ∈ Finset.range (D + 1), newtonCoeff w Mlab j * intBinom z j : ℤ) : ℚ) := by
    intro z
    simp only [Rq, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsm : ((descPochhammer ℤ j).map (Int.castRingHom ℚ)).eval (z : ℚ) =
        ((j.factorial : ℚ) * (intBinom z j : ℚ)) := by
      have h1 : ((descPochhammer ℤ j).map (Int.castRingHom ℚ)).eval (z : ℚ) =
          (((descPochhammer ℤ j).eval z : ℤ) : ℚ) := by
        simp
      rw [h1]
      have h2 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) z j
      rw [← Polynomial.eval_eq_smeval] at h2
      have h3 : (descPochhammer ℤ j).eval z = (j.factorial : ℤ) * intBinom z j := by
        simpa [intBinom, nsmul_eq_mul] using h2
      rw [h3]
      push_cast
      ring
    rw [hsm]
    have hfac : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    field_simp [hfac]
  have hagree : ∀ k : ℕ, k ≤ D → Pq.eval (k : ℚ) = Rq.eval (k : ℚ) := by
    intro k hk
    rw [show (k : ℚ) = ((k : ℤ) : ℚ) by norm_cast, heval_Rq (k : ℤ)]
    have hPq : Pq.eval ((k : ℤ) : ℚ) = ((P.eval (k : ℤ) : ℤ) : ℚ) := by
      simp [Pq, Polynomial.eval_map]
    rw [hPq]
    norm_cast
    have hch : ∀ j, intBinom (k : ℤ) j = (Nat.choose k j : ℤ) := by
      intro j
      unfold intBinom
      simpa using Ring.choose_natCast (R := ℤ) k j
    simp_rw [hch, newtonCoeff]
    exact (newton_expansion_nat P D k hk).symm
  have hdiff_eq_zero : Pq - Rq = 0 := by
    by_contra hne
    have hdeg_diff : (Pq - Rq).natDegree ≤ D :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le hdegP hdegR)
    have hroots : ∀ k ∈ Finset.range (D + 1), (k : ℚ) ∈ (Pq - Rq).roots := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub,
        hagree k (by omega), sub_self]
    have hcard : D + 1 ≤ (Pq - Rq).roots.card := by
      have hinj : Function.Injective (fun k : ℕ => (k : ℚ)) := Nat.cast_injective
      have hsub : ((Finset.range (D + 1)).image (fun k : ℕ => (k : ℚ))).val ⊆ (Pq - Rq).roots := by
        intro q hq
        rw [Finset.mem_val, Finset.mem_image] at hq
        obtain ⟨k, hk, rfl⟩ := hq
        exact hroots k hk
      have hnodup : ((Finset.range (D + 1)).image (fun k : ℕ => (k : ℚ))).val.Nodup :=
        Finset.nodup _
      calc D + 1 = (Finset.range (D + 1)).card := (Finset.card_range _).symm
        _ = ((Finset.range (D + 1)).image (fun k : ℕ => (k : ℚ))).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ = ((Finset.range (D + 1)).image (fun k : ℕ => (k : ℚ))).val.card := rfl
        _ ≤ (Pq - Rq).roots.card := Multiset.card_le_card (Multiset.le_iff_subset hnodup |>.mpr hsub)
    have hle := Polynomial.card_roots' (Pq - Rq)
    omega
  have hPR : Pq = Rq := sub_eq_zero.mp hdiff_eq_zero
  have hev : Pq.eval (d : ℚ) = Rq.eval (d : ℚ) := by rw [hPR]
  rw [heval_Rq d] at hev
  have hPd : Pq.eval (d : ℚ) = ((P.eval d : ℤ) : ℚ) := by
    simp [Pq, Polynomial.eval_map]
  rw [hPd] at hev
  exact_mod_cast hev

private lemma truncPoly_binom_mul (P0 ℓ : ℕ) (a b : ℤ) :
    (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})
      (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom a j.val : ℤ) : ZMod (2 ^ P0)))) *
    (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})
      (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom b j.val : ℤ) : ZMod (2 ^ P0)))) =
    (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})
      (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom (a + b) j.val : ℤ) : ZMod (2 ^ P0)))) := by
  let I := Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ}
  let pA : Polynomial (ZMod (2 ^ P0)) :=
    ∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom a j.val : ℤ) : ZMod (2 ^ P0))
  let pB : Polynomial (ZMod (2 ^ P0)) :=
    ∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom b j.val : ℤ) : ZMod (2 ^ P0))
  let pAB : Polynomial (ZMod (2 ^ P0)) :=
    ∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom (a + b) j.val : ℤ) : ZMod (2 ^ P0))
  change Ideal.Quotient.mk I pA * Ideal.Quotient.mk I pB = Ideal.Quotient.mk I pAB
  rw [← map_mul, Ideal.Quotient.eq]
  rw [Ideal.mem_span_singleton]
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub]
  have hcoeff_fin : ∀ (x : ℤ) (r : ℕ),
      (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom x j.val : ℤ) : ZMod (2 ^ P0))).coeff r =
        if r < ℓ then ((intBinom x r : ℤ) : ZMod (2 ^ P0)) else 0 := by
    intro x r
    rw [Polynomial.finsetSum_coeff]
    by_cases hr : r < ℓ
    · rw [if_pos hr]
      rw [Finset.sum_eq_single ⟨r, hr⟩]
      · simp
      · intro j _ hj
        have hne : j.val ≠ r := fun h => hj (Fin.ext h)
        simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : j.val ≠ r := fun h => hr (h ▸ j.isLt)
      simp [Polynomial.coeff_monomial, hne]
  have hpAB : pAB.coeff k = ((intBinom (a + b) k : ℤ) : ZMod (2 ^ P0)) := by
    simpa [pAB, hk] using hcoeff_fin (a + b) k
  rw [Polynomial.coeff_mul, hpAB]
  have hsum : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, pA.coeff x.1 * pB.coeff x.2 =
      ((intBinom (a + b) k : ℤ) : ZMod (2 ^ P0)) := by
    have hcv : intBinom (a + b) k =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, intBinom a x.1 * intBinom b x.2 :=
      Ring.add_choose_eq k (Commute.all a b)
    rw [hcv]
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxsum : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hx1 : x.1 < ℓ := by omega
    have hx2 : x.2 < ℓ := by omega
    simp [pA, pB, hcoeff_fin, hx1, hx2]
  rw [hsum, sub_self]

private lemma truncPoly_binom_prod {n : ℕ} (P0 ℓ : ℕ) (f : Fin n → ℤ) :
    (∏ t : Fin n,
      (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})
        (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom (f t) j.val : ℤ) : ZMod (2 ^ P0))) :
        TruncPoly P0 ℓ)) =
    (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})
      (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom (∑ t : Fin n, f t) j.val : ℤ) : ZMod (2 ^ P0)))) := by
  let I := Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ}
  let g : ℤ → TruncPoly P0 ℓ := fun x =>
    Ideal.Quotient.mk I (∑ j : Fin ℓ, Polynomial.monomial j.val ((intBinom x j.val : ℤ) : ZMod (2 ^ P0)))
  change ∏ t : Fin n, g (f t) = g (∑ t : Fin n, f t)
  have hg0 : g 0 = 1 := by
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have h1 : (1 : Polynomial (ZMod (2 ^ P0))) ∈ I := by
        simp [I]
      have hsub : Subsingleton (TruncPoly P0 0) := by
        rw [Ideal.Quotient.subsingleton_iff]
        exact Ideal.eq_top_of_isUnit_mem I h1 isUnit_one
      exact Subsingleton.elim _ _
    · have h0lt : 0 < ℓ := Nat.pos_of_ne_zero hℓ
      change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I 1
      congr 1
      rw [Finset.sum_eq_single ⟨0, h0lt⟩]
      · simp [intBinom]
      · intro j _ hj
        have hpos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        have hz : intBinom 0 j.val = 0 := Ring.choose_zero_pos ℤ hpos
        simp [hz]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hgadd : ∀ a b : ℤ, g a * g b = g (a + b) := truncPoly_binom_mul P0 ℓ
  have hfin : ∀ s : Finset (Fin n), ∏ t ∈ s, g (f t) = g (∑ t ∈ s, f t) := by
    intro s
    classical
    induction s using Finset.induction with
    | empty => simp [hg0]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, hgadd]
  exact hfin Finset.univ

theorem solution :
    ∀ (w Mlab : ℕ), 4 ≤ w → 2 ≤ Mlab →
      (∀ d : ℤ, 0 ≤ (filterPoly w Mlab).eval d) ∧
      (∀ d : ℤ, -((w : ℤ) * ((Mlab : ℤ) - 1)) ≤ d → d ≤ (w : ℤ) * ((Mlab : ℤ) - 1) →
        ((filterPoly w Mlab).eval d = 0 ↔ d ≡ 1 [ZMOD (Mlab : ℤ)])) ∧
      (∀ d : ℤ, (filterPoly w Mlab).eval d =
        ∑ j ∈ Finset.range (dFilt w + 1), newtonCoeff w Mlab j * intBinom d j) ∧
      (∀ (P0 : ℕ) [NeZero (2 ^ P0)] {ι : Type} [Fintype ι]
        (y : ι → Fin (2 * w) → ℤ) (ς : Fin (2 * w) → ℤ),
        1 ≤ P0 →
        (∀ t : Fin (2 * w), ς t = 1 ∨ ς t = -1) →
        let ℓ := dFilt w + 1
        let d : ι → ℤ := fun u => ∑ t : Fin (2 * w), ς t * y u t
        let ZQ : ℤ := ∑ u : ι, (filterPoly w Mlab).eval (d u)
        ZQ < (2 ^ P0 : ℤ) →
        ∀ Z : Fin ℓ → ZMod (2 ^ P0),
          (Ideal.Quotient.mk _ (∑ j : Fin ℓ, Polynomial.monomial j.val (Z j)) : TruncPoly P0 ℓ) =
            ∑ u : ι, ∏ t : Fin (2 * w),
              (Ideal.Quotient.mk _ (∑ j : Fin ℓ,
                Polynomial.monomial j.val ((intBinom (ς t * y u t) j.val : ℤ) : ZMod (2 ^ P0))) :
                TruncPoly P0 ℓ) →
          ((∑ j : Fin ℓ, (newtonCoeff w Mlab j.val : ZMod (2 ^ P0)) * Z j).val : ℤ) = ZQ) := by
  intro w Mlab hw hM
  refine ⟨filterPoly_nonneg w Mlab, filterPoly_eval_eq_zero_iff w Mlab hw hM,
    filterPoly_newton_expansion w Mlab, ?_⟩
  intro P0 _ ι _ y ς _ _
  dsimp only
  intro hZQlt Z hZeq
  let ℓ := dFilt w + 1
  let d : ι → ℤ := fun u => ∑ t : Fin (2 * w), ς t * y u t
  let ZQ : ℤ := ∑ u : ι, (filterPoly w Mlab).eval (d u)
  let I := Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ}
  have hrhs :
      (∑ u : ι, ∏ t : Fin (2 * w),
        (Ideal.Quotient.mk I (∑ j : Fin ℓ,
          Polynomial.monomial j.val ((intBinom (ς t * y u t) j.val : ℤ) : ZMod (2 ^ P0))) :
          TruncPoly P0 ℓ)) =
      Ideal.Quotient.mk I (∑ j : Fin ℓ, Polynomial.monomial j.val
        (∑ u : ι, ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0)))) := by
    have hstep1 : ∀ u : ι,
        (∏ t : Fin (2 * w),
          (Ideal.Quotient.mk I (∑ j : Fin ℓ,
            Polynomial.monomial j.val ((intBinom (ς t * y u t) j.val : ℤ) : ZMod (2 ^ P0))) :
            TruncPoly P0 ℓ)) =
        Ideal.Quotient.mk I (∑ j : Fin ℓ,
          Polynomial.monomial j.val ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0))) := by
      intro u
      exact truncPoly_binom_prod P0 ℓ (fun t => ς t * y u t)
    simp_rw [hstep1, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_sum]
  have hqeq :
      Ideal.Quotient.mk I (∑ j : Fin ℓ, Polynomial.monomial j.val (Z j)) =
      Ideal.Quotient.mk I (∑ j : Fin ℓ, Polynomial.monomial j.val
        (∑ u : ι, ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0)))) :=
    hZeq.trans hrhs
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at hqeq
  have hZcoeff : ∀ j : Fin ℓ, Z j = ∑ u : ι, ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0)) := by
    intro j
    have hj := hqeq j.val j.isLt
    rw [Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at hj
    have hL : (∑ k : Fin ℓ, (Polynomial.monomial k.val (Z k)).coeff j.val) = Z j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : (∑ k : Fin ℓ, (Polynomial.monomial k.val
          (∑ u : ι, ((intBinom (d u) k.val : ℤ) : ZMod (2 ^ P0)))).coeff j.val) =
        ∑ u : ι, ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0)) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR] at hj
    exact sub_eq_zero.mp hj
  have hsum_mod :
      (∑ j : Fin ℓ, (newtonCoeff w Mlab j.val : ZMod (2 ^ P0)) * Z j) =
      (ZQ : ZMod (2 ^ P0)) := by
    simp_rw [hZcoeff, Finset.mul_sum]
    rw [Finset.sum_comm]
    change ∑ u : ι, ∑ j : Fin (dFilt w + 1),
        (newtonCoeff w Mlab j.val : ZMod (2 ^ P0)) * ((intBinom (d u) j.val : ℤ) : ZMod (2 ^ P0)) =
      (∑ u : ι, (filterPoly w Mlab).eval (d u) : ℤ)
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [filterPoly_newton_expansion w Mlab (d u)]
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (newtonCoeff w Mlab j : ZMod (2 ^ P0)) * ((intBinom (d u) j : ℤ) : ZMod (2 ^ P0)))]
    push_cast
    rfl
  rw [hsum_mod]
  have hZQnonneg : 0 ≤ ZQ := Finset.sum_nonneg fun u _ => filterPoly_nonneg w Mlab (d u)
  lift ZQ to ℕ using hZQnonneg with nZQ hnZQ
  have hZQlt' : (nZQ : ℤ) < (2 ^ P0 : ℤ) := by
    rw [hnZQ]
    exact hZQlt
  have hnZQlt : nZQ < 2 ^ P0 := by exact_mod_cast hZQlt'
  rw [Int.cast_natCast, ZMod.val_natCast_of_lt hnZQlt]
  exact hnZQ
