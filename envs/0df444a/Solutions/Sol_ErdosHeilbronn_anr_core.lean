-- Prove2me | solution 1 for ErdosHeilbronn.anr_core
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T21:11:09.944386+00:00
-- url     : https://prove2.me/submissions/32138f0c-f107-4c48-ab98-ff945968ab7c

import Mathlib

theorem solution {F : Type*} [Field F] [DecidableEq F]
    (A B : Finset F) (f : MvPolynomial (Fin 2) F) (hf : f ≠ 0)
    (k₁ k₂ : ℕ) (htA : k₁ + 1 = A.card) (htB : k₂ + 1 = B.card)
    (hdeg : MvPolynomial.totalDegree f ≤ k₁ + k₂)
    (hc : MvPolynomial.coeff (Finsupp.single 0 k₁ + Finsupp.single 1 k₂)
      (f * (MvPolynomial.X 0 + MvPolynomial.X 1) ^
        (k₁ + k₂ - MvPolynomial.totalDegree f)) ≠ 0) :
    (k₁ + k₂ - MvPolynomial.totalDegree f + 1)
      ≤ (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)).card := by
  classical
  set C := (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)) with hC
  set d := MvPolynomial.totalDegree f with hd
  set m := k₁ + k₂ - d with hm
  set t : Fin 2 →₀ ℕ := Finsupp.single 0 k₁ + Finsupp.single 1 k₂ with ht
  by_contra hlt
  push Not at hlt
  set n := m - C.card with hn
  have hnm : n + C.card = m := by omega
  set S : MvPolynomial (Fin 2) F := MvPolynomial.X 0 + MvPolynomial.X 1 with hS
  set Q : Polynomial F := ∏ c ∈ C, (Polynomial.X - Polynomial.C c) with hQ
  have hQm : Q.Monic := Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)
  have hQd : Q.natDegree = C.card := by
    rw [hQ, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)]
    simp
  set g : MvPolynomial (Fin 2) F := f * S ^ n * Polynomial.aeval S Q with hg
  have hdegS : ∀ j, (f * S ^ j).totalDegree ≤ d + j := by
    intro j
    refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left ?_ _)
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    have : S.totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
    nlinarith
  have hgsum : g = ∑ i ∈ Finset.range (C.card + 1), Q.coeff i • (f * S ^ (n + i)) := by
    rw [hg, Polynomial.aeval_eq_sum_range, hQd, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_smul_comm, pow_add, mul_assoc]
  have htdeg : t.degree = k₁ + k₂ := by
    rw [ht, map_add, Finsupp.degree_single, Finsupp.degree_single]
  have hcoeff : g.coeff t ≠ 0 := by
    rw [hgsum, MvPolynomial.coeff_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [MvPolynomial.coeff_smul, ← hQd, hQm.coeff_natDegree, one_smul, hQd, hnm]
      simpa using hc
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt, smul_zero]
      refine lt_of_le_of_lt (hdegS _) ?_
      have h2 : (∑ i ∈ t.support, t i) = k₁ + k₂ := htdeg
      have h3 := hQd
      have h4 := hnm
      omega
  have hgdeg : g.totalDegree = t.degree := by
    apply le_antisymm
    · rw [htdeg, hgsum]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
      rw [Finset.mem_range] at hi
      refine (MvPolynomial.totalDegree_smul_le _ _).trans ((hdegS _).trans ?_)
      omega
    · have := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 hcoeff)
      exact this
  obtain ⟨s, hs, hne⟩ := MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero g t hcoeff hgdeg
    ![A, B] (by intro i; fin_cases i <;> simp [ht] <;> omega)
  apply hne
  have hs' : ![s 0, s 1] = s := by funext i; fin_cases i <;> rfl
  by_cases hfs : MvPolynomial.eval s f = 0
  · simp [hg, hfs]
  · have hmem : s 0 + s 1 ∈ C := by
      rw [hC, Finset.mem_image]
      refine ⟨(s 0, s 1), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_product.2 ⟨by simpa using hs 0, by simpa using hs 1⟩, by rw [hs']; exact hfs⟩
    have : MvPolynomial.eval s (Polynomial.aeval S Q) = 0 := by
      rw [hQ, map_prod, map_prod]
      exact Finset.prod_eq_zero hmem (by simp [hS])
    simp [hg, this]
