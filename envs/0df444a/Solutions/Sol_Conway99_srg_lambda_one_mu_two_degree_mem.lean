-- Prove2me | solution 1 for Conway99.srg_lambda_one_mu_two_degree_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T17:42:17.797222+00:00
-- url     : https://prove2.me/submissions/6e5c275e-089e-445f-beb3-a348141bae98

import Mathlib
import Theorems.Thm_Conway99_srg_lambda_one_mu_two_card

open SimpleGraph Finset Matrix

set_option maxHeartbeats 1000000

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k : ℕ} (h : g.IsSRGWith n k 1 2) (hn : 1 < n) :
    k = 2 ∨ k = 4 ∨ k = 14 ∨ k = 22 ∨ k = 112 ∨ k = 994 := by
  classical
  have hcard : 2 * n = k ^ 2 + 2 := Conway99.srg_lambda_one_mu_two_card h (by omega)
  have hk2 : 2 ≤ k := by
    by_contra hc
    push_neg at hc
    interval_cases k <;> omega
  have hV : Fintype.card V = n := h.card
  have hAherm : (g.adjMatrix ℝ).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm]
  -- the complement's adjacency matrix
  have hcompl : (gᶜ).adjMatrix ℝ
      = (Matrix.of fun _ _ => (1 : ℝ)) - 1 - g.adjMatrix ℝ := by
    ext v w
    by_cases hvw : v = w
    · subst hvw
      simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.one_apply]
    · by_cases ha : g.Adj v w <;>
        simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.one_apply_ne hvw,
          hvw, ha]
  have hmat : (g.adjMatrix ℝ) * (g.adjMatrix ℝ)
      = ((k : ℝ) - 2) • (1 : Matrix V V ℝ) - g.adjMatrix ℝ
        + (2 : ℝ) • (Matrix.of fun _ _ => (1 : ℝ)) := by
    have hm : (g.adjMatrix ℝ) ^ 2
        = (k : ℕ) • (1 : Matrix V V ℝ) + (1 : ℕ) • g.adjMatrix ℝ
          + (2 : ℕ) • (gᶜ).adjMatrix ℝ := h.matrix_eq
    rw [pow_two] at hm
    rw [hm, hcompl]
    ext v w
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply]
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_one]
    ring
  -- mulVec dictionary
  set A : Matrix V V ℝ := g.adjMatrix ℝ with hAdef
  set J : Matrix V V ℝ := Matrix.of fun _ _ => (1 : ℝ) with hJdef
  have hJvec : ∀ x : V → ℝ, J *ᵥ x = fun _ => ∑ y, x y := by
    intro x
    funext i
    simp [hJdef, Matrix.mulVec, dotProduct]
  have hAconst : ∀ c : ℝ, A *ᵥ (fun _ => c) = fun _ => (k : ℝ) * c := by
    intro c
    funext i
    exact SimpleGraph.adjMatrix_mulVec_const_apply_of_regular h.regular
  set B := hAherm.eigenvectorBasis with hBdef
  set mu : V → ℝ := hAherm.eigenvalues with hmudef
  have hne : ∀ j : V, (⇑(B j) : V → ℝ) ≠ 0 := by
    intro j
    exact (WithLp.ofLp_eq_zero 2).ne.2 (B.orthonormal.ne_zero j)
  have hmul : ∀ j : V, A *ᵥ (⇑(B j) : V → ℝ) = mu j • (⇑(B j) : V → ℝ) :=
    fun j => hAherm.mulVec_eigenvectorBasis j
  -- the J-eigenvector identity
  have eqJ : ∀ j : V,
      (mu j ^ 2 + mu j - ((k : ℝ) - 2)) • (⇑(B j) : V → ℝ)
        = fun _ => 2 * ∑ y, (B j) y := by
    intro j
    have h1 : (A * A) *ᵥ (⇑(B j) : V → ℝ) = mu j ^ 2 • (⇑(B j) : V → ℝ) := by
      rw [← Matrix.mulVec_mulVec, hmul j, Matrix.mulVec_smul, hmul j, smul_smul]
      ring_nf
    rw [hmat] at h1
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hmul j, hJvec] at h1
    funext i
    have := congrFun h1 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith [this]
  -- every eigenvalue is `k` or a root of `x^2 + x - (k-2)`
  have key : ∀ j : V, (mu j - (k : ℝ)) * (mu j ^ 2 + mu j - ((k : ℝ) - 2)) = 0 := by
    intro j
    obtain ⟨i0, hi0⟩ : ∃ i, (B j) i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne j (funext hc)
    have hA1 : A *ᵥ (fun _ : V => 2 * ∑ y, (B j) y)
        = fun _ => (k : ℝ) * (2 * ∑ y, (B j) y) := hAconst _
    have hA2 : A *ᵥ ((mu j ^ 2 + mu j - ((k : ℝ) - 2)) • (⇑(B j) : V → ℝ))
        = (mu j ^ 2 + mu j - ((k : ℝ) - 2)) • (mu j • (⇑(B j) : V → ℝ)) := by
      rw [Matrix.mulVec_smul, hmul j]
    rw [eqJ j] at hA2
    have h5 := congrFun (hA1.symm.trans hA2) i0
    have hqi := congrFun (eqJ j) i0
    simp only [Pi.smul_apply, smul_eq_mul] at h5 hqi
    have h6 : (mu j - (k : ℝ)) * (mu j ^ 2 + mu j - ((k : ℝ) - 2)) * (B j) i0 = 0 := by
      linear_combination (-1 : ℝ) * h5 - (k : ℝ) * hqi
    rcases mul_eq_zero.mp h6 with h' | h'
    · exact h'
    · exact absurd h' hi0
  have hVne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- the fibre of the eigenvalue `k`
  set T : Finset V := Finset.univ.filter (fun j => mu j = (k : ℝ)) with hTdef
  have hTne : T.Nonempty := by
    have hones : (fun _ : V => (1 : ℝ)) ≠ 0 := by
      intro hc
      have := congrFun hc (Classical.arbitrary V)
      simp at this
    have hMv : (((k : ℝ) • (1 : Matrix V V ℝ)) - A) *ᵥ (fun _ : V => (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAconst]
      funext i
      simp
    have hdet : (((k : ℝ) • (1 : Matrix V V ℝ)) - A).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hones, hMv⟩
    have hmem : (k : ℝ) ∈ spectrum ℝ A := by
      rw [spectrum.mem_iff]
      intro hu
      rw [Algebra.algebraMap_eq_smul_one] at hu
      rw [Matrix.isUnit_iff_isUnit_det, hdet] at hu
      exact not_isUnit_zero hu
    rw [hAherm.spectrum_real_eq_range_eigenvalues] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, by simp [hTdef, hmudef, hj]⟩
  have hconst : ∀ j ∈ T, ∃ c : ℝ, c ≠ 0 ∧ (⇑(B j) : V → ℝ) = fun _ => c := by
    intro j hj
    rw [hTdef, Finset.mem_filter] at hj
    have hmuj : mu j = (k : ℝ) := hj.2
    have hq : mu j ^ 2 + mu j - ((k : ℝ) - 2) = 2 * (n : ℝ) := by
      have hc2 : (2 * n : ℝ) = (k : ℝ) ^ 2 + 2 := by exact_mod_cast hcard
      rw [hmuj]; linarith
    have hw : ∀ i, (2 * (n : ℝ)) * (B j) i = 2 * ∑ y, (B j) y := by
      intro i
      have h7 := congrFun (eqJ j) i
      simp only [Pi.smul_apply, smul_eq_mul] at h7
      rw [hq] at h7
      exact h7
    refine ⟨(∑ y, (B j) y) / n, ?_, ?_⟩
    · intro hc0
      apply hne j
      funext i
      have := hw i
      rw [div_eq_zero_iff] at hc0
      rcases hc0 with hc0 | hc0
      · rw [hc0] at this
        simp only [Pi.zero_apply]
        nlinarith [this]
      · exact absurd hc0 (ne_of_gt hnR)
    · funext i
      have := hw i
      field_simp
      linarith [this]
  have hTle : T.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b' hb' 
    by_contra hab
    obtain ⟨c1, hc1, he1⟩ := hconst a ha
    obtain ⟨c2, hc2, he2⟩ := hconst b' hb'
    have horth : inner ℝ (B a) (B b') = (0 : ℝ) := B.orthonormal.2 hab
    rw [PiLp.inner_apply] at horth
    have : ∀ i : V, inner ℝ ((B a) i) ((B b') i) = c1 * c2 := by
      intro i
      have e1 : (B a) i = c1 := congrFun he1 i
      have e2 : (B b') i = c2 := congrFun he2 i
      rw [e1, e2]
      simp [RCLike.inner_apply]
      ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ, hV,
      nsmul_eq_mul] at horth
    have : (n : ℝ) * (c1 * c2) ≠ 0 := by
      exact mul_ne_zero (ne_of_gt hnR) (mul_ne_zero hc1 hc2)
    exact this horth
  have hTcard : T.card = 1 := le_antisymm hTle (Finset.card_pos.mpr hTne)
  -- the other two eigenvalues are ±s shifted
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hmR : (0 : ℝ) < 4 * (k : ℝ) - 7 := by linarith
  set s : ℝ := Real.sqrt (4 * (k : ℝ) - 7) with hsdef
  have hs2 : s ^ 2 = 4 * (k : ℝ) - 7 := Real.sq_sqrt (le_of_lt hmR)
  have hspos : 0 < s := Real.sqrt_pos.mpr hmR
  have hpm : ∀ j ∈ Finset.univ \ T, (2 * mu j + 1 = s) ∨ (2 * mu j + 1 = -s) := by
    intro j hj
    have hjT : mu j ≠ (k : ℝ) := by
      rw [Finset.mem_sdiff, hTdef, Finset.mem_filter] at hj
      intro hc
      exact hj.2 ⟨Finset.mem_univ j, hc⟩
    have hq0 : mu j ^ 2 + mu j - ((k : ℝ) - 2) = 0 := by
      rcases mul_eq_zero.mp (key j) with h' | h'
      · exact absurd (by linarith : mu j = (k : ℝ)) hjT
      · exact h'
    have h9 : (2 * mu j + 1 - s) * (2 * mu j + 1 + s) = 0 := by
      have : (2 * mu j + 1) ^ 2 = s ^ 2 := by rw [hs2]; nlinarith [hq0]
      nlinarith [this]
    rcases mul_eq_zero.mp h9 with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  -- trace
  have htrace : ∑ j : V, mu j = 0 := by
    have h1 : A.trace = ∑ j : V, ((mu j : ℝ) : ℝ) := hAherm.trace_eq_sum_eigenvalues
    rw [hAdef, SimpleGraph.trace_adjMatrix] at h1
    simpa using h1.symm
  have hsum1 : ∑ j : V, (2 * mu j + 1) = (n : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htrace, Finset.sum_const, Finset.card_univ, hV]
    simp
  set P : Finset V := (Finset.univ \ T).filter (fun j => 2 * mu j + 1 = s) with hPdef
  set Q : Finset V := (Finset.univ \ T).filter (fun j => ¬ (2 * mu j + 1 = s)) with hQdef
  have hsumT : ∑ j ∈ T, (2 * mu j + 1) = 2 * (k : ℝ) + 1 := by
    have : ∀ j ∈ T, 2 * mu j + 1 = 2 * (k : ℝ) + 1 := by
      intro j hj
      rw [hTdef, Finset.mem_filter] at hj
      rw [hj.2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hTcard, one_smul]
  have hsumR : ∑ j ∈ Finset.univ \ T, (2 * mu j + 1) = (P.card : ℝ) * s + (Q.card : ℝ) * (-s) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ \ T) (fun j => 2 * mu j + 1 = s)]
    congr 1
    · rw [hPdef]
      rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.sum_const,
        nsmul_eq_mul]
    · rw [hQdef]
      have hall : ∀ j ∈ (Finset.univ \ T).filter (fun j => ¬ (2 * mu j + 1 = s)),
          2 * mu j + 1 = -s := by
        intro j hj
        have hj1 := Finset.mem_filter.mp hj
        rcases hpm j hj1.1 with h' | h'
        · exact absurd h' hj1.2
        · exact h'
      rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul]
  have hkey : (2 * (k : ℝ) + 1) + ((P.card : ℝ) - Q.card) * s = (n : ℝ) := by
    have hsp : ∑ j : V, (2 * mu j + 1)
        = ∑ j ∈ Finset.univ \ T, (2 * mu j + 1) + ∑ j ∈ T, (2 * mu j + 1) :=
      (Finset.sum_sdiff (Finset.subset_univ T)).symm
    rw [hsp, hsumR, hsumT] at hsum1
    linarith [hsum1]
  -- pass to the integers
  have hR : (((P.card : ℤ) - Q.card : ℤ) : ℝ) ^ 2 * (4 * (k : ℝ) - 7)
      = ((n : ℝ) - 2 * (k : ℝ) - 1) ^ 2 := by
    have h1 : ((P.card : ℝ) - Q.card) * s = (n : ℝ) - 2 * (k : ℝ) - 1 := by linarith
    have h2 := congrArg (fun x : ℝ => x ^ 2) h1
    simp only [mul_pow, hs2] at h2
    push_cast
    exact h2
  have hZ : ((P.card : ℤ) - Q.card) ^ 2 * (4 * (k : ℤ) - 7) = ((n : ℤ) - 2 * (k : ℤ) - 1) ^ 2 := by
    exact_mod_cast hR
  have hn2 : 2 * (n : ℤ) = (k : ℤ) ^ 2 + 2 := by exact_mod_cast hcard
  have hk2Z : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk2
  set Dz : ℤ := (P.card : ℤ) - Q.card with hDzdef
  set tz : ℤ := (n : ℤ) - 2 * (k : ℤ) - 1 with htzdef
  have h2tz : 2 * tz = (k : ℤ) ^ 2 - 4 * (k : ℤ) := by rw [htzdef]; linarith
  by_cases hD : Dz = 0
  · have htz : tz = 0 := by
      have : tz ^ 2 = 0 := by rw [← hZ, hD]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : (k : ℤ) ^ 2 = 4 * (k : ℤ) := by rw [htz] at h2tz; linarith
    have hk4 : (k : ℤ) = 4 := by nlinarith [hk2Z]
    exact Or.inr (Or.inl (by exact_mod_cast hk4))
  · have hdvd2 : Dz ^ 2 ∣ tz ^ 2 := ⟨4 * (k : ℤ) - 7, hZ.symm⟩
    have hdvd : Dz ∣ tz := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd2
    obtain ⟨u, hu⟩ := hdvd
    have hM : 4 * (k : ℤ) - 7 = u ^ 2 := by
      have h1 : Dz ^ 2 * (4 * (k : ℤ) - 7) = Dz ^ 2 * u ^ 2 := by rw [hZ, hu]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hD) h1
    have hd : 2 * (Dz * u) = (k : ℤ) ^ 2 - 4 * (k : ℤ) := by rw [← hu]; exact h2tz
    have hc' : u ^ 2 = 4 * (k : ℤ) - 7 := hM.symm
    have h32 : 32 * (Dz * u) = u ^ 4 - 2 * u ^ 2 - 63 := by
      linear_combination 16 * hd - (u ^ 2 + 4 * (k : ℤ) - 9) * hc'
    have h63 : (63 : ℤ) = u * (u ^ 3 - 2 * u - 32 * Dz) := by linear_combination h32
    have hudvd : u ∣ 63 := ⟨u ^ 3 - 2 * u - 32 * Dz, h63⟩
    have hune : u ≠ 0 := by
      intro hc0
      rw [hc0] at hc'
      simp at hc'
      omega
    obtain ⟨U, hUdef⟩ : ∃ U : ℕ, U = u.natAbs := ⟨_, rfl⟩
    have hUdvd : U ∣ 63 := by
      have h1 := Int.natAbs_dvd_natAbs.mpr hudvd
      rw [hUdef]
      simpa using h1
    have hUpos : 0 < U := by rw [hUdef]; exact Int.natAbs_pos.mpr hune
    have hUk : 4 * k = U * U + 7 := by
      have h1 : (U : ℤ) * (U : ℤ) = u ^ 2 := by
        rw [hUdef, Int.natAbs_mul_self']
        ring
      have h2 : 4 * (k : ℤ) = (U : ℤ) * (U : ℤ) + 7 := by rw [h1]; linarith [hc']
      exact_mod_cast h2
    have hmemd : U ∈ Nat.divisors 63 := Nat.mem_divisors.mpr ⟨hUdvd, by norm_num⟩
    have h63d : Nat.divisors 63 = {1, 3, 7, 9, 21, 63} := by decide
    rw [h63d] at hmemd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemd
    rcases hmemd with h' | h' | h' | h' | h' | h' <;> rw [h'] at hUk <;> omega
