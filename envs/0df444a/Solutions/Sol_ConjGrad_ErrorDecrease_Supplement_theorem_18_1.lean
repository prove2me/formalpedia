-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_18_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:12.379805+00:00
-- url     : https://prove2.me/submissions/83442f38-7583-4706-9527-1a21df0269cf

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cfConv
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:1 (Hestenes–Stiefel 1952, p. 432): for symmetric positive definite `A` and an
initial residual `r₀ = k − Ax₀` not perpendicular to any eigenvector, the cg numbers `aᵢ`, `bᵢ`
are obtained by expanding `F = Q/χ` (`Q` the characteristic polynomial of `A` with respect to
`r₀`, `χ` the characteristic polynomial of `A`) into the normalized continued fraction (18:2):
`F = κ Nₙ/Rₙ` with `κ = a₀|r₀|²`, `Rₙ = χ/χ(0)`, `bᵢ = cᵢ₊₁aᵢ/aᵢ₊₁` (15:4), and these
coefficients are the only ones giving such an expansion. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ)
    (hcyc : ∀ (v : Fin n → ℝ) (c : ℝ), v ≠ 0 → A *ᵥ v = c • v →
      (cgIter A k x₀ 0).r ⬝ᵥ v ≠ 0) :
    (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
        Polynomial.C (A.charpoly.eval 0)⁻¹ * A.charpoly ∧
    relCharPoly A (cgIter A k x₀ 0).r * (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
      Polynomial.C (cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) *
        (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).1 * A.charpoly ∧
    (∀ i : ℕ, i + 1 < n →
      ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        cgCoeffC A k x₀ (i + 1) * cgAlpha A (cgIter A k x₀ i) /
          cgAlpha A (cgIter A k x₀ (i + 1))) ∧
    (0 < n → cgBeta A k x₀ (n - 1) = 0) ∧
    (∀ (a c : ℕ → ℝ) (κ : ℝ), (∀ i < n, a i ≠ 0) →
      relCharPoly A (cgIter A k x₀ 0).r * (cfConv a c n).2 = Polynomial.C κ * (cfConv a c n).1 * A.charpoly →
      (0 < n → κ = cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) ∧
      (∀ i < n, a i = cgAlpha A (cgIter A k x₀ i)) ∧
      ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i) := by
        classical
        open Polynomial in
        set r0 : Fin n → ℝ := (cgIter A k x₀ 0).r with hr0def
        set χ : Polynomial ℝ := A.charpoly with hχdef
        have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
          intro u v
          have hT : Aᵀ = A := by
            have := hA.1
            rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
        have hposA : ∀ w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w) := by
          intro w hw
          simpa using hA.dotProduct_mulVec_pos hw
        have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
        -- eigen data
        obtain ⟨lam, b, ob, eig, hlpos, inj, hα, expand, hχprod⟩ : ∃ (lam : Fin n → ℝ)
            (b : Fin n → Fin n → ℝ), (∀ i j, b i ⬝ᵥ b j = if i = j then 1 else 0) ∧
            (∀ j, A *ᵥ b j = lam j • b j) ∧ (∀ j, 0 < lam j) ∧ Function.Injective lam ∧
            (∀ j, r0 ⬝ᵥ b j ≠ 0) ∧ (∀ w : Fin n → ℝ, w = ∑ j, (w ⬝ᵥ b j) • b j) ∧
            χ = ∏ j, (Polynomial.X - Polynomial.C (lam j)) := by
          clear hsym hposA hzero
          let b : Fin n → Fin n → ℝ := fun i => WithLp.ofLp (hA.1.eigenvectorBasis i)
          have ob : ∀ i j, b i ⬝ᵥ b j = if i = j then 1 else 0 := by
            intro i j
            have := orthonormal_iff_ite.mp hA.1.eigenvectorBasis.orthonormal i j
            rw [EuclideanSpace.inner_eq_star_dotProduct] at this
            simpa [b, dotProduct_comm] using this
          have eig : ∀ j, A *ᵥ b j = hA.1.eigenvalues j • b j := fun j => hA.1.mulVec_eigenvectorBasis j
          have bne : ∀ j, b j ≠ 0 := by
            intro j h; have := ob j j; simp [h] at this
          have inj : Function.Injective hA.1.eigenvalues := by
            intro i j hij
            by_contra hne
            by_cases hi : r0 ⬝ᵥ b i = 0
            · exact hcyc (b i) _ (bne i) (eig i) hi
            · have hv : (r0 ⬝ᵥ b j) • b i - (r0 ⬝ᵥ b i) • b j ≠ 0 := by
                intro h0
                have := congrArg (fun x => x ⬝ᵥ b j) h0
                simp [sub_dotProduct, ob, hne] at this
                exact hi this
              apply hcyc _ (hA.1.eigenvalues i) hv
              · rw [mulVec_sub, mulVec_smul, mulVec_smul, eig, eig, ← hij, smul_sub,
                  smul_comm (hA.1.eigenvalues i) (r0 ⬝ᵥ b j), smul_comm (hA.1.eigenvalues i) (r0 ⬝ᵥ b i)]
              · simp [dotProduct_sub, dotProduct_smul, mul_comm]
          have expand : ∀ w : Fin n → ℝ, w = ∑ i, (w ⬝ᵥ b i) • b i := by
            intro w
            have h := hA.1.eigenvectorBasis.sum_repr' (WithLp.toLp 2 w)
            have h2 := congrArg WithLp.ofLp h
            simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at h2
            simpa [b, dotProduct_comm] using h2.symm
          refine ⟨hA.1.eigenvalues, b, ob, eig, fun j => hA.eigenvalues_pos j, inj,
            fun j => hcyc _ _ (bne j) (eig j), expand, ?_⟩
          rw [hχdef, hA.1.charpoly_eq]
          rfl
        have EV : ∀ (P : Polynomial ℝ) (w : Fin n → ℝ) (j : Fin n),
            (Polynomial.aeval A P *ᵥ w) ⬝ᵥ b j = P.eval (lam j) * (w ⬝ᵥ b j) := by
          clear hposA hzero expand hα inj hlpos hχprod
          have hpow : ∀ (m : ℕ) (w : Fin n → ℝ) (j : Fin n),
              ((A ^ m) *ᵥ w) ⬝ᵥ b j = lam j ^ m * (w ⬝ᵥ b j) := by
            intro m
            induction m with
            | zero => intro w j; rw [pow_zero, one_mulVec, pow_zero, one_mul]
            | succ m ih =>
              intro w j
              rw [pow_succ, ← mulVec_mulVec, ih, dotProduct_comm, hsym, eig, dotProduct_smul,
                smul_eq_mul, pow_succ]
              ring
          intro P w j
          induction P using Polynomial.induction_on' with
          | add p q hp hq =>
            rw [map_add, add_mulVec, add_dotProduct, hp, hq, Polynomial.eval_add, add_mul]
          | monomial m r =>
            rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
              smul_mulVec, smul_dotProduct, hpow, Polynomial.eval_monomial, smul_eq_mul]
            ring
        have ROOTS : ∀ P : Polynomial ℝ, P.natDegree ≤ n → P.eval 0 = 0 →
            (∀ j, P.eval (lam j) = 0) → P = 0 := by
          intro P hd h0 hl
          have hinj : Function.Injective (Fin.cons (0 : ℝ) lam : Fin (n+1) → ℝ) := by
            rw [Fin.cons_injective_iff]
            refine ⟨?_, inj⟩
            rintro ⟨j, hj⟩
            exact (hlpos j).ne' hj
          refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj ?_ ?_
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact h0
            · rw [Fin.cons_succ]; exact hl j
          · rw [Fintype.card_fin]; omega
        have ROOTS' : ∀ P : Polynomial ℝ, P.natDegree < n → (∀ j, P.eval (lam j) = 0) → P = 0 := by
          intro P hd hl
          refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P inj hl ?_
          rw [Fintype.card_fin]; exact hd
        have hχmonic : χ.Monic := Matrix.charpoly_monic A
        have hχdeg : χ.natDegree = n := by simp [hχdef]
        have hχroot : ∀ j, χ.eval (lam j) = 0 := by
          intro j
          have := EV χ (b j) j
          rw [hχdef, Matrix.aeval_self_charpoly, zero_mulVec, zero_dotProduct, ob, if_pos rfl,
            mul_one] at this
          exact this.symm
        have hχ0 : χ.eval 0 ≠ 0 := by
          intro h
          exact hχmonic.ne_zero (ROOTS χ hχdeg.le h hχroot)
        have vanish : ∀ P : Polynomial ℝ, Polynomial.aeval A P *ᵥ r0 = 0 → ∀ j, P.eval (lam j) = 0 := by
          intro P h j
          have := EV P r0 j
          rw [h, zero_dotProduct] at this
          exact (mul_eq_zero.mp this.symm).resolve_right (hα j)
        have KRYa : ∀ P : Polynomial ℝ, P.natDegree < n → P.eval 0 = 1 →
            Polynomial.aeval A P *ᵥ r0 ≠ 0 := by
          intro P hd h0 h
          have := ROOTS' P hd (vanish P h)
          rw [this, Polynomial.eval_zero] at h0
          exact zero_ne_one h0
        have KRYb : ∀ P : Polynomial ℝ, P.natDegree ≤ n → P.eval 0 = 1 →
            Polynomial.aeval A P *ᵥ r0 = 0 → P = Polynomial.C (χ.eval 0)⁻¹ * χ := by
          intro P hd h0 h
          have hv := vanish P h
          refine sub_eq_zero.mp (ROOTS _ ?_ ?_ ?_)
          · refine (Polynomial.natDegree_sub_le _ _).trans (max_le hd ?_)
            exact (Polynomial.natDegree_C_mul_le _ _).trans hχdeg.le
          · rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, h0, inv_mul_cancel₀ hχ0,
              sub_self]
          · intro j
            rw [Polynomial.eval_sub, Polynomial.eval_mul, hχroot, hv, mul_zero, sub_zero]
        have KRYc : ∀ S : Polynomial ℝ, S.natDegree < n → Polynomial.aeval A S *ᵥ r0 = 0 → S = 0 := by
          intro S hd h
          exact ROOTS' S hd (vanish S h)
        -- the functional T
        set y : Fin n → Polynomial ℝ :=
          Matrix.vecMul (fun i => Polynomial.C (r0 i)) (adjugate (charmatrix A)) with hydef
        set T : (Fin n → ℝ) → Polynomial ℝ := fun w => y ⬝ᵥ (fun j => Polynomial.C (w j)) with hTdef
        have TQ : relCharPoly A r0 = T r0 := by
          show relCharPoly A r0 = y ⬝ᵥ (fun j => Polynomial.C (r0 j))
          rw [hydef]
          unfold relCharPoly
          simp only [dotProduct, vecMul, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.C_mul]; ring
        have Tadd : ∀ u v, T (u + v) = T u + T v := by
          intro u v
          show y ⬝ᵥ (fun j => Polynomial.C ((u + v) j)) = y ⬝ᵥ (fun j => Polynomial.C (u j))
            + y ⬝ᵥ (fun j => Polynomial.C (v j))
          rw [← dotProduct_add]
          congr 1; funext j; exact Polynomial.C_add
        have Tsub : ∀ u v, T (u - v) = T u - T v := by
          intro u v
          show y ⬝ᵥ (fun j => Polynomial.C ((u - v) j)) = y ⬝ᵥ (fun j => Polynomial.C (u j))
            - y ⬝ᵥ (fun j => Polynomial.C (v j))
          rw [← dotProduct_sub]
          congr 1; funext j; exact Polynomial.C_sub
        have Tsmul : ∀ (t : ℝ) u, T (t • u) = Polynomial.C t * T u := by
          intro t u
          show y ⬝ᵥ (fun j => Polynomial.C ((t • u) j)) = Polynomial.C t * y ⬝ᵥ (fun j => Polynomial.C (u j))
          rw [← smul_eq_mul, ← dotProduct_smul]
          congr 1; funext j
          show Polynomial.C (t * u j) = Polynomial.C t * Polynomial.C (u j)
          exact Polynomial.C_mul
        have T0 : T 0 = 0 := by
          show y ⬝ᵥ (fun j => Polynomial.C ((0 : Fin n → ℝ) j)) = 0
          simp only [Pi.zero_apply, map_zero]
          exact dotProduct_zero y
        have TA : ∀ w, T (A *ᵥ w) = Polynomial.X * T w - χ * Polynomial.C (r0 ⬝ᵥ w) := by
          intro w
          have hM : A.map Polynomial.C = (Polynomial.X : Polynomial ℝ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ))
              - charmatrix A := by
            refine Matrix.ext fun i j => ?_
            rw [Matrix.sub_apply, charmatrix_apply, Matrix.smul_apply, Matrix.map_apply]
            by_cases h : i = j
            · subst h; simp
            · simp [h]
          have hadj : adjugate (charmatrix A) * A.map Polynomial.C =
              (Polynomial.X : Polynomial ℝ) • adjugate (charmatrix A) - χ • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) := by
            rw [hM, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, adjugate_mul]
            rfl
          have hv : (fun j => Polynomial.C ((A *ᵥ w) j)) = A.map Polynomial.C *ᵥ (fun j => Polynomial.C (w j)) := by
            funext j
            exact RingHom.map_mulVec Polynomial.C A w j
          show y ⬝ᵥ (fun j => Polynomial.C ((A *ᵥ w) j)) = Polynomial.X * (y ⬝ᵥ (fun j => Polynomial.C (w j)))
            - χ * Polynomial.C (r0 ⬝ᵥ w)
          rw [hv, dotProduct_mulVec, hydef, vecMul_vecMul, hadj, vecMul_sub, vecMul_smul, vecMul_smul, vecMul_one,
            sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
            RingHom.map_dotProduct]
          rfl
        have Tev : ∀ w j, (T w).eval (lam j) = 0 → w ⬝ᵥ b j = 0 := by
          have hTb : ∀ kk, T (b kk) = Polynomial.C (r0 ⬝ᵥ b kk) *
              ∏ l ∈ Finset.univ.erase kk, (Polynomial.X - Polynomial.C (lam l)) := by
            intro kk
            have h1 := TA (b kk)
            rw [eig, Tsmul, hχprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ kk)] at h1
            refine mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (lam kk)) ?_
            linear_combination -h1
          have Tsum : ∀ (s : Finset (Fin n)) (f : Fin n → Fin n → ℝ),
              T (∑ kk ∈ s, f kk) = ∑ kk ∈ s, T (f kk) := by
            intro s f
            induction s using Finset.induction_on with
            | empty => rw [Finset.sum_empty, Finset.sum_empty, T0]
            | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Tadd, ih]
          intro w j hw
          rw [expand w, Tsum, Polynomial.eval_finsetSum, Finset.sum_eq_single j] at hw
          · rw [Tsmul, hTb, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_C, Polynomial.eval_prod] at hw
            have hp : ∏ l ∈ Finset.univ.erase j, Polynomial.eval (lam j) (Polynomial.X - Polynomial.C (lam l)) ≠ 0 := by
              rw [Finset.prod_ne_zero_iff]
              intro l hl
              rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
              exact fun h => (Finset.mem_erase.mp hl).1 (inj h).symm
            rcases mul_eq_zero.mp hw with h | h
            · exact h
            · exact absurd ((mul_eq_zero.mp h).resolve_left (hα j)) hp
          · intro kk _ hk
            rw [Tsmul, hTb, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_prod]
            rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun h => hk h.symm, Finset.mem_univ j⟩)
              (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])]
            ring
          · intro h; exact absurd (Finset.mem_univ j) h
        -- generic continued-fraction facts
        have cfDeg : ∀ (a c : ℕ → ℝ) (i m : ℕ), i < m → ((cfConv a c i).2).coeff m = 0 := by
          clear * -
          intro a c
          have hc : ∀ (u v w : ℝ) (P Q : Polynomial ℝ) (m : ℕ),
              ((Polynomial.C u - Polynomial.C v * Polynomial.X) * P - Polynomial.C w * Q).coeff (m+1) =
                u * P.coeff (m+1) - v * P.coeff m - w * Q.coeff (m+1) := by
            intro u v w P Q m
            rw [sub_mul, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
          have key : ∀ i, (∀ m, i < m → ((cfConv a c i).2).coeff m = 0) ∧
              (∀ m, i + 1 < m → ((cfConv a c (i+1)).2).coeff m = 0) := by
            intro i
            induction i with
            | zero =>
              refine ⟨fun m hm => ?_, fun m hm => ?_⟩
              · show (1 : Polynomial ℝ).coeff m = 0
                rw [Polynomial.coeff_one, if_neg (by omega)]
              · show (1 - Polynomial.C (a 0) * Polynomial.X).coeff m = 0
                rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega),
                  Polynomial.coeff_C_mul_X, if_neg (by omega), sub_zero]
            | succ i ih =>
              refine ⟨ih.2, fun m hm => ?_⟩
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              show ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2).coeff (m'+1) = 0
              rw [hc, ih.2 _ (by omega), ih.2 _ (by omega), ih.1 _ (by omega)]
              ring
          intro i m him
          exact (key i).1 m him
        have cfNat : ∀ (a c : ℕ → ℝ) (i : ℕ), ((cfConv a c i).2).natDegree ≤ i := by
          intro a c i
          exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => cfDeg a c i m (by exact_mod_cast hm))
        have cfLead : ∀ (a c : ℕ → ℝ) (i : ℕ),
            ((cfConv a c i).2).coeff i = ∏ l ∈ Finset.range i, (-a l) := by
          intro a c
          have key : ∀ i, ((cfConv a c i).2).coeff i = ∏ l ∈ Finset.range i, (-a l) ∧
              ((cfConv a c (i+1)).2).coeff (i+1) = ∏ l ∈ Finset.range (i+1), (-a l) := by
            intro i
            induction i with
            | zero =>
              refine ⟨by simp [cfConv], ?_⟩
              show (1 - Polynomial.C (a 0) * Polynomial.X).coeff 1 = _
              rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega),
                  Polynomial.coeff_C_mul_X, if_pos rfl, Finset.prod_range_one, zero_sub]
            | succ i ih =>
              refine ⟨ih.2, ?_⟩
              show ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2).coeff (i+2) = _
              rw [sub_mul, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
                Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
                cfDeg a c (i+1) (i+2) (by omega), cfDeg a c i (i+2) (by omega), ih.2,
                Finset.prod_range_succ _ (i+1)]
              ring
          exact fun i => (key i).1
        have cf0 : ∀ (a c : ℕ → ℝ) (i : ℕ), ((cfConv a c i).2).eval 0 = 1 := by
          clear * -
          intro a c
          have key : ∀ i, ((cfConv a c i).2).eval 0 = 1 ∧ ((cfConv a c (i+1)).2).eval 0 = 1 := by
            intro i
            induction i with
            | zero =>
              refine ⟨Polynomial.eval_one, ?_⟩
              show (1 - Polynomial.C (a 0) * Polynomial.X).eval 0 = 1
              simp
            | succ i ih =>
              refine ⟨ih.2, ?_⟩
              show ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2).eval 0 = 1
              rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, ih.1, ih.2,
                Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
                Polynomial.eval_C, Polynomial.eval_X]
              ring
          exact fun i => (key i).1
        have cfrec : ∀ (a c : ℕ → ℝ) (i : ℕ), cfConv a c (i + 2) =
            ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).1
                - Polynomial.C (c (i+1)) * (cfConv a c i).1,
             (Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2) := fun a c i => rfl
        -- residual vectors of a continued fraction
        set ρ : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (Fin n → ℝ) :=
          fun a c i => Polynomial.aeval A (cfConv a c i).2 *ᵥ r0 with hρdef
        have ρ0 : ∀ a c, ρ a c 0 = r0 := by
          intro a c
          show Polynomial.aeval A (1 : Polynomial ℝ) *ᵥ r0 = r0
          rw [map_one, one_mulVec]
        have ρ1 : ∀ a c, ρ a c 1 = r0 - a 0 • (A *ᵥ r0) := by
          intro a c
          show Polynomial.aeval A (1 - Polynomial.C (a 0) * Polynomial.X) *ᵥ r0 = r0 - a 0 • (A *ᵥ r0)
          rw [map_sub, map_one, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
            Algebra.algebraMap_eq_smul_one, sub_mulVec, one_mulVec, smul_mul_assoc, one_mul,
            smul_mulVec]
        have ρrec : ∀ a c i, ρ a c (i+2) = (1 + c (i+1)) • ρ a c (i+1)
            - a (i+1) • (A *ᵥ ρ a c (i+1)) - c (i+1) • ρ a c i := by
          intro a c i
          show Polynomial.aeval A ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2) *ᵥ r0 = _
          rw [map_sub, map_mul, map_mul, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C,
            Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
            Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_mulVec, sub_mul,
            sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, smul_mul_assoc, one_mul,
            smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec, one_mulVec]
        -- the defect polynomial
        set Z : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℕ → Polynomial ℝ :=
          fun a c κ i => (cfConv a c i).2 * relCharPoly A r0 - T (ρ a c i)
            - Polynomial.C κ * (cfConv a c i).1 * χ with hZdef
        have Z0 : ∀ a c κ, Z a c κ 0 = 0 := by
          intro a c κ
          show (1 : Polynomial ℝ) * relCharPoly A r0 - T (ρ a c 0) - Polynomial.C κ * 0 * χ = 0
          rw [ρ0, TQ]; ring
        have Z1 : ∀ a c κ, Z a c κ 1 = χ * Polynomial.C (κ - a 0 * (r0 ⬝ᵥ r0)) := by
          intro a c κ
          show (1 - Polynomial.C (a 0) * Polynomial.X) * relCharPoly A r0 - T (ρ a c 1)
            - Polynomial.C κ * (-1) * χ = _
          rw [ρ1, Tsub, Tsmul, TA, ← TQ, Polynomial.C_sub, Polynomial.C_mul]; ring
        have Zrec : ∀ a c κ i, Z a c κ (i+2) =
            (Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * Z a c κ (i+1)
              - Polynomial.C (c (i+1)) * Z a c κ i
              + χ * Polynomial.C (-(a (i+1)) * (r0 ⬝ᵥ ρ a c (i+1))) := by
          intro a c κ i
          show ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).2
                - Polynomial.C (c (i+1)) * (cfConv a c i).2) * relCharPoly A r0 - T (ρ a c (i+2))
            - Polynomial.C κ * ((Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * (cfConv a c (i+1)).1
                - Polynomial.C (c (i+1)) * (cfConv a c i).1) * χ = _
          rw [ρrec, Tsub, Tsub, Tsmul, Tsmul, Tsmul, TA, Polynomial.C_mul, Polynomial.C_neg]
          simp only [hZdef]
          ring
        have TRI : ∀ (a c f : ℕ → ℝ) (W : ℕ → Polynomial ℝ), W 0 = 0 → W 1 = χ * Polynomial.C (f 0) →
            (∀ i, W (i+2) = (Polynomial.C (1 + c (i+1)) - Polynomial.C (a (i+1)) * Polynomial.X) * W (i+1)
              - Polynomial.C (c (i+1)) * W i + χ * Polynomial.C (f (i+1))) →
            ∀ j, (∀ l < j, f l = 0) → ∀ i, (i ≤ j → W i = 0) ∧
              (j < i → (∀ m, n + (i - 1 - j) < m → (W i).coeff m = 0) ∧
                (W i).coeff (n + (i - 1 - j)) = f j * ∏ l ∈ Finset.Ico (j+1) i, (-a l)) := by
          clear * - hχmonic hχdeg
          intro a c f W h0 h1 hrec j hj i
          have hχc : ∀ m, n < m → χ.coeff m = 0 := fun m hm =>
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hχdeg]; exact hm)
          have hχn : χ.coeff n = 1 := by
            have := hχmonic.coeff_natDegree; rw [hχdeg] at this; exact this
          have hco : ∀ i m, (W (i+2)).coeff (m+1) = (1 + c (i+1)) * (W (i+1)).coeff (m+1)
              - a (i+1) * (W (i+1)).coeff m - c (i+1) * (W i).coeff (m+1) + χ.coeff (m+1) * f (i+1) := by
            intro i m
            rw [hrec, sub_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sub,
              Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_mul_C]
          induction i using Nat.strong_induction_on with
          | _ i ih =>
          rcases i with _ | _ | i
          · exact ⟨fun _ => h0, fun h => absurd h (Nat.not_lt_zero _)⟩
          · refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [h1, hj 0 (by omega), map_zero, mul_zero]
            · obtain rfl : j = 0 := by omega
              refine ⟨fun m hm => ?_, ?_⟩
              · rw [h1, Polynomial.coeff_mul_C, hχc m (by omega), zero_mul]
              · rw [h1, Polynomial.coeff_mul_C, show n + (0 + 1 - 1 - 0) = n by omega, hχn,
                  Finset.Ico_self, Finset.prod_empty]; ring
          · have ih1 := ih (i+1) (by omega)
            have ih0 := ih i (by omega)
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [hrec, ih1.1 (by omega), ih0.1 (by omega), hj (i+1) (by omega), map_zero, mul_zero,
                mul_zero, mul_zero, sub_zero, add_zero]
            · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
              · -- j ≤ i
                have hj1 : j < i + 1 := by omega
                obtain ⟨A1, A2⟩ := ih1.2 hj1
                rw [show n + (i + 1 - 1 - j) = n + (i - j) by omega] at A1 A2
                have B : ∀ m, n + (i - j) ≤ m → (W i).coeff m = 0 := by
                  intro m hm
                  rcases Nat.lt_or_ge j i with hji | hji
                  · exact (ih0.2 hji).1 m (by omega)
                  · rw [ih0.1 hji, Polynomial.coeff_zero]
                rw [show n + (i + 1 + 1 - 1 - j) = n + (i - j) + 1 by omega]
                refine ⟨fun m hm => ?_, ?_⟩
                · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                  rw [hco, A1 (m'+1) (by omega), A1 m' (by omega), B (m'+1) (by omega),
                    hχc (m'+1) (by omega)]; ring
                · rw [hco, A1 _ (by omega), A2, B _ (by omega), hχc _ (by omega),
                    Finset.prod_Ico_succ_top (by omega : j + 1 ≤ i + 1)]; ring
              · -- j = i + 1
                subst h'
                have hW : W (i+2) = χ * Polynomial.C (f (i+1)) := by
                  rw [hrec, ih1.1 le_rfl, ih0.1 (by omega), mul_zero, mul_zero, sub_zero, zero_add]
                rw [hW, show n + (i + 1 + 1 - 1 - (i + 1)) = n by omega]
                refine ⟨fun m hm => ?_, ?_⟩
                · rw [Polynomial.coeff_mul_C, hχc m hm, zero_mul]
                · rw [Polynomial.coeff_mul_C, hχn, Finset.Ico_self, Finset.prod_empty]; ring
        have ORTH : ∀ a c : ℕ → ℝ, (∀ i < n, a i ≠ 0) → (∀ i, 0 < i → i < n → r0 ⬝ᵥ ρ a c i = 0) →
            ρ a c n = 0 → ∀ kk i, kk < i → i ≤ n → ρ a c i ⬝ᵥ ((A ^ kk) *ᵥ r0) = 0 := by
          intro a c ha hm hn kk
          induction kk with
          | zero =>
            intro i hi hin
            rcases lt_or_eq_of_le hin with h | h
            · rw [pow_zero, one_mulVec, dotProduct_comm]
              exact hm i hi h
            · rw [h, hn, zero_dotProduct]
          | succ kk ih =>
            intro i hi hin
            rcases lt_or_eq_of_le hin with h | h
            · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
              have key : a (j+1) • (A *ᵥ ρ a c (j+1)) =
                  (1 + c (j+1)) • ρ a c (j+1) - c (j+1) • ρ a c j - ρ a c (j+2) := by
                rw [ρrec a c j]; abel
              have e1 : ρ a c (j+1) ⬝ᵥ (A ^ (kk+1) *ᵥ r0) = (A *ᵥ ρ a c (j+1)) ⬝ᵥ (A ^ kk *ᵥ r0) := by
                rw [pow_succ', ← mulVec_mulVec, hsym, dotProduct_comm]
              have h3 : a (j+1) * (ρ a c (j+1) ⬝ᵥ (A ^ (kk+1) *ᵥ r0)) = 0 := by
                rw [e1, ← smul_eq_mul, ← smul_dotProduct, key, sub_dotProduct, sub_dotProduct,
                  smul_dotProduct, smul_dotProduct, ih (j+1) (by omega) (by omega),
                  ih j (by omega) (by omega), ih (j+2) (by omega) (by omega)]
                simp
              exact (mul_eq_zero.mp h3).resolve_left (ha (j+1) h)
            · rw [h, hn, zero_dotProduct]
        have UNIQR : ∀ a c a' c' : ℕ → ℝ,
            (∀ kk i, kk < i → i ≤ n → ρ a c i ⬝ᵥ ((A ^ kk) *ᵥ r0) = 0) →
            (∀ kk i, kk < i → i ≤ n → ρ a' c' i ⬝ᵥ ((A ^ kk) *ᵥ r0) = 0) →
            ∀ i ≤ n, (cfConv a c i).2 = (cfConv a' c' i).2 := by
          intro a c a' c' h1 h2 i hi
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · rfl
          obtain ⟨D, hD⟩ : ∃ D, D = (cfConv a c i).2 - (cfConv a' c' i).2 := ⟨_, rfl⟩
          have hD0 : D.coeff 0 = 0 := by
            rw [Polynomial.coeff_zero_eq_eval_zero, hD, Polynomial.eval_sub, cf0, cf0, sub_self]
          have hDX : D = Polynomial.X * Polynomial.divX D := by
            have := Polynomial.X_mul_divX_add D
            rw [hD0, map_zero, add_zero] at this
            exact this.symm
          have hDdeg : D.natDegree ≤ i := by
            rw [hD]
            exact (Polynomial.natDegree_sub_le _ _).trans (max_le (cfNat _ _ _) (cfNat _ _ _))
          have hSdeg : (Polynomial.divX D).natDegree < i := by
            rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; omega
          obtain ⟨v, hv⟩ : ∃ v, v = Polynomial.aeval A (Polynomial.divX D) *ᵥ r0 := ⟨_, rfl⟩
          have e : ρ a c i - ρ a' c' i = A *ᵥ v := by
            show Polynomial.aeval A (cfConv a c i).2 *ᵥ r0 - Polynomial.aeval A (cfConv a' c' i).2 *ᵥ r0 = _
            rw [← sub_mulVec, ← map_sub, ← hD, hDX, map_mul, Polynomial.aeval_X, ← mulVec_mulVec, hv]
          have hvsum : v = ∑ kk ∈ Finset.range i, (Polynomial.divX D).coeff kk • (A ^ kk *ᵥ r0) := by
            rw [hv, Polynomial.aeval_eq_sum_range' hSdeg, Matrix.sum_mulVec]
            exact Finset.sum_congr rfl (fun kk _ => smul_mulVec _ _ _)
          have hz : (A *ᵥ v) ⬝ᵥ v = 0 := by
            rw [← e]
            conv_lhs => rw [hvsum]
            rw [dotProduct_sum]
            refine Finset.sum_eq_zero (fun kk hk => ?_)
            have hk' := Finset.mem_range.mp hk
            rw [dotProduct_smul, sub_dotProduct, h1 kk i hk' hi, h2 kk i hk' hi, sub_zero, smul_zero]
          have hv0 : v = 0 := by
            by_contra hne
            have := hposA v hne
            rw [dotProduct_comm, hz] at this
            exact lt_irrefl _ this
          have hS : Polynomial.divX D = 0 := KRYc _ (lt_of_lt_of_le hSdeg hi) (by rw [← hv, hv0])
          rw [hS, mul_zero, hD] at hDX
          exact sub_eq_zero.mp hDX
        have COEF : ∀ a c a' c' : ℕ → ℝ, (∀ i < n, a i ≠ 0) →
            (∀ i ≤ n, (cfConv a c i).2 = (cfConv a' c' i).2) →
            (∀ i < n, a i = a' i) ∧ (∀ i, 0 < i → i < n → c i = c' i) := by
          clear * - cfDeg cfLead cfrec
          intro a c a' c' ha hR
          have hP : ∀ i < n, ∏ l ∈ Finset.range i, (-a l) ≠ 0 := fun i hi =>
            Finset.prod_ne_zero_iff.mpr (fun l hl => neg_ne_zero.mpr (ha l (by
              have := Finset.mem_range.mp hl; omega)))
          have hPP : ∀ i ≤ n, ∏ l ∈ Finset.range i, (-a l) = ∏ l ∈ Finset.range i, (-a' l) := by
            intro i hi; rw [← cfLead, ← cfLead, hR i hi]
          have hA : ∀ i < n, a i = a' i := by
            intro i hi
            have e := hPP (i+1) hi
            rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hPP i hi.le] at e
            have := mul_left_cancel₀ (hP i hi) e
            linarith
          refine ⟨hA, fun i hi hin => ?_⟩
          obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          have hco : ∀ (a c : ℕ → ℝ), ((cfConv a c (i+2)).2).coeff (i+1) =
              (1 + c (i+1)) * ((cfConv a c (i+1)).2).coeff (i+1)
                - a (i+1) * ((cfConv a c (i+1)).2).coeff i := by
            intro a c
            rw [cfrec]
            dsimp only
            rw [sub_mul, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
              cfDeg a c i (i+1) (by omega), mul_zero, sub_zero]
          have e := hco a c
          rw [hR (i+2) (by omega), hco a' c', ← hR (i+1) (by omega), cfLead,
            ← hA (i+1) hin] at e
          have hL := hP (i+1) hin
          have : (c' (i+1) - c (i+1)) * ∏ l ∈ Finset.range (i+1), (-a l) = 0 := by linear_combination e
          have := (mul_eq_zero.mp this).resolve_right hL
          linarith
        -- the cg process
        set a₀ : ℕ → ℝ := fun i => cgAlpha A (cgIter A k x₀ i) with ha₀def
        set c₀ : ℕ → ℝ := cgCoeffC A k x₀ with hc₀def
        have CG : (∀ i ≤ n, ρ a₀ c₀ i = (cgIter A k x₀ i).r) ∧ (∀ i < n, (cgIter A k x₀ i).r ≠ 0) ∧
            (∀ i < n, a₀ i ≠ 0) ∧ (cgIter A k x₀ n).r = 0 ∧
            (∀ i, 0 < i → i ≤ n → r0 ⬝ᵥ (cgIter A k x₀ i).r = 0) := by
          suffices key : ∀ (R P : ℕ → Fin n → ℝ) (β : ℕ → ℝ), R 0 = r0 → P 0 = r0 →
              (∀ i, a₀ i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
              (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
              (∀ i, R (i+1) = R i - a₀ i • (A *ᵥ P i)) →
              (∀ i, P (i+1) = R (i+1) + β i • P i) →
              (∀ i, c₀ (i+1) = β i * a₀ (i+1) / a₀ i) →
              (∀ i ≤ n, ρ a₀ c₀ i = R i) ∧ (∀ i < n, R i ≠ 0) ∧ (∀ i < n, a₀ i ≠ 0) ∧ R n = 0 ∧
              (∀ i, 0 < i → i ≤ n → r0 ⬝ᵥ R i = 0) by
            exact key (fun i => (cgIter A k x₀ i).r) (fun i => (cgIter A k x₀ i).p)
              (fun i => (cgIter A k x₀ (i+1)).r ⬝ᵥ (cgIter A k x₀ (i+1)).r /
                ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r))
              rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          intro R P β hR0 hP0 hα hβ hRs hPs hc
          have hRP0 : ∀ i, R i = 0 → P i = 0 := by
            intro i hi
            cases i with
            | zero => rw [hP0, ← hR0, hi]
            | succ i => rw [hPs, hβ, hi]; simp
          have hαP : ∀ i, a₀ i = 0 → P i = 0 := by
            intro i hi
            rw [hα, div_eq_zero_iff] at hi
            rcases hi with hi | hi
            · exact hRP0 i (hzero _ hi)
            · by_contra hne
              exact (hposA _ hne).ne' hi
          have hQ : ∀ i, (∀ j < i, R i ⬝ᵥ P j = 0 ∧ R i ⬝ᵥ R j = 0 ∧ P i ⬝ᵥ (A *ᵥ P j) = 0) ∧
              R i ⬝ᵥ P i = R i ⬝ᵥ R i := by
            intro i
            induction i with
            | zero => exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [hP0, hR0]⟩
            | succ i ih =>
              obtain ⟨ih1, ih2⟩ := ih
              have hii : R (i+1) ⬝ᵥ P i = 0 := by
                by_cases hp : P i = 0
                · rw [hp]; simp
                · have hpp := hposA _ hp
                  rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ih2, hα]
                  simp only [smul_eq_mul]
                  field_simp
                  ring
              have ha : ∀ j < i + 1, R (i+1) ⬝ᵥ P j = 0 := by
                intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
                · rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ← hsym,
                    (ih1 j hj).1, (ih1 j hj).2.2]
                  simp
                · rw [hj]; exact hii
              have hb : ∀ j < i + 1, R (i+1) ⬝ᵥ R j = 0 := by
                intro j hj
                cases j with
                | zero => rw [hR0, ← hP0]; exact ha 0 hj
                | succ j =>
                  have e : R (j+1) = P (j+1) - β j • P j := by rw [hPs]; abel
                  rw [e, dotProduct_sub, dotProduct_smul, ha _ hj, ha j (by omega)]
                  simp
              have hRA' : ∀ j < i, R (i+1) ⬝ᵥ (A *ᵥ P j) = 0 := by
                intro j hj
                by_cases h0 : a₀ j = 0
                · rw [hαP j h0]; simp
                · have e : a₀ j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                  have : a₀ j * (R (i+1) ⬝ᵥ (A *ᵥ P j)) = 0 := by
                    rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega),
                      hb (j+1) (by omega)]
                    simp
                  rcases mul_eq_zero.mp this with h1 | h1
                  · exact absurd h1 h0
                  · exact h1
              refine ⟨fun j hj => ⟨ha j hj, hb j hj, ?_⟩, ?_⟩
              · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
                · rw [hPs, add_dotProduct, smul_dotProduct, hRA' j hj, (ih1 j hj).2.2]; simp
                · subst hj
                  by_cases h0 : a₀ j = 0
                  · rw [hαP j h0]; simp
                  · have e : a₀ j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                    have h1 : a₀ j * (R (j+1) ⬝ᵥ (A *ᵥ P j)) = - (R (j+1) ⬝ᵥ R (j+1)) := by
                      rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega)]
                      simp
                    have hp : P j ≠ 0 := by
                      intro hp; apply h0; rw [hα, hp]; simp
                    have hpp := hposA _ hp
                    have hrr : R j ⬝ᵥ R j ≠ 0 := by
                      intro hr; apply h0; rw [hα, hr]; simp
                    rw [hPs, add_dotProduct, smul_dotProduct, hβ, smul_eq_mul]
                    rw [hα] at h1
                    field_simp at h1 ⊢
                    linear_combination h1
              · rw [hPs, dotProduct_add, dotProduct_smul, hii]; simp
          have hane : ∀ i, R i ≠ 0 → a₀ i ≠ 0 := by
            intro i hr
            have hrr : R i ⬝ᵥ R i ≠ 0 := fun h => hr (hzero _ h)
            have hp : P i ≠ 0 := by
              intro hp; apply hrr; rw [← (hQ i).2, hp, dotProduct_zero]
            rw [hα]
            exact div_ne_zero hrr (hposA _ hp).ne'
          have h3 : ∀ i, a₀ i ≠ 0 → R (i+2) = (1 + c₀ (i+1)) • R (i+1) - a₀ (i+1) • (A *ᵥ R (i+1))
              - c₀ (i+1) • R i := by
            intro i hai
            have e1 : A *ᵥ P i = (a₀ i)⁻¹ • (R i - R (i+1)) := by
              rw [hRs i, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hai, one_smul]
            rw [hRs (i+1), hPs i, mulVec_add, mulVec_smul, e1, hc i]
            module
          have hρR : ∀ i, (i ≤ n → ρ a₀ c₀ i = R i) ∧ (i + 1 ≤ n → ρ a₀ c₀ (i+1) = R (i+1)) := by
            intro i
            induction i with
            | zero =>
              refine ⟨fun _ => by rw [ρ0, hR0], fun _ => by rw [ρ1, hRs 0, hR0, hP0]⟩
            | succ i ih =>
              refine ⟨ih.2, fun hi => ?_⟩
              have hi0 : ρ a₀ c₀ i = R i := ih.1 (by omega)
              have hi1 : ρ a₀ c₀ (i+1) = R (i+1) := ih.2 (by omega)
              have hne : R i ≠ 0 := by
                rw [← hi0]
                exact KRYa _ (lt_of_le_of_lt (cfNat _ _ i) (by omega)) (cf0 _ _ i)
              rw [ρrec, hi0, hi1, h3 i (hane i hne)]
          have hRne : ∀ i < n, R i ≠ 0 := by
            intro i hi
            rw [← (hρR i).1 hi.le]
            exact KRYa _ (lt_of_le_of_lt (cfNat _ _ i) hi) (cf0 _ _ i)
          have horth : ∀ i j, i ≠ j → R i ⬝ᵥ R j = 0 := by
            intro i j hij
            rcases Nat.lt_or_gt_of_ne hij with h | h
            · rw [dotProduct_comm]; exact ((hQ j).1 i h).2.1
            · exact ((hQ i).1 j h).2.1
          refine ⟨fun i hi => (hρR i).1 hi, hRne, fun i hi => hane i (hRne i hi), ?_, ?_⟩
          · by_contra hRn
            have hne : ∀ i : Fin (n+1), R i ≠ 0 := by
              intro i
              rcases Nat.lt_or_ge (i : ℕ) n with h | h
              · exact hRne i h
              · rw [show (i : ℕ) = n by omega]; exact hRn
            have hli : LinearIndependent ℝ (fun i : Fin (n+1) => R i) := by
              rw [linearIndependent_iff']
              intro s g hs i hi
              have := congrArg (fun v => v ⬝ᵥ R i) hs
              simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at this
              rw [Finset.sum_eq_single i] at this
              · exact (mul_eq_zero.mp this).resolve_right (fun h => hne i (hzero _ h))
              · intro j _ hji
                rw [horth j i (fun h => hji (Fin.ext h)), mul_zero]
              · intro h; exact absurd hi h
            have := hli.fintype_card_le_finrank
            rw [Fintype.card_fin, Module.finrank_fin_fun] at this
            omega
          · intro i hi _
            rw [← hR0, dotProduct_comm]; exact horth i 0 (by omega)
        obtain ⟨CGρ, CGne, CGa, CGn, CGm⟩ := CG
        have ρn0 : ρ a₀ c₀ n = 0 := by rw [CGρ n le_rfl, CGn]
        have Zcg : Z a₀ c₀ (a₀ 0 * (r0 ⬝ᵥ r0)) n = 0 := by
          have TR := TRI a₀ c₀ (fun j => if j = 0 then 0 else -(a₀ j) * (r0 ⬝ᵥ ρ a₀ c₀ j))
            (Z a₀ c₀ (a₀ 0 * (r0 ⬝ᵥ r0))) (Z0 _ _ _) (by rw [Z1, sub_self, if_pos rfl])
            (fun i => by rw [Zrec, if_neg (Nat.succ_ne_zero i)]) n (fun l hl => by
              by_cases h0 : l = 0
              · rw [if_pos h0]
              · rw [if_neg h0, CGρ l hl.le, CGm l (Nat.pos_of_ne_zero h0) hl.le, mul_zero]) n
          exact TR.1 le_rfl
        have ORTHcg := ORTH a₀ c₀ CGa (fun i hi hin => by rw [CGρ i hin.le]; exact CGm i hi hin.le) ρn0
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact KRYb _ (cfNat _ _ n) (cf0 _ _ n) ρn0
        · have h := Zcg
          simp only [hZdef, ρn0, T0, sub_zero] at h
          rw [mul_comm]; exact sub_eq_zero.mp h
        · intro i hi
          have h1 := CGa i (by omega)
          have h2 := CGa (i+1) hi
          have hr : (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r ≠ 0 := fun h => CGne i (by omega) (hzero _ h)
          have e : c₀ (i+1) = (cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r /
              ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) * a₀ (i+1) / a₀ i := rfl
          show _ = c₀ (i+1) * a₀ i / a₀ (i+1)
          rw [e]
          field_simp
        · intro hn
          unfold cgBeta
          rw [Nat.sub_add_cancel hn, CGn]; simp
        · intro a c κ ha H
          have hZn : Z a c κ n = - T (ρ a c n) := by
            simp only [hZdef]; rw [mul_comm (cfConv a c n).2, H]; ring
          have hdvd : ∀ i, χ ∣ Z a c κ i ∧ χ ∣ Z a c κ (i+1) := by
            intro i
            induction i with
            | zero => rw [Z0, Z1]; exact ⟨dvd_zero _, dvd_mul_right _ _⟩
            | succ i ih =>
              refine ⟨ih.2, ?_⟩
              rw [Zrec]
              exact dvd_add (dvd_sub (dvd_mul_of_dvd_right ih.2 _) (dvd_mul_of_dvd_right ih.1 _))
                (dvd_mul_right _ _)
          have hρn : ρ a c n = 0 := by
            obtain ⟨g, hg⟩ := (hdvd n).1
            rw [expand (ρ a c n)]
            refine Finset.sum_eq_zero (fun j _ => ?_)
            have : (T (ρ a c n)).eval (lam j) = 0 := by
              have : T (ρ a c n) = -(χ * g) := by rw [← hg, hZn, neg_neg]
              rw [this, Polynomial.eval_neg, Polynomial.eval_mul, hχroot]; simp
            rw [Tev _ _ this, zero_smul]
          have hZn0 : Z a c κ n = 0 := by rw [hZn, hρn, T0, neg_zero]
          set f : ℕ → ℝ := fun j => if j = 0 then κ - a 0 * (r0 ⬝ᵥ r0)
            else -(a j) * (r0 ⬝ᵥ ρ a c j) with hfdef
          have TR := TRI a c f (Z a c κ) (Z0 a c κ) (by rw [Z1]; simp [hfdef])
            (fun i => by rw [Zrec]; simp [hfdef])
          have hf : ∀ j < n, f j = 0 := by
            intro j
            induction j using Nat.strong_induction_on with
            | _ j ihj =>
              intro hj
              have := ((TR j (fun l hl => ihj l hl (by omega)) n).2 hj).2
              rw [hZn0, Polynomial.coeff_zero] at this
              have hprod : ∏ l ∈ Finset.Ico (j+1) n, (-a l) ≠ 0 :=
                Finset.prod_ne_zero_iff.mpr (fun l hl => neg_ne_zero.mpr (ha l (Finset.mem_Ico.mp hl).2))
              exact (mul_eq_zero.mp this.symm).resolve_right hprod
          have hm : ∀ i, 0 < i → i < n → r0 ⬝ᵥ ρ a c i = 0 := by
            intro i hi hin
            have := hf i hin
            simp only [hfdef, if_neg (show i ≠ 0 by omega)] at this
            exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr (ha i hin))
          have ORTHac := ORTH a c ha hm hρn
          have hR := UNIQR a c a₀ c₀ ORTHac ORTHcg
          obtain ⟨hA1, hC1⟩ := COEF a c a₀ c₀ ha hR
          refine ⟨fun hn => ?_, hA1, hC1⟩
          have := hf 0 hn
          simp only [hfdef, if_pos rfl] at this
          rw [hA1 0 hn] at this
          linarith
