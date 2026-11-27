-- Prove2me | solution 1 for BicliqueSDP.Chain.Supplement.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:53.618105+00:00
-- url     : https://prove2.me/submissions/11fc7a6f-e794-4c11-a92d-27e782db0af3

import Definitions.Def_BicliqueSDP_Chain_Supplement_ProductFree
set_option autoImplicit false

open BicliqueSDP
open BicliqueSDP.Chain
open BicliqueSDP.Chain.Supplement

/-- Theorem A.2: the sharpened product-free density bound with its exact denominator. -/
theorem solution {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ) (k : ℕ) (hk : IsMinRepDim Γ k) (hA : IsProductFree A) :
    (A.card : ℝ) ≤ (Fintype.card Γ : ℝ) / (1 + (k : ℝ) ^ (1 / 3 : ℝ)) := by
      classical
      set n : ℝ := (Fintype.card Γ : ℝ) with hn_def
      set a : ℝ := (A.card : ℝ) with ha_def
      have hnpos : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
      have han : a ≤ n := by rw [ha_def, hn_def]; exact_mod_cast A.card_le_univ
      have ha0 : 0 ≤ a := by positivity
      set M : Matrix Γ Γ ℝ := Matrix.of fun y z => if z * y⁻¹ ∈ A then 1 else 0 with hM_def
      set J : Matrix Γ Γ ℝ := Matrix.of fun _ _ => 1 with hJ_def
      set S : Matrix Γ Γ ℝ := M.transpose * M - (a ^ 2 / n) • J with hS_def
      have hMapp : ∀ y z, M y z = if z * y⁻¹ ∈ A then 1 else 0 := fun y z => rfl
      have hsumA : ∑ x : Γ, (if x ∈ A then (1:ℝ) else 0) = a := by
        rw [Finset.sum_boole]; simp [ha_def]
      have hrow : ∀ y, ∑ z, M y z = a := by
        intro y
        rw [← hsumA]
        exact Fintype.sum_equiv (Equiv.mulRight y⁻¹) _ _ (fun z => by
          by_cases h : z * y⁻¹ ∈ A <;> simp [hMapp, h])
      have hcol : ∀ z, ∑ y, M y z = a := by
        intro z
        rw [← hsumA]
        exact Fintype.sum_equiv ((Equiv.inv Γ).trans (Equiv.mulLeft z)) _ _ (fun y => by simp [hMapp])
      have hMinv : ∀ g y z, M (y * g) (z * g) = M y z := by
        intro g y z; simp [hMapp, mul_inv_rev, mul_assoc]
      have hMsq : ∀ y z, M y z * M y z = M y z := by
        intro y z; rw [hMapp]; split_ifs <;> norm_num
      have hSapp : ∀ y z, S y z = (∑ w, M w y * M w z) - a ^ 2 / n := by
        intro y z; simp [hS_def, hJ_def, Matrix.mul_apply]
      have hSt : S.transpose = S := by
        ext y z; simp only [Matrix.transpose_apply, hSapp, mul_comm]
      have hSsymm : S.IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hSt]
      have hSinv : ∀ g y z, S (y * g) (z * g) = S y z := by
        intro g y z
        rw [hSapp, hSapp]
        congr 1
        exact (Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w => by simp [hMinv])).symm
      have hMv1 : M.mulVec (fun _ => (1:ℝ)) = fun _ => a := by
        ext y; simp [Matrix.mulVec, dotProduct, hrow]
      have h1M : ∀ x : Γ → ℝ, ∑ y, M.mulVec x y = a * ∑ y, x y := by
        intro x
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_mul, hcol]
      have hSmul : ∀ x : Γ → ℝ, S.mulVec x = M.transpose.mulVec (M.mulVec x) - (a ^ 2 / n * ∑ y, x y) • (fun _ => (1:ℝ)) := by
        intro x
        ext y
        simp [hS_def, hJ_def, Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
      have hS1 : S.mulVec (fun _ => (1:ℝ)) = 0 := by
        rw [hSmul, hMv1]
        ext y
        simp [Matrix.mulVec, dotProduct, hn_def]
        field_simp
        rw [← Finset.sum_mul, hcol]; ring
      have hSquad : ∀ x : Γ → ℝ, dotProduct x (S.mulVec x) = dotProduct (M.mulVec x) (M.mulVec x) - a ^ 2 / n * (∑ y, x y) ^ 2 := by
        intro x
        rw [hSmul, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_smul]
        simp [dotProduct, smul_eq_mul]
        ring
      have hSpsd : ∀ x : Γ → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
        intro x
        rw [hSquad]
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := M.mulVec x)
        rw [h1M] at hcs
        simp only [sq] at hcs
        have : a ^ 2 / n * (∑ y, x y) ^ 2 ≤ dotProduct (M.mulVec x) (M.mulVec x) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
          simp only [dotProduct, Finset.card_univ, ← hn_def] at hcs ⊢
          nlinarith [hcs]
        linarith
      have htrace : S.trace = n * a - a ^ 2 := by
        simp only [Matrix.trace, Matrix.diag, hSapp, Finset.sum_sub_distrib, hMsq]
        rw [Finset.sum_comm]
        simp [hrow, hn_def]
        field_simp
      -- spectral data
      obtain ⟨lam, v, hv1, hvexp, hvnorm, htr⟩ : ∃ (lam : Γ → ℝ) (v : Γ → Γ → ℝ),
          (∀ i, S.mulVec (v i) = lam i • v i) ∧ (∀ f : Γ → ℝ, f = ∑ i, dotProduct (v i) f • v i) ∧
          (∀ i, dotProduct (v i) (v i) = 1) ∧ S.trace = ∑ i, lam i := by
        refine ⟨hSsymm.eigenvalues, fun i => ⇑(hSsymm.eigenvectorBasis i),
          fun i => hSsymm.mulVec_eigenvectorBasis i, ?_, ?_, ?_⟩
        · intro f
          have := congrArg WithLp.ofLp ((hSsymm.eigenvectorBasis).sum_repr' (WithLp.toLp 2 f))
          simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_sum, WithLp.ofLp_smul, star_trivial] at this
          conv_lhs => rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dotProduct_comm]
        · intro i
          have h := (hSsymm.eigenvectorBasis).orthonormal.1 i
          have h2 : ‖hSsymm.eigenvectorBasis i‖ ^ 2 = 1 := by rw [h]; norm_num
          rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h2
          exact h2
        · simpa using hSsymm.trace_eq_sum_eigenvalues
      have hlam0 : ∀ i, 0 ≤ lam i := by
        intro i
        have := hSpsd (v i)
        rwa [hv1 i, dotProduct_smul, hvnorm i, smul_eq_mul, mul_one] at this
      have hmult : ∀ i, lam i ≠ 0 → (k : ℝ) ≤ ((Finset.univ.filter fun j => lam j = lam i).card : ℝ) := by
        intro i hi
        set μ := lam i with hμ
        let E : Submodule ℝ (Γ → ℝ) := Module.End.eigenspace (Matrix.toLin' S) μ
        have hmemE : ∀ f, f ∈ E ↔ S.mulVec f = μ • f := by
          intro f; simp [E, Matrix.toLin'_apply]
        let P : Γ → Module.End ℝ (Γ → ℝ) := fun g => LinearMap.funLeft ℝ ℝ (· * g)
        have hPapp : ∀ g f y, P g f y = f (y * g) := fun g f y => rfl
        have hPS : ∀ g f, S.mulVec (P g f) = P g (S.mulVec f) := by
          intro g f; ext y
          simp only [hPapp, Matrix.mulVec, dotProduct]
          exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun z => by simp [hSinv])
        have hPE : ∀ g, ∀ f ∈ E, P g f ∈ E := by
          intro g f hf
          rw [hmemE] at hf ⊢
          rw [hPS, hf, map_smul]
        let ρ : Γ →* Module.End ℝ E :=
          { toFun := fun g => (P g).restrict (hPE g)
            map_one' := by ext f y; simp [hPapp, LinearMap.restrict_apply]
            map_mul' := by intro g h; ext f y; simp [hPapp, LinearMap.restrict_apply, mul_assoc] }
        have hρapp : ∀ g (f : E) y, (ρ g f : Γ → ℝ) y = (f : Γ → ℝ) (y * g) := fun g f y => rfl
        have hnt : ∃ g, ρ g ≠ 1 := by
          by_contra hcon
          push Not at hcon
          have hwE : v i ∈ E := (hmemE _).2 (hv1 i)
          have hconst : v i = (v i 1) • (fun _ => (1:ℝ)) := by
            ext y
            have := congrArg (fun φ : Module.End ℝ E => ((φ ⟨v i, hwE⟩ : E) : Γ → ℝ) 1) (hcon y)
            simp only [hρapp, one_mul, Module.End.one_apply] at this
            simp [this]
          have h0 : μ • v i = 0 := by
            rw [← hv1 i, hconst, Matrix.mulVec_smul, hS1, smul_zero]
          rcases smul_eq_zero.1 h0 with h | h
          · exact hi h
          · have := hvnorm i; rw [h] at this; simp at this
        set d := Module.finrank ℝ E with hd
        let b := Module.finBasis ℝ E
        let ρC : Representation ℂ Γ (Fin d → ℂ) :=
          (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp
            (((algebraMap ℝ ℂ).mapMatrix : Matrix (Fin d) (Fin d) ℝ →+* _).toMonoidHom.comp
              ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ))
        have hρC : ∀ g, ρC g = 1 → ρ g = 1 := by
          intro g hg
          have h2 : (algebraMap ℝ ℂ).mapMatrix ((LinearMap.toMatrixAlgEquiv b) (ρ g)) = 1 := by
            have := congrArg (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).symm hg
            simpa [ρC] using this
          have h1 : (LinearMap.toMatrixAlgEquiv b) (ρ g) = 1 := by
            ext p q
            have := congrFun (congrFun h2 p) q
            by_cases hpq : p = q
            · subst hpq; simpa using this
            · simpa [Matrix.one_apply, hpq] using this
          exact (LinearMap.toMatrixAlgEquiv b).injective (h1.trans (map_one _).symm)
        have hkd : k ≤ d := by
          obtain ⟨g, hg⟩ := hnt
          exact hk.2 ⟨ρC, g, fun h => hg (hρC g h)⟩
        have hSv : ∀ j f, dotProduct (v j) (S.mulVec f) = lam j * dotProduct (v j) f := by
          intro j f
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSt, hv1, smul_dotProduct, smul_eq_mul]
        have hEle : E ≤ Submodule.span ℝ
            (((Finset.univ.filter fun j => lam j = lam i).image v : Finset (Γ → ℝ)) : Set (Γ → ℝ)) := by
          intro f hf
          rw [hmemE] at hf
          rw [hvexp f]
          have hc : ∀ j, dotProduct (v j) f * (lam j - μ) = 0 := by
            intro j
            have := hSv j f
            rw [hf, dotProduct_smul, smul_eq_mul] at this
            linarith
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => lam j = lam i)]
          rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => ¬ lam j = lam i) (fun j hj => by
            have hj' := (Finset.mem_filter.1 hj).2
            have : dotProduct (v j) f = 0 := by
              rcases mul_eq_zero.1 (hc j) with h | h
              · exact h
              · exact absurd (by linarith) hj'
            rw [this, zero_smul]), add_zero]
          refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          exact Finset.mem_coe.2 (Finset.mem_image_of_mem v hj)
        have hdc : d ≤ (Finset.univ.filter fun j => lam j = lam i).card :=
          (Submodule.finrank_mono hEle).trans ((finrank_span_finset_le_card _).trans Finset.card_image_le)
        exact_mod_cast hkd.trans hdc
      have hlamk : ∀ i, (k : ℝ) * lam i ≤ n * a - a ^ 2 := by
        intro i
        by_cases hi : lam i = 0
        · rw [hi, mul_zero]; nlinarith
        · have h1 := hmult i hi
          calc (k:ℝ) * lam i ≤ ((Finset.univ.filter fun j => lam j = lam i).card : ℝ) * lam i :=
                mul_le_mul_of_nonneg_right h1 (hlam0 i)
          _ = ∑ j ∈ Finset.univ.filter (fun j => lam j = lam i), lam j := by
                rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.1 hj).2)]; simp
          _ ≤ ∑ j, lam j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun j _ _ => hlam0 j)
          _ = _ := by rw [← htr, htrace]
      have hkpos : 0 < k := by
        obtain ⟨ρ, g, hg⟩ := hk.1
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; exact absurd (LinearMap.ext fun x => Subsingleton.elim _ _) hg
        · exact h0
      have hquad : ∀ f : Γ → ℝ, (k : ℝ) * dotProduct f (S.mulVec f) ≤ (n * a - a ^ 2) * dotProduct f f := by
        intro f
        have hSf : S.mulVec f = ∑ i, (dotProduct (v i) f * lam i) • v i := by
          conv_lhs => rw [hvexp f]
          simp [Matrix.mulVec_sum, Matrix.mulVec_smul, hv1, smul_smul]
        have e1 : dotProduct f (S.mulVec f) = ∑ i, lam i * (dotProduct (v i) f) ^ 2 := by
          rw [hSf, dotProduct_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dotProduct_smul, smul_eq_mul, dotProduct_comm f (v i)]; ring
        have e2 : dotProduct f f = ∑ i, (dotProduct (v i) f) ^ 2 := by
          rw [show dotProduct f f = dotProduct (∑ i, dotProduct (v i) f • v i) f by rw [← hvexp f]]
          rw [sum_dotProduct]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_dotProduct, smul_eq_mul]; ring
        rw [e1, e2, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have := mul_le_mul_of_nonneg_right (hlamk i) (sq_nonneg (dotProduct (v i) f))
        linarith
      have hcube : a ^ 3 * k ≤ (n - a) ^ 3 := by
        rcases eq_or_lt_of_le ha0 with ha | ha
        · rw [← ha]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero]; positivity
        set χ : Γ → ℝ := fun y => if y ∈ A then 1 else 0 with hχ
        set f : Γ → ℝ := fun y => χ y - a / n with hf
        have hχsum : ∑ y, χ y = a := hsumA
        have hfeq : f = χ - (a / n) • (fun _ => (1:ℝ)) := by ext y; simp [hf]
        have hfsum : ∑ y, f y = 0 := by
          simp only [hf, Finset.sum_sub_distrib, hχsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
          field_simp; ring
        have hff : dotProduct f f = a - a ^ 2 / n := by
          have : ∀ y, f y * f y = χ y * (1 - 2 * (a / n)) + (a / n) ^ 2 := by
            intro y; simp only [hf, hχ]; split_ifs <;> ring
          simp only [dotProduct, this, Finset.sum_add_distrib, ← Finset.sum_mul, hχsum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, ← hn_def]
          field_simp; ring
        have hχMχ : dotProduct χ (M.mulVec χ) = 0 := by
          simp only [dotProduct, Matrix.mulVec]
          refine Finset.sum_eq_zero fun y _ => ?_
          by_cases hy : y ∈ A
          · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun z _ => ?_)
            rw [hMapp]; simp only [hχ]
            by_cases h1 : z * y⁻¹ ∈ A
            · have := hA _ h1 _ hy
              simp only [inv_mul_cancel_right] at this
              simp [h1, this]
            · simp [h1]
          · simp [hχ, hy]
        have e1 : dotProduct χ (fun _ : Γ => a) = a * a := by
          simp only [dotProduct, ← Finset.sum_mul, hχsum]
        have e2 : dotProduct (fun _ : Γ => (1:ℝ)) (M.mulVec χ) = a * a := by
          simp only [dotProduct, one_mul, h1M, hχsum]
        have e3 : dotProduct (fun _ : Γ => (1:ℝ)) (fun _ : Γ => a) = n * a := by
          simp [dotProduct, hn_def]
        have hfMf : dotProduct f (M.mulVec f) = - a ^ 3 / n := by
          rw [hfeq, Matrix.mulVec_sub, Matrix.mulVec_smul, hMv1]
          simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, e1, e2, e3, hχMχ]
          field_simp; ring
        have hfS : dotProduct f (S.mulVec f) = dotProduct (M.mulVec f) (M.mulVec f) := by
          rw [hSquad, hfsum]; ring
        have hcs : (dotProduct f (M.mulVec f)) ^ 2 ≤ dotProduct f f * dotProduct (M.mulVec f) (M.mulVec f) := by
          simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (M.mulVec f)
        have hq := hquad f
        have hF : a - a ^ 2 / n = a * (n - a) / n := by field_simp
        have hF0 : 0 ≤ a - a ^ 2 / n := by
          rw [hF]; apply div_nonneg _ hnpos.le; nlinarith
        have h1 : (a ^ 3 / n) ^ 2 * k ≤ (a - a ^ 2 / n) ^ 2 * (n * a - a ^ 2) := by
          rw [hfMf] at hcs
          calc (a ^ 3 / n) ^ 2 * k = (- a ^ 3 / n) ^ 2 * k := by ring
          _ ≤ (a - a ^ 2 / n) * dotProduct (M.mulVec f) (M.mulVec f) * k := by
                rw [← hff]; exact mul_le_mul_of_nonneg_right hcs (by positivity)
          _ = (a - a ^ 2 / n) * (k * dotProduct (M.mulVec f) (M.mulVec f)) := by ring
          _ ≤ (a - a ^ 2 / n) * ((n * a - a ^ 2) * (a - a ^ 2 / n)) :=
                mul_le_mul_of_nonneg_left (by rw [← hfS, ← hff]; exact hq) hF0
          _ = _ := by ring
        rw [hF] at h1
        have h2 : a ^ 3 * (a ^ 3 * k) / n ^ 2 ≤ a ^ 3 * (n - a) ^ 3 / n ^ 2 := by
          have e : (a * (n - a) / n) ^ 2 * (n * a - a ^ 2) = a ^ 3 * (n - a) ^ 3 / n ^ 2 := by ring
          have e' : (a ^ 3 / n) ^ 2 * k = a ^ 3 * (a ^ 3 * k) / n ^ 2 := by ring
          linarith
        have h3 := (div_le_div_iff_of_pos_right (by positivity)).1 h2
        exact le_of_mul_le_mul_left h3 (pow_pos ha 3)
      set t : ℝ := (k:ℝ) ^ (1/3:ℝ) with ht
      have ht0 : 0 ≤ t := by positivity
      have ht3 : t ^ 3 = k := by
        rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hat : a * t ≤ n - a := by
        have h1 : (a*t)^3 ≤ (n-a)^3 := by rw [mul_pow, ht3]; exact hcube
        exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith) h1
      rw [le_div_iff₀ (by positivity)]; nlinarith
