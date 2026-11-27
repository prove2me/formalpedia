-- Prove2me | solution 1 for BicliqueSDP.Chain.Supplement.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:37.09116+00:00
-- url     : https://prove2.me/submissions/64599ee3-a0a8-417b-af2c-af7a1078ebba

import Definitions.Def_BicliqueSDP_Chain_Supplement_ProductFree
set_option autoImplicit false

open BicliqueSDP
open BicliqueSDP.Chain
open BicliqueSDP.Chain.Supplement

/-- Lemma A.1, including the exact factor n-|A| and the full adjacency spectrum. -/
theorem solution {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ) (k : ℕ) (hk : IsMinRepDim Γ k) (hA : IsProductFree A) :
    lambda2 A ≤ Real.sqrt ((A.card : ℝ) * ((Fintype.card Γ : ℝ) - A.card) / k) := by
      classical
      open scoped BigOperators ComplexOrder in
      open Matrix in
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k = 0 := by omega
        obtain ⟨ρ, g, hg⟩ := hk.1
        subst k
        exact hg (Subsingleton.elim _ _)
      have spectral_bound : ∀ (M : Matrix Γ Γ ℂ), M.PosSemidef →
          (∀ u w g, M (u * g) (w * g) = M u w) →
          (∀ u, ∑ w, M u w = 0) →
          ∀ μ : ℝ, 0 < μ → (Module.End.HasEigenvalue M.toEuclideanLin (μ : ℂ)) →
          (k : ℝ) * μ ≤ M.trace.re := by
        intro M hM hinv hzero μ hμ heig
        let T := M.toEuclideanLin
        let W := Module.End.eigenspace T (μ : ℂ)
        let ρ : Representation ℂ Γ (EuclideanSpace ℂ Γ) :=
          { toFun := fun g =>
              { toFun := fun x => WithLp.toLp 2 (fun u => x (u * g))
                map_add' := by intros; rfl
                map_smul' := by intros; rfl }
            map_one' := by ext x u; simp
            map_mul' := by
              intro g h; ext x u
              change x (u * (g * h)) = x ((u * g) * h)
              rw [mul_assoc] }
        have hρ (g : Γ) (x : EuclideanSpace ℂ Γ) (u : Γ) : ρ g x u = x (u * g) := rfl
        have hcomm (g : Γ) (x : EuclideanSpace ℂ Γ) : T (ρ g x) = ρ g (T x) := by
          apply PiLp.ext
          intro u
          change (∑ w, M u w * x (w * g)) = ∑ w, M (u * g) w * x w
          exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w => by change M u w * x (w * g) = M (u * g) (w * g) * x (w * g); rw [hinv])
        have hstable : ∀ g, W ≤ W.comap (ρ g) := by
          intro g x hx
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff]
          rw [hcomm, Module.End.mem_eigenspace_iff.mp hx, map_smul]
        let σ := ρ.subrepresentation W hstable
        let e := (Module.finBasis ℂ W).equivFun
        let τ : Representation ℂ Γ (Fin (Module.finrank ℂ W) → ℂ) :=
          e.conjRingEquiv.toMonoidHom.comp σ
        have hnontriv : ∃ g, τ g ≠ 1 := by
          by_contra h
          have ht : ∀ g, τ g = 1 := by simpa using h
          obtain ⟨x, hx, hx0⟩ := heig.exists_hasEigenvector
          have hfix (g : Γ) : ρ g x = x := by
            have hh := congrArg (fun f => f (e ⟨x, hx⟩)) (ht g)
            have hh' : e (σ g ⟨x, hx⟩) = e ⟨x, hx⟩ := by simpa [τ, LinearEquiv.conjRingEquiv] using hh
            exact congrArg Subtype.val (e.injective hh')
          have hc (u : Γ) : x u = x 1 := by
            have := congrArg (fun y : EuclideanSpace ℂ Γ => y 1) (hfix u)
            simpa [hρ] using this
          have hTx : T x = 0 := by
            apply PiLp.ext
            intro u
            change (∑ w, M u w * x w) = 0
            simp_rw [hc]
            rw [← Finset.sum_mul, hzero, zero_mul]
          have hxeq := Module.End.mem_eigenspace_iff.mp hx
          rw [hTx] at hxeq
          have : x = 0 := (smul_eq_zero.mp hxeq.symm).resolve_left (by exact_mod_cast ne_of_gt hμ)
          exact hx0 this
        have hdim : k ≤ Module.finrank ℂ W := hk.2 ⟨τ, hnontriv⟩
        have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1
        have hcard := hs.card_filter_eigenvalues_eq finrank_euclideanSpace (μ : ℂ)
        have hsum : (∑ i, hs.eigenvalues finrank_euclideanSpace i) = M.trace.re := by
          rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hM.1]
          simp only [Complex.re_sum]
          symm
          exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card Γ))).symm _
        have hnonneg (i : Fin (Fintype.card Γ)) : 0 ≤ hs.eigenvalues finrank_euclideanSpace i := by
          let e : Fin (Fintype.card Γ) ≃ Γ := Fintype.equivOfCardEq (Fintype.card_fin _)
          simpa only [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀,
            Equiv.symm_apply_apply, e] using hM.eigenvalues_nonneg (e i)
        have hsub : (∑ i ∈ Finset.univ.filter (fun i => hs.eigenvalues finrank_euclideanSpace i = (μ : ℂ)),
            hs.eigenvalues finrank_euclideanSpace i) ≤ ∑ i, hs.eigenvalues finrank_euclideanSpace i := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; apply hnonneg)
        have hfilter : (∑ i ∈ Finset.univ.filter (fun i => hs.eigenvalues finrank_euclideanSpace i = (μ : ℂ)),
            hs.eigenvalues finrank_euclideanSpace i) = (Module.finrank ℂ W : ℝ) * μ := by
          rw [Finset.sum_congr rfl (fun i hi => Complex.ofReal_injective (Finset.mem_filter.mp hi).2)]
          simp only [Finset.sum_const, nsmul_eq_mul]
          congr 2
        rw [hfilter, hsum] at hsub
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hdim) hμ.le).trans hsub
      let a : ℝ := A.card
      let n : ℝ := Fintype.card Γ
      let p : ℝ := a / n
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Γ)
      have hcount (e : Γ ≃ Γ) : (∑ x, if e x ∈ A then (1 : ℝ) else 0) = a := by
        rw [e.sum_comp (fun x => if x ∈ A then (1 : ℝ) else 0)]
        simp [a]
      have hcountL (u : Γ) : (∑ v, if u * v ∈ A then (1 : ℝ) else 0) = a := hcount (Equiv.mulLeft u)
      have hcountR (v : Γ) : (∑ u, if u * v ∈ A then (1 : ℝ) else 0) = a := hcount (Equiv.mulRight v)
      let C : Matrix Γ Γ ℝ := fun u v => (if u * v ∈ A then 1 else 0) - p
      have hCrow (u : Γ) : ∑ v, C u v = 0 := by
        change (∑ v, ((if u * v ∈ A then (1 : ℝ) else 0) - p)) = 0
        rw [Finset.sum_sub_distrib, hcountL u]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change a - n * (a / n) = 0
        field_simp [hn.ne']
        <;> ring
      have hCcol (v : Γ) : ∑ u, C u v = 0 := by
        change (∑ u, ((if u * v ∈ A then (1 : ℝ) else 0) - p)) = 0
        rw [Finset.sum_sub_distrib, hcountR v]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change a - n * (a / n) = 0
        field_simp [hn.ne']
        <;> ring
      let B : Matrix Γ Γ ℂ := fun u v => (C u v : ℂ)
      let M := B * Bᴴ
      have hMpos : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose B
      have hMinv (u w g : Γ) : M (u * g) (w * g) = M u w := by
        change (∑ v, (C (u * g) v : ℂ) * star (C (w * g) v : ℂ)) =
          ∑ v, (C u v : ℂ) * star (C w v : ℂ)
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun v => by change (C (u * g) v : ℂ) * star (C (w * g) v : ℂ) = (C u (g * v) : ℂ) * star (C w (g * v) : ℂ); simp only [C, mul_assoc])
      have hMzero (u : Γ) : ∑ w, M u w = 0 := by
        change (∑ w, ∑ v, (C u v : ℂ) * star (C w v : ℂ)) = 0
        rw [Finset.sum_comm]
        simp only [Complex.star_def, Complex.conj_ofReal, ← Finset.mul_sum, ← Complex.ofReal_sum, hCcol, Complex.ofReal_zero,
          mul_zero, Finset.sum_const_zero]
      have hMtrace : M.trace.re = a * (n - a) := by
        have hrow (u : Γ) : ∑ v, C u v ^ 2 = (1 - 2 * p) * a + n * p ^ 2 := by
          have he (v : Γ) : C u v ^ 2 = (1 - 2 * p) * (if u * v ∈ A then 1 else 0) + p ^ 2 := by
            dsimp [C]; split_ifs <;> ring
          simp_rw [he]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcountL u]
          simp [n]
        change (∑ u, ∑ v, (C u v : ℂ) * star (C u v : ℂ)).re = a * (n - a)
        simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]
        simp only [← pow_two, hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change n * ((1 - 2 * (a / n)) * a + n * (a / n) ^ 2) = a * (n - a)
        field_simp [hn.ne']
        <;> ring
      have ha : 0 ≤ a := by dsimp [a]; positivity
      by_cases ht : lambda2 A ≤ 0
      · exact ht.trans (Real.sqrt_nonneg _)
      have htpos : 0 < lambda2 A := lt_of_not_ge ht
      let H := (cayleyAdj A).toEuclideanLin
      let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (cayleyAdj_hermitian A)
      let Q : Matrix Γ Γ ℝ := fun u v => if u * v ∈ A then 1 else 0
      have hQrow (u : Γ) : ∑ v, Q u v = a := hcountL u
      have hQcol (v : Γ) : ∑ u, Q u v = a := hcountR v
      have hleft (x : EuclideanSpace ℝ (Γ ⊕ Γ)) (u : Γ) :
          H x (Sum.inl u) = ∑ v, Q u v * x (Sum.inr v) := by
        simp [H, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, cayleyAdj, bipGraph, cayleyEdge, Q, ite_mul]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp_all
      have hright (x : EuclideanSpace ℝ (Γ ⊕ Γ)) (v : Γ) :
          H x (Sum.inr v) = ∑ u, Q u v * x (Sum.inl u) := by
        simp [H, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, cayleyAdj, bipGraph, cayleyEdge, Q, ite_mul]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp_all
      let L : EuclideanSpace ℝ (Γ ⊕ Γ) →ₗ[ℝ] ℝ :=
        { toFun := fun x => ∑ u, x (Sum.inl u)
          map_add' := by intros; simp [Finset.sum_add_distrib]
          map_smul' := by intros; simp [Finset.mul_sum] }
      let R : EuclideanSpace ℝ (Γ ⊕ Γ) →ₗ[ℝ] ℝ :=
        { toFun := fun x => ∑ u, x (Sum.inr u)
          map_add' := by intros; simp [Finset.sum_add_distrib]
          map_smul' := by intros; simp [Finset.mul_sum] }
      have hL (x : EuclideanSpace ℝ (Γ ⊕ Γ)) : L (H x) = a * R x := by
        change (∑ u, H x (Sum.inl u)) = a * ∑ v, x (Sum.inr v)
        simp_rw [hleft]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hQcol]
        rw [Finset.mul_sum]
      have hR (x : EuclideanSpace ℝ (Γ ⊕ Γ)) : R (H x) = a * L x := by
        change (∑ v, H x (Sum.inr v)) = a * ∑ u, x (Sum.inl u)
        simp_rw [hright]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hQrow]
        rw [Finset.mul_sum]
      have hmean (t : ℝ) (x : EuclideanSpace ℝ (Γ ⊕ Γ)) (he : H x = t • x)
          (ht : 0 < t) (hne : t ≠ a) : L x = 0 := by
        have h1 := hL x
        have h2 := hR x
        rw [he, map_smul, smul_eq_mul] at h1 h2
        have hz : (t - a) * (t + a) * L x = 0 := by
          linear_combination t * h1 + a * h2
        exact (mul_eq_zero.mp hz).resolve_left
          (mul_ne_zero (sub_ne_zero.mpr hne) (ne_of_gt (by linarith : 0 < t + a)))
      have hsize : 1 < Fintype.card (Γ ⊕ Γ) := by
        simp only [Fintype.card_sum]
        have : 0 < Fintype.card Γ := Fintype.card_pos
        omega
      let i0 : Fin (Fintype.card (Γ ⊕ Γ)) := ⟨0, by omega⟩
      let i1 : Fin (Fintype.card (Γ ⊕ Γ)) := ⟨1, hsize⟩
      let b := hs.eigenvectorBasis finrank_euclideanSpace
      let l := hs.eigenvalues finrank_euclideanSpace
      have hl1 : l i1 = lambda2 A := rfl
      have hl0 : lambda2 A ≤ l i0 := by
        rw [← hl1]
        exact hs.eigenvalues_antitone _ (by change (0 : ℕ) ≤ 1; omega)
      have he (i) : H (b i) = l i • b i := hs.apply_eigenvectorBasis _ i
      have hb0 (i) : b i ≠ 0 := b.orthonormal.ne_zero i
      have hex : ∃ (t : ℝ) (x : EuclideanSpace ℝ (Γ ⊕ Γ)),
          lambda2 A ≤ t ∧ 0 < t ∧ x ≠ 0 ∧ H x = t • x ∧ L x = 0 := by
        by_cases h0 : l i0 = a
        · by_cases h1 : l i1 = a
          · by_cases hL0 : L (b i0) = 0
            · exact ⟨l i0, b i0, hl0, htpos.trans_le hl0, hb0 _, he _, hL0⟩
            · let x := L (b i0) • b i1 - L (b i1) • b i0
              have hx0 : x ≠ 0 := by
                intro hx
                have hh := congrArg (fun y => inner ℝ (b i1) y) hx
                have hne : i1 ≠ i0 := by
                  intro heq
                  have hv := congrArg Fin.val heq
                  change (1 : ℕ) = 0 at hv
                  omega
                simp [x, inner_sub_right, inner_smul_right, b.inner_eq_ite, hne] at hh
                exact hL0 hh
              refine ⟨a, x, by simpa [h0] using hl0, by simpa [h0] using htpos.trans_le hl0, hx0, ?_, ?_⟩
              · simp only [x, map_sub, map_smul, he, h0, h1]
                module
              · simp [x, map_sub, map_smul, smul_eq_mul, mul_comm]
          · exact ⟨l i1, b i1, hl1.le, by rwa [hl1], hb0 _, he _, hmean _ _ (he _) (by rwa [hl1]) h1⟩
        · exact ⟨l i0, b i0, hl0, htpos.trans_le hl0, hb0 _, he _, hmean _ _ (he _) (htpos.trans_le hl0) h0⟩
      obtain ⟨t, x, htt, ht, hx0, hxe, hxL⟩ := hex
      have hxR : R x = 0 := by
        have hh := hR x
        rw [hxe, map_smul, smul_eq_mul, hxL, mul_zero] at hh
        exact (mul_eq_zero.mp hh).resolve_left ht.ne'
      have hcleft (u : Γ) : ∑ v, C u v * x (Sum.inr v) = t * x (Sum.inl u) := by
        calc
          _ = (∑ v, Q u v * x (Sum.inr v)) - p * R x := by
            simp only [C, Q, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, R, LinearMap.coe_mk, AddHom.coe_mk]
          _ = t * x (Sum.inl u) := by
            rw [hxR, mul_zero, sub_zero, ← hleft, hxe]
            rfl
      have hcright (v : Γ) : ∑ u, C u v * x (Sum.inl u) = t * x (Sum.inr v) := by
        calc
          _ = (∑ u, Q u v * x (Sum.inl u)) - p * L x := by
            simp only [C, Q, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, L, LinearMap.coe_mk, AddHom.coe_mk]
          _ = t * x (Sum.inr v) := by
            rw [hxL, mul_zero, sub_zero, ← hright, hxe]
            rfl
      let y : Γ → ℂ := fun u => (x (Sum.inl u) : ℂ)
      let z : Γ → ℂ := fun v => (x (Sum.inr v) : ℂ)
      have hy0 : y ≠ 0 := by
        intro hy
        apply hx0
        apply PiLp.ext
        intro v
        cases v with
        | inl u =>
          have hh := congrFun hy u
          change x (Sum.inl u) = 0
          apply Complex.ofReal_injective
          exact hh
        | inr v =>
          have hh := hcright v
          have hxl (u : Γ) : x (Sum.inl u) = 0 := by
            have hh := congrFun hy u
            apply Complex.ofReal_injective
            exact hh
          simp only [hxl, mul_zero, Finset.sum_const_zero] at hh
          exact (mul_eq_zero.mp hh.symm).resolve_left ht.ne'
      have hBz : B *ᵥ z = (t : ℂ) • y := by
        ext u
        change (∑ v, (C u v : ℂ) * (x (Sum.inr v) : ℂ)) = (t : ℂ) * (x (Sum.inl u) : ℂ)
        exact_mod_cast hcleft u
      have hBty : Bᴴ *ᵥ y = (t : ℂ) • z := by
        ext v
        change (∑ u, star (C u v : ℂ) * (x (Sum.inl u) : ℂ)) = (t : ℂ) * (x (Sum.inr v) : ℂ)
        simp only [Complex.star_def, Complex.conj_ofReal]
        exact_mod_cast hcright v
      have hMy : M *ᵥ y = ((t ^ 2 : ℝ) : ℂ) • y := by
        rw [show M = B * Bᴴ from rfl, ← Matrix.mulVec_mulVec, hBty, Matrix.mulVec_smul, hBz,
          smul_smul, Complex.ofReal_pow, pow_two]
      have hMeig : Module.End.HasEigenvalue M.toEuclideanLin ((t ^ 2 : ℝ) : ℂ) := by
        apply Module.End.hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2 y)
        constructor
        · apply Module.End.mem_eigenspace_iff.mpr
          exact congrArg (WithLp.toLp 2) hMy
        · intro hh
          exact hy0 (congrArg WithLp.ofLp hh)
      have hbound := spectral_bound M hMpos hMinv hMzero (t ^ 2) (sq_pos_of_pos ht) hMeig
      rw [hMtrace] at hbound
      have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have hsquare : t ^ 2 ≤ a * (n - a) / k := (le_div_iff₀ hkreal).mpr (by nlinarith [hbound])
      have htbound : t ≤ Real.sqrt (a * (n - a) / k) := Real.le_sqrt_of_sq_le hsquare
      exact htt.trans htbound
