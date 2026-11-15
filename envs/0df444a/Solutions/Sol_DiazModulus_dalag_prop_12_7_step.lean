-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_7_step
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-15T05:51:35.154559+00:00
-- url     : https://prove2.me/submissions/25762872-754f-4648-863f-3368cc5cc080

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.7, the inductive step

Let `M` be the `d × ℓ` matrix whose columns are `v₁, …, v_ℓ`: its entries lie in `E`, and `M ≠ 0` since `v₁ ≠ 0`.
The Property (A B; C 0) gives `r ≤ d, ℓ` and `P ∈ GL_d(k)`, `Q ∈ GL_ℓ(k)` such that `N = PMQ` vanishes in rows and
columns `≥ r` and has a regular upper-left `r × r` block. Then `r ≤ rank N = rank M ≤ dim V`, and `dim V < d`,
since otherwise `V = K^d` would contain the first unit vector, a non-zero vector of `k^d`. Let `V₁ ⊂ K^r` be the
`K`-subspace of the `u` whose extension by zeros lies in `P·V`; it meets `k^r` only in `0`, because `P⁻¹` has
entries in `k`. With `ℓ₁ = ℓ − r`, let `w_j` be the first `r` entries of column `r + j` of `N`. The zero block
makes the extension of `w_j` equal to that column, which is `P` times `Σ_t Q_{t, r+j} v_t ∈ V`, so `w_j ∈ V₁`.
The entries of `N` are `k`-linear combinations of entries of `M`, so they lie in `E`. Finally the columns of `N`
are `k`-free (a `k`-relation among them gives one among the `v_t` through the invertible `P` and `Q`), hence so
are the `w_j`. -/

open DiazModulus Matrix in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d ℓ : ℕ} (V : Submodule K (Fin d → K))
    (hV : ∀ v ∈ V, (∀ i, ∃ c : k, v i = algebraMap k K c) → v = 0)
    (v : Fin ℓ → Fin d → K) (hv : LinearIndependent k v) (hvV : ∀ j, v j ∈ V)
    (hvE : ∀ j i, v j i ∈ E) (hℓ : 0 < ℓ) :
    ∃ (r ℓ₁ : ℕ) (V₁ : Submodule K (Fin r → K)) (w : Fin ℓ₁ → Fin r → K),
      r + ℓ₁ = ℓ ∧ r ≤ Module.finrank K ↥V ∧ r < d ∧
      (∀ u ∈ V₁, (∀ i, ∃ c : k, u i = algebraMap k K c) → u = 0) ∧
      LinearIndependent k w ∧ (∀ j, w j ∈ V₁) ∧ (∀ j i, w j i ∈ E) := by
  classical
  -- 1. the coordinate matrix
  let M : Matrix (Fin d) (Fin ℓ) K := Matrix.of fun i j => v j i
  have hMv : ∀ q : Fin ℓ → K, M *ᵥ q = ∑ t, q t • v t := by
    intro q; funext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hv0 : v ⟨0, hℓ⟩ ≠ 0 := hv.ne_zero _
  have hM0 : M ≠ 0 := by
    intro h; apply hv0; funext i
    have := congrFun (congrFun h i) ⟨0, hℓ⟩
    simpa [M] using this
  -- 2. the Property (A B; C 0)
  obtain ⟨r, hrd, hrℓ, P, Q, hP, hQ, hz, hA⟩ := hE d ℓ M (fun i j => hvE j i) hM0
  set P' : Matrix (Fin d) (Fin d) K := P.map (algebraMap k K) with hP'def
  set Q' : Matrix (Fin ℓ) (Fin ℓ) K := Q.map (algebraMap k K) with hQ'def
  set N : Matrix (Fin d) (Fin ℓ) K := P' * M * Q' with hNdef
  have hP' : IsUnit P'.det := by
    have : P'.det = algebraMap k K P.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hP.map _
  have hQ' : IsUnit Q'.det := by
    have : Q'.det = algebraMap k K Q.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hQ.map _
  -- 3–4. ranks
  have hMV : M.rank ≤ Module.finrank K ↥V := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hvV j))
  have hNM : N.rank = M.rank := by
    rw [hNdef, Matrix.rank_mul_eq_left_of_isUnit_det Q' (P' * M) hQ',
      Matrix.rank_mul_eq_right_of_isUnit_det P' M hP']
  have hrN : r ≤ N.rank := by
    have h := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hA)
    rw [Fintype.card_fin] at h
    rw [← h]
    exact Matrix.rank_submatrix_le N (Fin.castLE hrd) (Fin.castLE hrℓ)
  -- 5. dim V < d
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; exact absurd (funext fun i => i.elim0) hv0
    · exact h
  have hnd : Module.finrank K ↥V < d := by
    by_contra hcon
    have hle := Submodule.finrank_le V
    rw [Module.finrank_fin_fun] at hle
    have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    have hmem : (Pi.single (⟨0, hd0⟩ : Fin d) (1 : K) : Fin d → K) ∈ V := htop ▸ Submodule.mem_top
    have h0 := hV _ hmem (fun i => by
      by_cases hi : i = ⟨0, hd0⟩
      · exact ⟨1, by subst hi; simp⟩
      · exact ⟨0, by simp [hi]⟩)
    have := congrFun h0 ⟨0, hd0⟩
    simp at this
  -- 6–7. the extension by zeros and V₁, the vectors whose extension lies in P·V
  let ext : (Fin r → K) →ₗ[K] (Fin d → K) :=
    { toFun := fun u i => if h : i.val < r then u ⟨i.val, h⟩ else 0
      map_add' := by intro u u'; funext i; by_cases h : i.val < r <;> simp [h]
      map_smul' := by intro c u; funext i; by_cases h : i.val < r <;> simp [h] }
  have hext : ∀ u i, ext u i = if h : i.val < r then u ⟨i.val, h⟩ else 0 := fun _ _ => rfl
  have hext_inj : ∀ u, ext u = 0 → u = 0 := by
    intro u hu; funext i
    have := congrFun hu (Fin.castLE hrd i)
    simpa [hext, i.isLt] using this
  let V₁ : Submodule K (Fin r → K) := (V.map P'.mulVecLin).comap ext
  have hPinv : (P⁻¹).map (algebraMap k K) * P' = 1 := by
    rw [hP'def, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hV₁ : ∀ u ∈ V₁, (∀ i, ∃ c : k, u i = algebraMap k K c) → u = 0 := by
    intro u hu hc
    choose c hc using hc
    obtain ⟨y, hyV, hy⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hu)
    have hy' : P' *ᵥ y = ext u := hy
    let c' : Fin d → k := fun i => if h : i.val < r then c ⟨i.val, h⟩ else 0
    have hextc : ext u = algebraMap k K ∘ c' := by
      funext i; by_cases h : i.val < r <;> simp [hext, c', h, hc]
    have hyk : y = (P⁻¹).map (algebraMap k K) *ᵥ ext u := by
      rw [← hy', Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
    have hy0 : y = 0 := hV y hyV (fun i => ⟨(P⁻¹ *ᵥ c') i, by
      rw [hyk, hextc, RingHom.map_mulVec]⟩)
    apply hext_inj
    rw [← hy', hy0, Matrix.mulVec_zero]
  -- 8. the columns of the block B
  set ℓ₁ := ℓ - r with hℓ₁
  let col : Fin ℓ₁ → Fin ℓ := fun j => ⟨r + j.val, by omega⟩
  have hcol_inj : Function.Injective col := by
    intro a b h; ext; simpa [col] using congrArg Fin.val h
  let w : Fin ℓ₁ → Fin r → K := fun j i => N (Fin.castLE hrd i) (col j)
  have hextw : ∀ j, ext (w j) = fun i => N i (col j) := by
    intro j; funext i
    by_cases h : i.val < r
    · simp only [hext, h, dif_pos, w]; rfl
    · simp only [hext, h, dif_neg, not_false_eq_true]
      exact (hz i (col j) (by omega) (by simp [col])).symm
  -- (a) w j ∈ V₁
  have hwV : ∀ j, w j ∈ V₁ := by
    intro j
    refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨fun a => (M * Q') a (col j), ?_, ?_⟩)
    · have : (fun a => (M * Q') a (col j)) = ∑ t, (Q' t (col j)) • v t := by
        funext a; simp [Matrix.mul_apply, M, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hvV t)
    · rw [hextw]; funext i
      simp only [Matrix.mulVecLin_apply, hNdef, Matrix.mul_assoc]
      rfl
  -- (b) entries in E
  have hNE : ∀ i c, N i c ∈ E := by
    intro i c
    simp only [hNdef, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun a _ => ?_
    have : P' i a * M a b * Q' b c = (P i a * Q b c) • M a b := by
      simp [P', Q', Algebra.smul_def]; ring
    rw [this]
    exact Submodule.smul_mem _ _ (hvE b a)
  have hwE : ∀ j i, w j i ∈ E := fun j i => hNE _ _
  -- (c) k-freeness
  have hNcol : LinearIndependent k (fun t : Fin ℓ => fun i => N i t) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : N *ᵥ (algebraMap k K ∘ g) = 0 := by
      rw [← hg]; funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
    have h2 : P' *ᵥ (M *ᵥ (Q' *ᵥ (algebraMap k K ∘ g))) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; exact h1
    have hPinj : Function.Injective P'.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hP')
    have h3 : M *ᵥ (Q' *ᵥ (algebraMap k K ∘ g)) = 0 :=
      hPinj (by rw [h2, Matrix.mulVec_zero])
    have h4 : Q' *ᵥ (algebraMap k K ∘ g) = algebraMap k K ∘ (Q *ᵥ g) := by
      funext i; rw [Function.comp_apply, RingHom.map_mulVec]
    rw [h4, hMv] at h3
    have h5 : ∑ t, (Q *ᵥ g) t • v t = 0 := by
      rw [← h3]; simp [algebraMap_smul]
    have h6 : Q *ᵥ g = 0 := by
      funext t; exact (Fintype.linearIndependent_iff.mp hv) _ h5 t
    have hQinj : Function.Injective Q.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hQ)
    have h7 : g = 0 := hQinj (by rw [h6, Matrix.mulVec_zero])
    intro t; rw [h7]; rfl
  have hw : LinearIndependent k w := by
    have h1 : LinearIndependent k (fun j : Fin ℓ₁ => fun i => N i (col j)) := hNcol.comp _ hcol_inj
    have h2 : (fun j : Fin ℓ₁ => fun i => N i (col j)) = (ext.restrictScalars k) ∘ w := by
      funext j; exact (hextw j).symm
    rw [h2] at h1
    exact h1.of_comp
  refine ⟨r, ℓ₁, V₁, w, by omega, ?_, by omega, hV₁, hw, hwV, hwE⟩
  calc r ≤ N.rank := hrN
    _ = M.rank := hNM
    _ ≤ _ := hMV
