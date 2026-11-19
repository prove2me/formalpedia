-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:42.695437+00:00
-- url     : https://prove2.me/submissions/607a3c3c-f9ac-44b8-bdb0-0126b8f4f96c

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.6, without the hypothesis n < d

Let `η₁, …, η_ℓ` be a basis of `Y` over `k` and `M` the `d × ℓ` matrix whose `j`-th column is `η_j`; its entries
lie in `E`. If `M ≠ 0`, the Property (A B; C 0) gives `r ≤ d, ℓ` and `P ∈ GL_d(k)`, `Q ∈ GL_ℓ(k)` such that
`N = PMQ` vanishes in rows and columns `≥ r` and has a regular upper-left `r × r` block; if `M = 0` (that is,
`Y = 0`), the same holds with `r = 0` and `P = Q = 1`. Then `r ≤ rank N = rank M ≤ dim V`, since the columns of
`M` lie in `V`. Let `S` be the `K`-span of the first `r` columns of `P⁻¹`: it is rational over `k`, being spanned
by vectors of `k^d`, and has dimension `r`, the columns of `P⁻¹` being free; so `d − d′ = r ≤ n`. It is the
intersection of the hyperplanes `Σ_i p_si z_i = 0` (`s > r`): a vector `z` with `(Pz)_s = 0` for `s > r` is
`P⁻¹(Pz)`, a combination of the first `r` columns of `P⁻¹`. For `t > r`, the vector `θ_t = Σ_j q_jt η_j` of `Y`
satisfies `(Pθ_t)_s = N_st = 0` for `s > r`, so `θ_t ∈ S`. The `θ_t` are `k`-free because `Q` is invertible and
the `η_j` form a basis, so `dim_k(Y ∩ S) ≥ ℓ − r` and `ℓ′ = dim_k(Y/(Y ∩ S)) ≤ r = d − d′`. -/

open DiazModulus Matrix in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d : ℕ} (V : Submodule K (Fin d → K)) (Y : Submodule k (Fin d → K)) [FiniteDimensional k ↥Y]
    (hY : Y ≤ V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) :
    ∃ S : Submodule K (Fin d → K),
      Submodule.span K {v : Fin d → K | v ∈ S ∧ ∀ i, ∃ c : k, v i = algebraMap k K c} = S ∧
      Module.finrank k (↥Y ⧸ (S.restrictScalars k).comap Y.subtype) ≤
        d - Module.finrank K ((Fin d → K) ⧸ S) ∧
      d - Module.finrank K ((Fin d → K) ⧸ S) ≤ Module.finrank K ↥V := by
  classical
  -- 1. the coordinate matrix of a basis of Y
  set ℓ := Module.finrank k ↥Y with hℓ
  let η := Module.finBasis k ↥Y
  let M : Matrix (Fin d) (Fin ℓ) K := Matrix.of fun i j => (η j : Fin d → K) i
  have hηV : ∀ j, (η j : Fin d → K) ∈ V := fun j => (Submodule.mem_inf.mp (hY (η j).2)).1
  have hME : ∀ i j, M i j ∈ E := fun i j =>
    (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hY (η j).2)).2) i (Set.mem_univ _)
  -- 2. the Property (A B; C 0); for M = 0 take r = 0 and P = Q = 1
  obtain ⟨r, hrd, hrℓ, P, Q, hP, hQ, hz, hA⟩ : ∃ (r : ℕ) (hrs : r ≤ d) (hrt : r ≤ ℓ)
      (P : Matrix (Fin d) (Fin d) k) (Q : Matrix (Fin ℓ) (Fin ℓ) k), IsUnit P.det ∧ IsUnit Q.det ∧
      (∀ (i : Fin d) (j : Fin ℓ), r ≤ i.val → r ≤ j.val →
        (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
      IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
        (Fin.castLE hrs) (Fin.castLE hrt)).det := by
    by_cases hM0 : M = 0
    · refine ⟨0, Nat.zero_le _, Nat.zero_le _, 1, 1, by simp, by simp,
        fun i j _ _ => by simp [hM0], ?_⟩
      rw [Matrix.det_fin_zero]; exact isUnit_one
    · exact hE d ℓ M hME hM0
  set P' : Matrix (Fin d) (Fin d) K := P.map (algebraMap k K) with hP'def
  set Q' : Matrix (Fin ℓ) (Fin ℓ) K := Q.map (algebraMap k K) with hQ'def
  set N : Matrix (Fin d) (Fin ℓ) K := P' * M * Q' with hNdef
  have hP' : IsUnit P'.det := by
    have : P'.det = algebraMap k K P.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hP.map _
  have hQ' : IsUnit Q'.det := by
    have : Q'.det = algebraMap k K Q.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hQ.map _
  -- 3. r ≤ rank N = rank M ≤ dim V
  have hrV : r ≤ Module.finrank K ↥V := by
    have hMV : M.rank ≤ Module.finrank K ↥V := by
      rw [Matrix.rank_eq_finrank_span_cols]
      exact Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hηV j))
    have hNM : N.rank = M.rank := by
      rw [hNdef, Matrix.rank_mul_eq_left_of_isUnit_det Q' (P' * M) hQ',
        Matrix.rank_mul_eq_right_of_isUnit_det P' M hP']
    have h := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hA)
    rw [Fintype.card_fin] at h
    calc r = _ := h.symm
      _ ≤ N.rank := Matrix.rank_submatrix_le N (Fin.castLE hrd) (Fin.castLE hrℓ)
      _ = M.rank := hNM
      _ ≤ _ := hMV
  -- 4. S, the span of the first r columns of P⁻¹
  set R : Matrix (Fin d) (Fin d) K := (P⁻¹).map (algebraMap k K) with hRdef
  have hRP : R * P' = 1 := by
    rw [hRdef, hP'def, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP,
      Matrix.map_one _ (map_zero _) (map_one _)]
  let c : Fin r → Fin d → K := fun a i => R i (Fin.castLE hrd a)
  let S : Submodule K (Fin d → K) := Submodule.span K (Set.range c)
  have hc : LinearIndependent K c := by
    have hR : IsUnit R := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : R.det = algebraMap k K P⁻¹.det := by rw [RingHom.map_det]; rfl
      rw [this]; exact (Matrix.isUnit_nonsing_inv_det P hP).map _
    exact (Matrix.linearIndependent_cols_iff_isUnit.mpr hR).comp _ (Fin.castLE_injective hrd)
  have hSr : Module.finrank K ↥S = r := by
    rw [finrank_span_eq_card hc, Fintype.card_fin]
  have hdS : d - Module.finrank K ((Fin d → K) ⧸ S) = r := by
    have := Submodule.finrank_quotient_add_finrank S
    rw [Module.finrank_fin_fun, hSr] at this
    omega
  -- a vector z with (P z)_s = 0 for all s ≥ r lies in S
  have hmemS : ∀ z : Fin d → K, (∀ s : Fin d, r ≤ s.val → (P' *ᵥ z) s = 0) → z ∈ S := by
    intro z hzs
    have hz' : z = ∑ s, (P' *ᵥ z) s • (fun i => R i s) := by
      have : z = R *ᵥ (P' *ᵥ z) := by rw [Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
      conv_lhs => rw [this]
      funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hz']
    refine Submodule.sum_mem _ fun s _ => ?_
    by_cases hs : s.val < r
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨s.val, hs⟩, rfl⟩)
    · rw [hzs s (by omega), zero_smul]; exact S.zero_mem
  refine ⟨S, ?_, ?_, by rw [hdS]; exact hrV⟩
  · -- S is rational over k
    apply le_antisymm
    · exact Submodule.span_le.mpr fun v hv => hv.1
    · exact Submodule.span_mono (by
        rintro _ ⟨a, rfl⟩
        exact ⟨Submodule.subset_span ⟨a, rfl⟩, fun i => ⟨P⁻¹ i (Fin.castLE hrd a), rfl⟩⟩)
  -- 5. θ_t = Σ_j q_jt η_j for t ≥ r lies in Y ∩ S, and these are k-free
  rw [hdS]
  set T := (S.restrictScalars k).comap Y.subtype with hT
  set ℓ₁ := ℓ - r with hℓ₁
  let col : Fin ℓ₁ → Fin ℓ := fun t => ⟨r + t.val, by omega⟩
  have hcol_inj : Function.Injective col := by
    intro a b h; ext; simpa [col] using congrArg Fin.val h
  let θ : Fin ℓ → ↥Y := fun t => η.equivFun.symm (fun j => Q j t)
  have hθ : LinearIndependent k θ := by
    have hQc : LinearIndependent k Q.col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hQ)
    exact hQc.map' η.equivFun.symm.toLinearMap (LinearEquiv.ker _)
  have hθS : ∀ t : Fin ℓ₁, θ (col t) ∈ T := by
    intro t
    show ((θ (col t) : ↥Y) : Fin d → K) ∈ S
    apply hmemS
    intro s hs
    have hθM : ((θ (col t) : ↥Y) : Fin d → K) = fun i => (M * Q') i (col t) := by
      funext i
      simp [θ, Module.Basis.equivFun_symm_apply, Matrix.mul_apply, M, Q', Algebra.smul_def, mul_comm]
      rfl
    rw [hθM]
    have h := hz s (col t) hs (by simp [col])
    rw [hNdef, Matrix.mul_assoc] at h
    exact h
  let θT : Fin ℓ₁ → ↥T := fun t => ⟨θ (col t), hθS t⟩
  have hθT : LinearIndependent k θT := by
    apply LinearIndependent.of_comp T.subtype
    exact hθ.comp _ hcol_inj
  have h1 := hθT.fintype_card_le_finrank
  have h2 := Submodule.finrank_quotient_add_finrank T
  rw [Fintype.card_fin] at h1
  omega
