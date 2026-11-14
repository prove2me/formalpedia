-- Prove2me | solution 1 for DiazModulus.roy_rational_adapted_basis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:32.7682+00:00
-- url     : https://prove2.me/submissions/4de6e3c1-0b6b-44a8-89bb-3309f1ed65cf

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A rational subspace is a coordinate subspace after an algebraic change of basis

Let `S ⊆ ℂ^d` be spanned by its algebraic vectors and let `W ⊆ Q̄^d` be the `Q̄`-subspace of
algebraic vectors of `S`, i.e. the vectors `w` with `ι w ∈ S`, where `ι : Q̄^d → ℂ^d` is the
coordinatewise inclusion. Pick a `Q̄`-basis of `W`, a basis of a complement, and concatenate them
into a basis `b` of `Q̄^d` (the `W`-part first, `k = dim_Q̄ W` vectors). Let `P` be the matrix with
columns `b`, `P'` its inverse (both algebraic), and `Q, Q'` their images in `ℂ^{d×d}`; still mutually
inverse, so `g := Q'` is a `ℂ`-linear automorphism, and `g`, `g⁻¹ = Q` preserve `Q̄^d` and `ℒ̃^d`
because `ℒ̃` is a `Q̄`-subspace of `ℂ`. Every `v ∈ ℂ^d` is `Σ_j (g v)_j ι(b_j)`, so if the
coordinates `j ≥ k` of `g v` vanish then `v ∈ S`. Conversely `g (ι w) = ι (repr_b w)` has vanishing
coordinates `j ≥ k` for `w ∈ W`, and these vectors span `S` over `ℂ`. Finally the columns
`ι(b_j)` are `ℂ`-independent (the matrix is invertible) and the first `k` of them span `S`, so
`dim_ℂ S = k`. -/

namespace RC1_RAB
open DiazModulus Matrix

/-- Coordinatewise inclusion `Q̄^d → ℂ^d`. -/
noncomputable def incl (d : ℕ) : (Fin d → ↥Qbar) →ₗ[↥Qbar] (Fin d → ℂ) :=
  LinearMap.compLeft (Algebra.linearMap (↥Qbar) ℂ) (Fin d)

theorem incl_apply {d : ℕ} (w : Fin d → ↥Qbar) (i : Fin d) : incl d w i = (w i : ℂ) := rfl

/-- An algebraic matrix maps algebraic vectors to algebraic vectors, `ℒ̃`-vectors to `ℒ̃`-vectors. -/
theorem mulVec_map_mem {d : ℕ} (M : Matrix (Fin d) (Fin d) ↥Qbar) (v : Fin d → ℂ) :
    ((∀ i, v i ∈ Qbar) → ∀ i, (M.map Qbar.subtype *ᵥ v) i ∈ Qbar) ∧
    ((∀ i, v i ∈ LogAlgTilde) → ∀ i, (M.map Qbar.subtype *ᵥ v) i ∈ LogAlgTilde) := by
  refine ⟨fun hv i => ?_, fun hv i => ?_⟩
  · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (M i j).2 (hv j)
  · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Submodule.sum_mem _ fun j _ => LogAlgTilde.smul_mem (M i j) (hv j)

/-- A basis of `Q̄^d` whose first `dim W` vectors lie in `W`, the other coordinates vanishing on `W`. -/
theorem exists_adapted_basis {d : ℕ} (W : Submodule ↥Qbar (Fin d → ↥Qbar)) :
    ∃ b : Module.Basis (Fin d) ↥Qbar (Fin d → ↥Qbar),
      (∀ j : Fin d, j.val < Module.finrank ↥Qbar W → b j ∈ W) ∧
      (∀ j : Fin d, Module.finrank ↥Qbar W ≤ j.val → ∀ w ∈ W, b.repr w j = 0) := by
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  let b0 := ((Module.finBasis ↥Qbar W).prod (Module.finBasis ↥Qbar W')).map
    (Submodule.prodEquivOfIsCompl W W' hW)
  have hkk : Module.finrank ↥Qbar W + Module.finrank ↥Qbar W' = d := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  let σ : Fin (Module.finrank ↥Qbar W) ⊕ Fin (Module.finrank ↥Qbar W') ≃ Fin d :=
    finSumFinEquiv.trans (finCongr hkk)
  refine ⟨b0.reindex σ, fun j hj => ?_, fun j hj w hw => ?_⟩
  · rw [Module.Basis.reindex_apply]
    rcases h : σ.symm j with i | i
    · simp [b0]
    · exfalso
      have h2 : σ (Sum.inr i) = j := by rw [← h, Equiv.apply_symm_apply]
      have h3 : (σ (Sum.inr i)).val = Module.finrank ↥Qbar W + i.val := rfl
      omega
  · rw [Module.Basis.repr_reindex_apply]
    rcases h : σ.symm j with i | i
    · exfalso
      have h2 : σ (Sum.inl i) = j := by rw [← h, Equiv.apply_symm_apply]
      have h3 : (σ (Sum.inl i)).val = i.val := rfl
      omega
    · simp [b0, Module.Basis.map_repr, Submodule.prodEquivOfIsCompl_symm_apply_left W W' hW ⟨w, hw⟩]

end RC1_RAB

open DiazModulus RC1_RAB in
theorem solution {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) (hS : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S) :
    ∃ g : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ),
      (∀ v : Fin d → ℂ, (∀ i, v i ∈ Qbar) → (∀ i, g v i ∈ Qbar) ∧ ∀ i, g.symm v i ∈ Qbar) ∧
      (∀ v : Fin d → ℂ, (∀ i, v i ∈ LogAlgTilde) → (∀ i, g v i ∈ LogAlgTilde) ∧ ∀ i, g.symm v i ∈ LogAlgTilde) ∧
      ∀ v : Fin d → ℂ, v ∈ S ↔ ∀ i : Fin d, Module.finrank ℂ ↥(S) ≤ i.val → g v i = 0 := by
  classical
  let W : Submodule ↥Qbar (Fin d → ↥Qbar) := (S.restrictScalars ↥Qbar).comap (incl d)
  obtain ⟨b, hb1, hb2⟩ := exists_adapted_basis W
  have hkd : Module.finrank ↥Qbar W ≤ d := by
    simpa using Submodule.finrank_le W
  obtain ⟨P, P', hPP', hP'P, hPij, hrepr⟩ : ∃ P P' : Matrix (Fin d) (Fin d) ↥Qbar,
      P * P' = 1 ∧ P' * P = 1 ∧ (∀ i j, P i j = b j i) ∧ ∀ w, Matrix.mulVec P' w = ⇑(b.repr w) := by
    refine ⟨(Pi.basisFun ↥Qbar (Fin d)).toMatrix b, b.toMatrix (Pi.basisFun ↥Qbar (Fin d)),
      Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
      fun i j => by simp [Module.Basis.toMatrix_apply], fun w => ?_⟩
    have h := (Pi.basisFun ↥Qbar (Fin d)).toMatrix_mulVec_repr b w
    have hw : ⇑((Pi.basisFun ↥Qbar (Fin d)).repr w) = w := by ext i; simp
    rwa [hw] at h
  set k := Module.finrank ↥Qbar W with hk_def
  set Q := P.map Qbar.subtype
  set Q' := P'.map Qbar.subtype
  have hQQ' : Q * Q' = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ'Q : Q' * Q = 1 := by
    rw [← Matrix.map_mul, hP'P, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinearMap (Matrix.toLin' Q') (Matrix.toLin' Q)
    (by rw [← Matrix.toLin'_mul, hQ'Q, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hQQ', Matrix.toLin'_one])
  have hg : ∀ v, g v = Matrix.mulVec Q' v := fun v => Matrix.toLin'_apply Q' v
  have hgs : ∀ v, g.symm v = Matrix.mulVec Q v := fun v => Matrix.toLin'_apply Q v
  have hQcol : ∀ u : Fin d → ℂ, Matrix.mulVec Q u = ∑ j, u j • incl d (b j) := by
    intro u; funext i
    simp [Q, Matrix.mulVec, dotProduct, hPij, Finset.sum_apply, incl_apply, mul_comm]
  have hdecomp : ∀ v, v = ∑ j, (Matrix.mulVec Q' v) j • incl d (b j) := by
    intro v; rw [← hQcol, Matrix.mulVec_mulVec, hQQ', Matrix.one_mulVec]
  have hchar : ∀ v, v ∈ S ↔ ∀ j : Fin d, k ≤ j.val → (Matrix.mulVec Q' v) j = 0 := by
    intro v; constructor
    · intro hv
      rw [← hS] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨hxS, hxa⟩ := hx
        intro j hj
        let w : Fin d → ↥Qbar := fun i => ⟨x i, hxa i⟩
        have hxw : x = Qbar.subtype ∘ w := rfl
        have hwW : w ∈ W := hxS
        rw [hxw, ← RingHom.map_mulVec, hrepr, hb2 j hj w hwW, map_zero]
      | zero => intro j _; simp
      | add x y _ _ hx hy => intro j hj; simp [Matrix.mulVec_add, hx j hj, hy j hj]
      | smul a x _ hx => intro j hj; simp [Matrix.mulVec_smul, hx j hj]
    · intro hv
      rw [hdecomp v]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : k ≤ j.val
      · simp [hv j hj]
      · exact S.smul_mem _ (hb1 j (by omega))
  have hk : Module.finrank ℂ S = k := by
    have hli : LinearIndependent ℂ (fun j => incl d (b j)) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha j
      have h1 : Matrix.mulVec Q a = 0 := by rw [hQcol]; exact ha
      have h2 : a = Matrix.mulVec Q' (Matrix.mulVec Q a) := by rw [Matrix.mulVec_mulVec, hQ'Q, Matrix.one_mulVec]
      rw [h2, h1, Matrix.mulVec_zero]; rfl
    have hli' := hli.comp _ (Fin.castLE_injective hkd)
    have hspan : Submodule.span ℂ (Set.range ((fun j => incl d (b j)) ∘ Fin.castLE hkd)) = S := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb1 _ (by simp)
      · intro v hv
        rw [hdecomp v]
        refine Submodule.sum_mem _ fun j _ => ?_
        by_cases hj : k ≤ j.val
        · simp [(hchar v).1 hv j hj]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, by omega⟩, ?_⟩)
          simp
    rw [← hspan, finrank_span_eq_card hli', Fintype.card_fin]
  refine ⟨g, fun v hv => ⟨fun i => ?_, fun i => ?_⟩, fun v hv => ⟨fun i => ?_, fun i => ?_⟩,
    fun v => ?_⟩
  · rw [hg]; exact (mulVec_map_mem P' v).1 hv i
  · rw [hgs]; exact (mulVec_map_mem P v).1 hv i
  · rw [hg]; exact (mulVec_map_mem P' v).2 hv i
  · rw [hgs]; exact (mulVec_map_mem P v).2 hv i
  · rw [hchar, hk]
    simp only [hg]
