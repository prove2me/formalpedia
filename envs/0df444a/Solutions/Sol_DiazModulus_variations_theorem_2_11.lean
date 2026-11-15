-- Prove2me | solution 1 for DiazModulus.variations_theorem_2_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:37:37.4889+00:00
-- url     : https://prove2.me/submissions/2eefc8e8-353e-4879-9e53-d7be3d0235af

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_variations_hyperplane_bound

open Complex ComplexConjugate

/-! # Waldschmidt, *Variations* Th. 2.11 (= *Role* Th. 6.2)

Suppose every `Λ′ⱼ = Λ₁Λ₁ⱼ + ⋯ + Λ_mΛ_mⱼ` lies in `ℒ̃`. In `ℂ^{m+1}` let `φ(z) = Λ₁z₁ + ⋯ + Λ_m z_m − z_{m+1}` and
`V = ker φ`. Since `φ(−w e_{m+1}) = w`, `φ` is onto and `dim V + 1 = m + 1`. An algebraic `z ∈ V` is an algebraic
relation `z₁Λ₁ + ⋯ + z_mΛ_m − z_{m+1}·1 = 0`, so `z = 0` by the freeness of `1, Λ₁, …, Λ_m`. The `m + ℓ` points
`(eᵢ, Λᵢ)` and `(M_{·j}, Λ′ⱼ)` lie in `V` and have coordinates in `ℒ̃`; they are `Q̄`-free because their first `m`
coordinates are the columns of `(I_m, M)`. The hyperplane bound (*Variations* Th. 3.1) makes `V ∩ ℒ̃^{m+1}`
finite-dimensional over `Q̄` of dimension at most `(m + 1)m`, so `m + ℓ ≤ m + m²`, contradicting `ℓ > m²`. -/

namespace RC2_T211
open DiazModulus

/-- The linear form `z ↦ Σ Λᵢ zᵢ − z_{m+1}` on `ℂ^{m+1}`. -/
def phi {m : ℕ} (Λ : Fin m → ℂ) : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ i : Fin m, Λ i * z (Fin.castSucc i) - z (Fin.last m)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem phi_apply {m : ℕ} (Λ : Fin m → ℂ) (z : Fin (m + 1) → ℂ) :
    phi Λ z = ∑ i : Fin m, Λ i * z (Fin.castSucc i) - z (Fin.last m) := rfl

/-- `dim ker φ + 1 = m + 1`. -/
theorem finrank_ker_phi {m : ℕ} (Λ : Fin m → ℂ) :
    Module.finrank ℂ ↥(LinearMap.ker (phi Λ)) + 1 = m + 1 := by
  have hsurj : Function.Surjective (phi Λ) := by
    intro w
    refine ⟨Pi.single (Fin.last m) (-w), ?_⟩
    simp [phi_apply, Fin.castSucc_ne_last]
  have h := LinearMap.finrank_range_add_finrank_ker (phi Λ)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

/-- `ker φ` meets `Q̄^{m+1}` only in `0` when `1, Λ₁, …, Λ_m` are `Q̄`-free. -/
theorem ker_phi_noQbar {m : ℕ} (Λ : Fin m → ℂ)
    (hΛind : LinearIndependent (↥Qbar) (Fin.cons 1 Λ : Fin (m + 1) → ℂ)) :
    ∀ v ∈ LinearMap.ker (phi Λ), (∀ i, v i ∈ Qbar) → v = 0 := by
  intro v hv hvQ
  have hv0 : ∑ i : Fin m, Λ i * v (Fin.castSucc i) - v (Fin.last m) = 0 := hv
  have key := (Fintype.linearIndependent_iff.mp hΛind)
    (Fin.cons (-⟨v (Fin.last m), hvQ _⟩) (fun i => ⟨v (Fin.castSucc i), hvQ _⟩))
    (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Subfield.smul_def, smul_eq_mul]
      simp
      have hc : ∑ i : Fin m, v (Fin.castSucc i) * Λ i = ∑ i : Fin m, Λ i * v (Fin.castSucc i) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      linear_combination hv0 + hc)
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have := key 0
    simp only [Fin.cons_zero, neg_eq_zero] at this
    simpa using congrArg Subtype.val this
  · have := key (Fin.succ i)
    simp only [Fin.cons_succ] at this
    simpa using congrArg Subtype.val this

end RC2_T211

open DiazModulus RC2_T211 in
theorem solution {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hcol : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℂ) M).col)
    (Λ : Fin m → ℂ) (hΛ : ∀ i, Λ i ∈ LogAlgTilde)
    (hΛind : LinearIndependent (↥Qbar) (Fin.cons 1 Λ : Fin (m + 1) → ℂ))
    (hℓ : m ^ 2 < ℓ) :
    ∃ j : Fin ℓ, ∑ i, Λ i * M i j ∉ LogAlgTilde := by
  by_contra hcon
  push Not at hcon
  set V := LinearMap.ker (phi Λ) with hVdef
  obtain ⟨hfin, hbound⟩ :=
    DiazModulus.variations_hyperplane_bound V (finrank_ker_phi Λ) (ker_phi_noQbar Λ hΛind)
  -- the points `(C c, μ c)`
  let C := (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℂ) M).col
  let μ : Fin m ⊕ Fin ℓ → ℂ := Sum.elim Λ (fun j => ∑ i, Λ i * M i j)
  let γ : Fin m ⊕ Fin ℓ → Fin (m + 1) → ℂ := fun c => Fin.snoc (C c) (μ c)
  have hγV : ∀ c, γ c ∈ V := by
    intro c
    show ∑ i : Fin m, Λ i * γ c (Fin.castSucc i) - γ c (Fin.last m) = 0
    simp only [γ, Fin.snoc_castSucc, Fin.snoc_last]
    rcases c with k | j
    · simp [C, μ, Matrix.col_apply, Matrix.one_apply]
    · simp [C, μ, Matrix.col_apply]
  have hγL : ∀ c k, γ c k ∈ LogAlgTilde := by
    intro c k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [γ, Fin.snoc_last]
      rcases c with k | j
      · simpa [μ] using hΛ k
      · simpa [μ] using hcon j
    · simp only [γ, Fin.snoc_castSucc]
      rcases c with k | j
      · simp only [C, Matrix.col_apply, Matrix.fromCols_apply_inl, Matrix.one_apply]
        split_ifs
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · exact LogAlgTilde.zero_mem
      · simpa [C, Matrix.col_apply] using hM i j
  have hγind : LinearIndependent (↥Qbar) γ := by
    have hcomp : (LinearMap.funLeft (↥Qbar) ℂ (Fin.castSucc : Fin m → Fin (m + 1))) ∘ γ = C := by
      funext c i
      simp [γ, C, Matrix.col_apply, LinearMap.funLeft_apply]
    apply LinearIndependent.of_comp (LinearMap.funLeft (↥Qbar) ℂ (Fin.castSucc : Fin m → Fin (m + 1)))
    rw [hcomp]
    exact hcol
  -- the points as a `Q̄`-free family in `V ∩ ℒ̃^{m+1}`
  let W := V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin (m + 1) => LogAlgTilde)
  let γW : Fin m ⊕ Fin ℓ → ↥W := fun c => ⟨γ c, hγV c, fun k _ => hγL c k⟩
  have hγWind : LinearIndependent (↥Qbar) γW := by
    apply LinearIndependent.of_comp W.subtype
    exact hγind
  have hcard := hγWind.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have := le_trans hcard hbound
  simp only [Nat.add_sub_cancel] at this
  nlinarith
