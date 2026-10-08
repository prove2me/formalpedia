-- Prove2me | solution 1 for ExtensionComplexity.TSP.xc_face_mono
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T22:57:43.945814+00:00
-- url     : https://prove2.me/submissions/71397dc3-f8c4-431a-8396-58f3d215c13d

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope


open Matrix ExtensionComplexity.TSP Set

namespace XCT

section Hull

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Membership in the convex hull of a finite family. -/
lemma mem_convexHull_range_iff {J : Type*} [Fintype J] (v : J → E) (x : E) :
    x ∈ convexHull ℝ (range v) ↔
      ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∑ j, w j • v j = x := by
  classical
  constructor
  · intro hx
    obtain ⟨ι, _, w', z', hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.1 hx
    choose g hg using hz
    refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), w' i, fun j =>
      Finset.sum_nonneg fun i _ => hw0 i, ?_, ?_⟩
    · rw [← hw1]
      exact Finset.sum_fiberwise Finset.univ g w'
    · rw [← hx]
      simp_rw [Finset.sum_smul]
      rw [← Finset.sum_fiberwise Finset.univ g (fun i => w' i • z' i)]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [← hg i, hi.2]
  · rintro ⟨w, hw0, hw1, hx⟩
    exact mem_convexHull_of_exists_fintype w v hw0 hw1 (fun j => mem_range_self j) hx

end Hull

section EF

variable {ι : Type*} [Fintype ι]

/-- An extended formulation with arbitrary finite index types gives an EF in the platform sense. -/
lemma isEF_of {P : Set (ι → ℝ)} {K R I : Type*} [Fintype K] [Fintype R] [Fintype I]
    (Eeq : Matrix R ι ℝ) (Feq : Matrix R K ℝ) (geq : R → ℝ)
    (Ele : Matrix I ι ℝ) (Fle : Matrix I K ℝ) (gle : I → ℝ)
    (h : ∀ x, x ∈ P ↔ ∃ y : K → ℝ, Eeq *ᵥ x + Feq *ᵥ y = geq ∧ Ele *ᵥ x + Fle *ᵥ y ≤ gle) :
    IsEFOfSize P (Fintype.card I) := by
  classical
  let eK := Fintype.equivFin K
  let eR := Fintype.equivFin R
  let eI := Fintype.equivFin I
  have hx1 : ∀ (M : Matrix R ι ℝ) (x : ι → ℝ),
      M.submatrix eR.symm id *ᵥ x = (M *ᵥ x) ∘ eR.symm := fun M x =>
    submatrix_mulVec_equiv M x eR.symm (Equiv.refl ι)
  have hx2 : ∀ (M : Matrix I ι ℝ) (x : ι → ℝ),
      M.submatrix eI.symm id *ᵥ x = (M *ᵥ x) ∘ eI.symm := fun M x =>
    submatrix_mulVec_equiv M x eI.symm (Equiv.refl ι)
  have hy1 : ∀ (M : Matrix R K ℝ) (y : Fin (Fintype.card K) → ℝ),
      M.submatrix eR.symm eK.symm *ᵥ y = (M *ᵥ (y ∘ eK)) ∘ eR.symm := fun M y => by
    rw [submatrix_mulVec_equiv M y eR.symm eK.symm]
    rfl
  have hy2 : ∀ (M : Matrix I K ℝ) (y : Fin (Fintype.card K) → ℝ),
      M.submatrix eI.symm eK.symm *ᵥ y = (M *ᵥ (y ∘ eK)) ∘ eI.symm := fun M y => by
    rw [submatrix_mulVec_equiv M y eI.symm eK.symm]
    rfl
  refine ⟨Fintype.card K, Fintype.card R, Eeq.submatrix eR.symm id, Feq.submatrix eR.symm eK.symm,
    geq ∘ eR.symm, Ele.submatrix eI.symm id, Fle.submatrix eI.symm eK.symm, gle ∘ eI.symm,
    fun x => ?_⟩
  rw [h]
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨y ∘ eK.symm, ?_, ?_⟩
    · rw [hx1, hy1]
      have : (y ∘ eK.symm) ∘ eK = y := by funext k; simp
      rw [this]
      funext i
      simp only [Pi.add_apply, Function.comp_apply]
      exact congrFun h1 _
    · rw [hx2, hy2]
      have : (y ∘ eK.symm) ∘ eK = y := by funext k; simp
      rw [this]
      intro i
      simp only [Pi.add_apply, Function.comp_apply]
      exact h2 _
  · rintro ⟨y, h1, h2⟩
    refine ⟨y ∘ eK, ?_, ?_⟩
    · funext r
      have := congrFun h1 (eR r)
      rw [hx1, hy1] at this
      simpa using this
    · intro i
      have := h2 (eI i)
      rw [hx2, hy2] at this
      simpa using this

/-- Every polytope has an extended formulation (from its vertex description). -/
lemma exists_EF_of_isPolytope {P : Set (ι → ℝ)} (hP : IsPolytope P) : ∃ r, IsEFOfSize P r := by
  classical
  obtain ⟨V, rfl⟩ := hP
  -- variables `y : V → ℝ`; equations `x - Σ y_v v = 0`, `Σ y_v = 1`; inequalities `-y ≤ 0`.
  let Eeq : Matrix (ι ⊕ Unit) ι ℝ :=
    Matrix.of fun r i => Sum.elim (fun j => if j = i then (1 : ℝ) else 0) (fun _ => 0) r
  let Feq : Matrix (ι ⊕ Unit) V ℝ :=
    Matrix.of fun r (v : V) => Sum.elim (fun j => -(v : ι → ℝ) j) (fun _ => (1 : ℝ)) r
  let geq : ι ⊕ Unit → ℝ := Sum.elim 0 (fun _ => 1)
  refine ⟨_, isEF_of (K := V) Eeq Feq geq 0 (-1 : Matrix V V ℝ) 0 fun x => ?_⟩
  rw [Finset.mem_convexHull']
  have key : ∀ y : V → ℝ, (Eeq *ᵥ x + Feq *ᵥ y = geq ↔
      (∑ v, y v = 1 ∧ ∑ v, y v • (v : ι → ℝ) = x)) := by
    intro y
    have hl : ∀ i, (Eeq *ᵥ x + Feq *ᵥ y) (Sum.inl i) = x i - ∑ v : V, y v * (v : ι → ℝ) i := by
      intro i
      simp only [Pi.add_apply, Eeq, Feq, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, neg_mul,
        Finset.sum_neg_distrib]
      rw [sub_eq_add_neg]
      congr 2
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hr : (Eeq *ᵥ x + Feq *ᵥ y) (Sum.inr ()) = ∑ v : V, y v := by
      simp [Eeq, Feq, mulVec, dotProduct]
    have hs : ∀ i, (∑ v : V, y v • (v : ι → ℝ)) i = ∑ v : V, y v * (v : ι → ℝ) i := by
      intro i
      simp [Finset.sum_apply]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := congrFun h (Sum.inr ())
        rw [hr] at this
        simpa [geq] using this
      · funext i
        have := congrFun h (Sum.inl i)
        rw [hl] at this
        simp only [geq, Sum.elim_inl, Pi.zero_apply] at this
        rw [hs]
        linarith
    · rintro ⟨h1, h2⟩
      funext r
      rcases r with i | u
      · rw [hl]
        have := congrFun h2 i
        rw [hs] at this
        simp only [geq, Sum.elim_inl, Pi.zero_apply]
        linarith
      · rw [hr]
        simpa [geq] using h1
  have hle : ∀ y : V → ℝ, ((0 : Matrix V ι ℝ) *ᵥ x + (-1 : Matrix V V ℝ) *ᵥ y ≤ 0 ↔
      ∀ v, 0 ≤ y v) := by
    intro y
    simp only [zero_mulVec, zero_add, neg_mulVec, one_mulVec]
    constructor
    · intro h v
      have := h v
      simp only [Pi.neg_apply, Pi.zero_apply, neg_nonpos] at this
      exact this
    · intro h v
      simp only [Pi.neg_apply, Pi.zero_apply, neg_nonpos]
      exact h v
  constructor
  · rintro ⟨w, hw0, hw1, hx⟩
    refine ⟨fun v => w v, (key _).2 ⟨?_, ?_⟩, (hle _).2 fun v => hw0 v v.2⟩
    · rw [← hw1]
      exact Finset.sum_coe_sort V w
    · rw [← hx]
      exact Finset.sum_coe_sort V (fun v => w v • v)
  · rintro ⟨y, h1, h2⟩
    obtain ⟨hs, hx⟩ := (key y).1 h1
    have h0 := (hle y).1 h2
    refine ⟨fun v => if hv : v ∈ V then y ⟨v, hv⟩ else 0, fun v hv => by simp [hv, h0], ?_, ?_⟩
    · rw [← hs, ← Finset.sum_coe_sort V]
      simp
    · rw [← hx, ← Finset.sum_coe_sort V]
      simp

/-- Lemma 9 (i), general form: an EF of `F` and a linear map `π` with `π(F) = P` give an EF of `P`
of the same size. -/
lemma isEF_image {κ : Type*} [Fintype κ] {F : Set (κ → ℝ)} {P : Set (ι → ℝ)} {r : ℕ}
    (hF : IsEFOfSize F r) (π : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (hπ : π '' F = P) : IsEFOfSize P r := by
  classical
  obtain ⟨k, p, Eeq, Feq, geq, Ele, Fle, gle, hEF⟩ := hF
  let Pm := LinearMap.toMatrix' π
  -- variables `(z, y) : (κ ⊕ Fin k) → ℝ`
  let Eeq' : Matrix (ι ⊕ Fin p) ι ℝ := fromRows (1 : Matrix ι ι ℝ) 0
  let Feq' : Matrix (ι ⊕ Fin p) (κ ⊕ Fin k) ℝ := fromRows (fromCols (-Pm) 0) (fromCols Eeq Feq)
  let geq' : ι ⊕ Fin p → ℝ := Sum.elim 0 geq
  let Fle' : Matrix (Fin r) (κ ⊕ Fin k) ℝ := fromCols Ele Fle
  suffices key : ∀ x, x ∈ P ↔ ∃ w : κ ⊕ Fin k → ℝ, Eeq' *ᵥ x + Feq' *ᵥ w = geq' ∧
      (0 : Matrix (Fin r) ι ℝ) *ᵥ x + Fle' *ᵥ w ≤ gle by
    simpa using isEF_of (K := κ ⊕ Fin k) (P := P) Eeq' Feq' geq' (0 : Matrix (Fin r) ι ℝ) Fle' gle key
  have hE : ∀ x, Eeq' *ᵥ x = Sum.elim x 0 := fun x => by
    rw [fromRows_mulVec, one_mulVec, zero_mulVec]
  have hF : ∀ w : κ ⊕ Fin k → ℝ, Feq' *ᵥ w =
      Sum.elim (-π (w ∘ Sum.inl)) (Eeq *ᵥ (w ∘ Sum.inl) + Feq *ᵥ (w ∘ Sum.inr)) := fun w => by
    rw [fromRows_mulVec, fromCols_mulVec, fromCols_mulVec, zero_mulVec, add_zero, neg_mulVec,
      LinearMap.toMatrix'_mulVec]
  have hL : ∀ w : κ ⊕ Fin k → ℝ, Fle' *ᵥ w = Ele *ᵥ (w ∘ Sum.inl) + Fle *ᵥ (w ∘ Sum.inr) :=
    fun w => fromCols_mulVec _ _ _
  intro x
  rw [← hπ]
  simp only [hE, hF, hL, zero_mulVec, zero_add]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, h1, h2⟩ := (hEF z).1 hz
    refine ⟨Sum.elim z y, ?_, ?_⟩
    · funext r
      rcases r with i | j
      · simp [geq']
      · simpa [geq'] using congrFun h1 j
    · simpa using h2
  · rintro ⟨w, h1, h2⟩
    refine ⟨w ∘ Sum.inl, (hEF _).2 ⟨w ∘ Sum.inr, ?_, h2⟩, ?_⟩
    · funext j
      simpa [geq'] using congrFun h1 (Sum.inr j)
    · funext i
      have := congrFun h1 (Sum.inl i)
      simp only [Pi.add_apply, Sum.elim_inl, Pi.neg_apply, geq', Pi.zero_apply] at this
      linarith

/-- Adding one equation `c ⬝ᵥ x = δ` to an EF of `Q` gives an EF of the face, same size. -/
lemma isEF_inter_hyperplane {Q : Set (ι → ℝ)} {r : ℕ} (hQ : IsEFOfSize Q r) (c : ι → ℝ) (δ : ℝ) :
    IsEFOfSize {x | x ∈ Q ∧ c ⬝ᵥ x = δ} r := by
  classical
  obtain ⟨k, p, Eeq, Feq, geq, Ele, Fle, gle, hEF⟩ := hQ
  let cRow : Matrix Unit ι ℝ := Matrix.of fun _ i => c i
  have hcRow : ∀ x, cRow *ᵥ x = fun _ => c ⬝ᵥ x := fun x => by funext u; rfl
  let Eeq' : Matrix (Fin p ⊕ Unit) ι ℝ := fromRows Eeq cRow
  let Feq' : Matrix (Fin p ⊕ Unit) (Fin k) ℝ := fromRows Feq 0
  let geq' : Fin p ⊕ Unit → ℝ := Sum.elim geq (fun _ => δ)
  refine isEF_of (K := Fin k) (P := {x | x ∈ Q ∧ c ⬝ᵥ x = δ}) Eeq' Feq' geq' Ele Fle gle
    (fun x => ?_) |> fun h => by simpa using h
  have hE : Eeq' *ᵥ x = Sum.elim (Eeq *ᵥ x) (fun _ => c ⬝ᵥ x) := by
    simp only [Eeq', fromRows_mulVec, hcRow]
  have hF : ∀ y : Fin k → ℝ, Feq' *ᵥ y = Sum.elim (Feq *ᵥ y) 0 := fun y => by
    simp only [Feq', fromRows_mulVec, zero_mulVec]
  simp only [Set.mem_setOf_eq, hEF, hE, hF]
  constructor
  · rintro ⟨⟨y, h1, h2⟩, h3⟩
    refine ⟨y, ?_, h2⟩
    funext r
    rcases r with j | u
    · simpa [geq'] using congrFun h1 j
    · simp [geq', h3]
  · rintro ⟨y, h1, h2⟩
    refine ⟨⟨y, ?_, h2⟩, ?_⟩
    · funext j
      simpa [geq'] using congrFun h1 (Sum.inl j)
    · simpa [geq'] using congrFun h1 (Sum.inr ())

lemma xc_le_of_isEF {P : Set (ι → ℝ)} {r : ℕ} (h : IsEFOfSize P r) :
    extensionComplexity P ≤ r :=
  Nat.sInf_le h

lemma isEF_xc {P : Set (ι → ℝ)} (h : ∃ r, IsEFOfSize P r) :
    IsEFOfSize P (extensionComplexity P) :=
  Nat.sInf_mem h

/-- `xc` does not increase under linear images. -/
lemma xc_image_le {κ : Type*} [Fintype κ] {F : Set (κ → ℝ)} (hF : ∃ r, IsEFOfSize F r)
    (π : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) {P : Set (ι → ℝ)} (hπ : π '' F = P) :
    extensionComplexity P ≤ extensionComplexity F :=
  xc_le_of_isEF (isEF_image (isEF_xc hF) π hπ)

/-- Lemma 9 (i). -/
theorem xc_extension_mono {κ : Type*} [Fintype κ] (P : Set (ι → ℝ))
    (F : Set (κ → ℝ)) (hF : IsPolytope F) (hext : IsExtension F P) :
    extensionComplexity P ≤ extensionComplexity F := by
  obtain ⟨-, π, hπ⟩ := hext
  exact xc_image_le (exists_EF_of_isPolytope hF) π hπ

/-- Lemma 9 (ii), without the polytope hypotheses on the face. -/
theorem xc_face_le {Q F : Set (ι → ℝ)} (hQ : ∃ r, IsEFOfSize Q r) (hface : IsFace Q F) :
    extensionComplexity F ≤ extensionComplexity Q := by
  rcases hface with rfl | ⟨c, δ, -, -, rfl⟩
  · exact le_rfl
  · exact xc_le_of_isEF (isEF_inter_hyperplane (isEF_xc hQ) c δ)

end EF

end XCT

open Matrix ExtensionComplexity.TSP

theorem solution {κ : Type*} [Fintype κ] (Q F : Set (κ → ℝ)) (hQ : IsPolytope Q)
    (hF : IsPolytope F) (hface : IsFace Q F) :
    extensionComplexity F ≤ extensionComplexity Q :=
  XCT.xc_face_le (XCT.exists_EF_of_isPolytope hQ) hface
