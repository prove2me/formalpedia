-- Prove2me | solution 1 for ExtensionComplexity.TSP.tsp_face_extends_cor
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T01:54:43.452144+00:00
-- url     : https://prove2.me/submissions/61ff6657-f66b-4d50-92ae-715ced6a978b

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


open Matrix ExtensionComplexity.TSP Set

namespace XCT

section Cone

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The convex cone generated by a finite family of vectors. -/
def cone (a : κ → ι → ℝ) : Set (ι → ℝ) :=
  {x | ∃ l : κ → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i • a i = x}

/-- Conic Carathéodory: a point of a finitely generated cone is a nonnegative combination of a
linearly independent subfamily. -/
lemma caratheodory (a : κ → ι → ℝ) {x : ι → ℝ} (hx : x ∈ cone a) :
    ∃ s : Finset κ, LinearIndependent ℝ (fun i : s => a i) ∧
      ∃ l : κ → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ i ∉ s, l i = 0) ∧ ∑ i, l i • a i = x := by
  classical
  obtain ⟨l, hl0, hlx⟩ := hx
  suffices H : ∀ m : ℕ, ∀ l : κ → ℝ, (∀ i, 0 ≤ l i) →
      (Finset.univ.filter (fun i => l i ≠ 0)).card = m → ∑ i, l i • a i = x →
      ∃ s : Finset κ, LinearIndependent ℝ (fun i : s => a i) ∧
        ∃ l : κ → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ i ∉ s, l i = 0) ∧ ∑ i, l i • a i = x from
    H _ l hl0 rfl hlx
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro l hl0 hm hlx
  set s := Finset.univ.filter (fun i => l i ≠ 0) with hs
  have hout : ∀ i ∉ s, l i = 0 := fun i hi => by
    by_contra h
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  by_cases hli : LinearIndependent ℝ (fun i : s => a i)
  · exact ⟨s, hli, l, hl0, hout, hlx⟩
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg, i₀, hi₀⟩ := hli
  -- extend `g` by zero, and normalize so that some coefficient is positive
  have hG : ∃ G : κ → ℝ, ∑ i, G i • a i = 0 ∧ (∀ i ∉ s, G i = 0) ∧ ∃ i, 0 < G i := by
    let G₀ : κ → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0
    have hG₀ : ∑ i, G₀ i • a i = 0 := by
      rw [← hg, ← Finset.sum_subset (Finset.subset_univ s)]
      · rw [← Finset.sum_coe_sort s]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [G₀, i.2]
      · intro i _ hi
        simp [G₀, hi]
    have hG₀s : ∀ i ∉ s, G₀ i = 0 := fun i hi => by simp [G₀, hi]
    have hG₀i : G₀ i₀ = g i₀ := by simp [G₀, i₀.2]
    rcases lt_or_gt_of_ne hi₀ with h | h
    · refine ⟨-G₀, ?_, fun i hi => by simp [hG₀s i hi], i₀, ?_⟩
      · simp [neg_smul, Finset.sum_neg_distrib, hG₀]
      · simp [hG₀i, h]
    · exact ⟨G₀, hG₀, hG₀s, i₀, by rw [hG₀i]; exact h⟩
  obtain ⟨G, hGsum, hGs, j₀, hj₀⟩ := hG
  set T := Finset.univ.filter (fun i => 0 < G i)
  have hT : T.Nonempty := ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₀⟩⟩
  obtain ⟨i₁, hi₁T, hmin⟩ := Finset.exists_min_image T (fun i => l i / G i) hT
  have hGi₁ : 0 < G i₁ := (Finset.mem_filter.1 hi₁T).2
  set t := l i₁ / G i₁
  have ht0 : 0 ≤ t := div_nonneg (hl0 _) hGi₁.le
  let l' : κ → ℝ := fun i => l i - t * G i
  have hl'0 : ∀ i, 0 ≤ l' i := by
    intro i
    by_cases hGi : 0 < G i
    · have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hGi⟩)
      have : t * G i ≤ l i := by
        rw [← le_div_iff₀ hGi]
        exact this
      simp only [l']
      linarith
    · push Not at hGi
      have : t * G i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hGi
      simp only [l']
      linarith [hl0 i]
  have hl'x : ∑ i, l' i • a i = x := by
    simp only [l', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hGsum,
      smul_zero, sub_zero, hlx]
  have hl'i₁ : l' i₁ = 0 := by
    simp only [l', t]
    field_simp
    ring
  have hsub : Finset.univ.filter (fun i => l' i ≠ 0) ⊆ s.erase i₁ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_erase]
    refine ⟨fun h => hi.2 (h ▸ hl'i₁), ?_⟩
    by_contra his
    apply hi.2
    simp [l', hout i his, hGs i his]
  have hi₁s : i₁ ∈ s := by
    by_contra h
    exact absurd (hGs i₁ h) hGi₁.ne'
  have hlt : (Finset.univ.filter (fun i => l' i ≠ 0)).card < m := by
    calc _ ≤ (s.erase i₁).card := Finset.card_le_card hsub
      _ < s.card := Finset.card_erase_lt_of_mem hi₁s
      _ = m := hm
  exact ih _ hlt l' hl'0 rfl hl'x

lemma cone_convex (a : κ → ι → ℝ) : Convex ℝ (cone a) := by
  rintro x ⟨l, hl0, rfl⟩ y ⟨l', hl'0, rfl⟩ θ θ' hθ hθ' -
  refine ⟨fun i => θ * l i + θ' * l' i, fun i => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hθ (hl0 i)) (mul_nonneg hθ' (hl'0 i))
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma zero_mem_cone (a : κ → ι → ℝ) : (0 : ι → ℝ) ∈ cone a :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma smul_mem_cone (a : κ → ι → ℝ) (i : κ) {t : ℝ} (ht : 0 ≤ t) : t • a i ∈ cone a := by
  classical
  refine ⟨fun j => if j = i then t else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs <;> simp [ht]
  · simp [ite_smul]

/-- Finitely generated cones are closed. -/
lemma isClosed_cone (a : κ → ι → ℝ) : IsClosed (cone a) := by
  classical
  let L : ∀ s : Finset κ, (s → ℝ) →ₗ[ℝ] (ι → ℝ) := fun s =>
    Fintype.linearCombination ℝ (fun i : s => a i)
  have hcone : cone a = ⋃ s ∈ {s : Finset κ | LinearIndependent ℝ (fun i : s => a i)},
      L s '' {μ | ∀ i, 0 ≤ μ i} := by
    ext x
    simp only [mem_iUnion, mem_image, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, hli, l, hl0, hls, hlx⟩ := caratheodory a hx
      refine ⟨s, hli, fun i => l i, fun i => hl0 i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hlx]
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hls i hi])]
      exact Finset.sum_coe_sort s (fun i => l i • a i)
    · rintro ⟨s, -, μ, hμ0, rfl⟩
      refine ⟨fun i => if h : i ∈ s then μ ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact hμ0 _
        · exact le_rfl
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hi])]
        rw [← Finset.sum_coe_sort s]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [i.2]
  rw [hcone]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun s hs => ?_
  have hker : LinearMap.ker (L s) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro μ hμ
    funext i
    exact Fintype.linearIndependent_iff.1 hs μ (by rw [← Fintype.linearCombination_apply]; exact hμ) i
  have hemb := LinearMap.isClosedEmbedding_of_injective hker
  refine hemb.isClosedMap _ ?_
  have : {μ : s → ℝ | ∀ i, 0 ≤ μ i} = ⋂ i, {μ | 0 ≤ μ i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

/-- **Farkas' lemma** (cone form). -/
theorem farkas (a : κ → ι → ℝ) {c : ι → ℝ} (hc : c ∉ cone a) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ a i ⬝ᵥ y) ∧ c ⬝ᵥ y < 0 := by
  classical
  obtain ⟨f, u, hfu, hu⟩ := geometric_hahn_banach_point_closed (cone_convex a) (isClosed_cone a) hc
  let y : ι → ℝ := fun j => f (fun k => if j = k then 1 else 0)
  have hf : ∀ z : ι → ℝ, f z = z ⬝ᵥ y := fun z => by
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) z
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    rfl
  have hu0 : u < 0 := by simpa using hu 0 (zero_mem_cone a)
  refine ⟨y, fun i => ?_, ?_⟩
  · rw [← hf]
    by_contra hneg
    push Not at hneg
    have ht : 0 ≤ u / f (a i) := div_nonneg_of_nonpos hu0.le hneg.le
    have := hu _ (smul_mem_cone a i ht)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  · rw [← hf]
    linarith

end Cone

section Affine

variable {ι : Type*} [Fintype ι] {m : Type*} [Fintype m]

/-- Weak duality. -/
lemma weak_duality {A : Matrix m ι ℝ} {b : m → ℝ} {lam : m → ℝ} (hlam : 0 ≤ lam) {x : ι → ℝ}
    (hx : A *ᵥ x ≤ b) : (lam ᵥ* A) ⬝ᵥ x ≤ lam ⬝ᵥ b := by
  rw [← dotProduct_mulVec]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hlam i)

/-- **Affine Farkas lemma**: a valid inequality of a nonempty polyhedron `{x | Ax ≤ b}` is
dominated by a nonnegative combination of the rows. -/
theorem affine_farkas (A : Matrix m ι ℝ) (b : m → ℝ) (hne : ∃ x, A *ᵥ x ≤ b) (c : ι → ℝ) (δ : ℝ)
    (hv : ∀ x, A *ᵥ x ≤ b → c ⬝ᵥ x ≤ δ) :
    ∃ lam : m → ℝ, 0 ≤ lam ∧ lam ᵥ* A = c ∧ lam ⬝ᵥ b ≤ δ := by
  classical
  -- homogenize in `Option ι → ℝ`
  let a : Option m → Option ι → ℝ := fun k o =>
    match k, o with
    | some r, some j => A r j
    | some r, none => b r
    | none, some _ => 0
    | none, none => 1
  let c' : Option ι → ℝ := fun o =>
    match o with
    | some j => c j
    | none => δ
  by_cases hc : c' ∈ cone a
  · obtain ⟨l, hl0, hl⟩ := hc
    refine ⟨fun r => l (some r), fun r => hl0 _, ?_, ?_⟩
    · funext j
      have := congrFun hl (some j)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option, a, c',
        mul_zero, zero_add] at this
      rw [← this]
      simp [vecMul, dotProduct]
    · have := congrFun hl none
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option, a, c',
        mul_one] at this
      have h0 := hl0 none
      simp only [dotProduct]
      linarith
  · exfalso
    obtain ⟨y, hy, hcy⟩ := farkas a hc
    let z : ι → ℝ := fun j => y (some j)
    let s : ℝ := y none
    have hs : 0 ≤ s := by
      have := hy none
      simpa [a, dotProduct, Fintype.sum_option, s] using this
    have hrow : ∀ r, 0 ≤ (A *ᵥ z) r + b r * s := by
      intro r
      have := hy (some r)
      simp only [dotProduct, Fintype.sum_option, a] at this
      simp only [mulVec, dotProduct, z, s]
      linarith
    have hcz : c ⬝ᵥ z + δ * s < 0 := by
      simp only [dotProduct, Fintype.sum_option, c'] at hcy
      simp only [dotProduct, z, s]
      linarith
    rcases hs.lt_or_eq with hs | hs
    · -- `x = -(1/s) z` violates validity
      let x : ι → ℝ := (-(1 / s)) • z
      have hx : A *ᵥ x ≤ b := by
        intro r
        simp only [x, mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have := hrow r
        rw [neg_mul, neg_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hs]
        linarith
      have := hv x hx
      simp only [x, dotProduct_smul, smul_eq_mul] at this
      rw [neg_mul, one_div, ← div_eq_inv_mul, neg_le, le_div_iff₀ hs] at this
      linarith
    · -- `s = 0`: a recession direction along which `c` increases
      obtain ⟨x₀, hx₀⟩ := hne
      rw [← hs] at hrow hcz
      simp only [mul_zero, add_zero] at hrow hcz
      set t : ℝ := (|δ - c ⬝ᵥ x₀| + 1) / (-(c ⬝ᵥ z))
      have hpos : 0 < -(c ⬝ᵥ z) := by linarith
      have ht : 0 ≤ t := div_nonneg (by positivity) hpos.le
      let x : ι → ℝ := x₀ - t • z
      have hx : A *ᵥ x ≤ b := by
        intro r
        simp only [x, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [hx₀ r, hrow r, mul_nonneg ht (hrow r)]
      have := hv x hx
      simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
      have hteq : t * (c ⬝ᵥ z) = -(|δ - c ⬝ᵥ x₀| + 1) := by
        simp only [t]
        rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']
        ring
      have := le_abs_self (δ - c ⬝ᵥ x₀)
      linarith

/-- **Lemma 2** (general index types). -/
theorem valid_ineq_comb (A : Matrix m ι ℝ) (b : m → ℝ) (P : Set (ι → ℝ))
    (hP : P = {x | A *ᵥ x ≤ b}) (u : ι → ℝ) (lo hi : ℝ)
    (hlo : IsLeast ((fun x => u ⬝ᵥ x) '' P) lo) (hhi : IsGreatest ((fun x => u ⬝ᵥ x) '' P) hi)
    (hlohi : lo < hi) (c : ι → ℝ) (δ : ℝ) (hvalid : ∀ x ∈ P, c ⬝ᵥ x ≤ δ) :
    ∃ lam : m → ℝ, 0 ≤ lam ∧ lam ᵥ* A = c ∧ lam ⬝ᵥ b = δ := by
  subst hP
  obtain ⟨⟨xlo, hxlo, rfl⟩, hlo'⟩ := hlo
  obtain ⟨⟨xhi, hxhi, rfl⟩, hhi'⟩ := hhi
  have hne : ∃ x, A *ᵥ x ≤ b := ⟨xlo, hxlo⟩
  -- the two directions `±u`
  obtain ⟨l₁, hl₁, hl₁A, hl₁b⟩ := affine_farkas A b hne u (u ⬝ᵥ xhi)
    (fun x hx => hhi' ⟨x, hx, rfl⟩)
  obtain ⟨l₂, hl₂, hl₂A, hl₂b⟩ := affine_farkas A b hne (-u) (-(u ⬝ᵥ xlo))
    (fun x hx => by rw [neg_dotProduct, neg_le_neg_iff]; exact hlo' ⟨x, hx, rfl⟩)
  have hl₁b' : l₁ ⬝ᵥ b = u ⬝ᵥ xhi :=
    le_antisymm hl₁b (by rw [← hl₁A]; exact weak_duality hl₁ hxhi)
  have hl₂b' : l₂ ⬝ᵥ b = -(u ⬝ᵥ xlo) :=
    le_antisymm hl₂b (by rw [← neg_dotProduct, ← hl₂A]; exact weak_duality hl₂ hxlo)
  set ν := l₁ + l₂
  have hν0 : 0 ≤ ν := add_nonneg hl₁ hl₂
  have hνA : ν ᵥ* A = 0 := by simp [ν, add_vecMul, hl₁A, hl₂A]
  have hνb : ν ⬝ᵥ b = u ⬝ᵥ xhi - u ⬝ᵥ xlo := by
    simp only [ν, add_dotProduct, hl₁b', hl₂b']
    ring
  have hgap : 0 < ν ⬝ᵥ b := by rw [hνb]; linarith
  obtain ⟨l, hl0, hlA, hlb⟩ := affine_farkas A b hne c δ hvalid
  set θ := (δ - l ⬝ᵥ b) / (ν ⬝ᵥ b)
  have hθ : 0 ≤ θ := div_nonneg (by linarith) hgap.le
  refine ⟨l + θ • ν, add_nonneg hl0 (smul_nonneg hθ hν0), ?_, ?_⟩
  · rw [add_vecMul, smul_vecMul, hνA, smul_zero, add_zero, hlA]
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    simp only [θ]
    field_simp
    ring

end Affine

section Yannakakis

variable {ι : Type*} [Fintype ι]

/-- The direction of Yannakakis' theorem used for lower bounds: if `P` has an EF of size `r` and
some linear functional is non-constant on `P` and attains its bounds, then for every family of
valid inequalities `c i ⬝ᵥ x ≤ δ i` and points `v j ∈ P`, the slack matrix `δ i - c i ⬝ᵥ v j`
has a nonnegative factorization of rank `r`. -/
theorem nonnegFactorization_of_EF {P : Set (ι → ℝ)} {r : ℕ} (hEF : IsEFOfSize P r)
    (u : ι → ℝ) (lo hi : ℝ) (hlo : IsLeast ((fun x => u ⬝ᵥ x) '' P) lo)
    (hhi : IsGreatest ((fun x => u ⬝ᵥ x) '' P) hi) (hlohi : lo < hi)
    {I J : Type*} (c : I → ι → ℝ) (δ : I → ℝ) (hvalid : ∀ i, ∀ x ∈ P, c i ⬝ᵥ x ≤ δ i)
    (v : J → ι → ℝ) (hv : ∀ j, v j ∈ P) :
    HasNonnegFactorization (Matrix.of fun i j => δ i - c i ⬝ᵥ v j) r := by
  classical
  obtain ⟨k, p, Eeq, Feq, geq, Ele, Fle, gle, hEF⟩ := hEF
  let G : Matrix (Fin p) (ι ⊕ Fin k) ℝ := fromCols Eeq Feq
  let H : Matrix (Fin r) (ι ⊕ Fin k) ℝ := fromCols Ele Fle
  let A' : Matrix ((Fin p ⊕ Fin p) ⊕ Fin r) (ι ⊕ Fin k) ℝ := fromRows (fromRows G (-G)) H
  let b' : (Fin p ⊕ Fin p) ⊕ Fin r → ℝ := Sum.elim (Sum.elim geq (-geq)) gle
  have hG : ∀ z, G *ᵥ z = Eeq *ᵥ (z ∘ Sum.inl) + Feq *ᵥ (z ∘ Sum.inr) := fun z =>
    fromCols_mulVec _ _ _
  have hH : ∀ z, H *ᵥ z = Ele *ᵥ (z ∘ Sum.inl) + Fle *ᵥ (z ∘ Sum.inr) := fun z =>
    fromCols_mulVec _ _ _
  have hA' : ∀ z, A' *ᵥ z = Sum.elim (Sum.elim (G *ᵥ z) (-(G *ᵥ z))) (H *ᵥ z) := fun z => by
    simp only [A', fromRows_mulVec, neg_mulVec]
  have hQ : ∀ z, A' *ᵥ z ≤ b' ↔ G *ᵥ z = geq ∧ H *ᵥ z ≤ gle := by
    intro z
    rw [hA']
    constructor
    · intro h
      refine ⟨funext fun t => le_antisymm (h (Sum.inl (Sum.inl t))) ?_, fun l => h (Sum.inr l)⟩
      have := h (Sum.inl (Sum.inr t))
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, b', neg_le_neg_iff] at this
      exact this
    · rintro ⟨h1, h2⟩ (((t | t)) | l)
      · simp [b', h1]
      · simp [b', h1]
      · exact h2 l
  have hmemP : ∀ x, x ∈ P ↔ ∃ z : ι ⊕ Fin k → ℝ, z ∘ Sum.inl = x ∧ A' *ᵥ z ≤ b' := by
    intro x
    rw [hEF]
    constructor
    · rintro ⟨y, h1, h2⟩
      refine ⟨Sum.elim x y, rfl, (hQ _).2 ⟨?_, ?_⟩⟩
      · rw [hG]; exact h1
      · rw [hH]; exact h2
    · rintro ⟨z, rfl, hz⟩
      obtain ⟨h1, h2⟩ := (hQ z).1 hz
      exact ⟨z ∘ Sum.inr, by rw [← hG]; exact h1, by rw [← hH]; exact h2⟩
  let Q : Set (ι ⊕ Fin k → ℝ) := {z | A' *ᵥ z ≤ b'}
  have hproj : ∀ z ∈ Q, z ∘ Sum.inl ∈ P := fun z hz => (hmemP _).2 ⟨z, rfl, hz⟩
  have hdot : ∀ (w : ι → ℝ) (z : ι ⊕ Fin k → ℝ), Sum.elim w 0 ⬝ᵥ z = w ⬝ᵥ (z ∘ Sum.inl) := by
    intro w z
    simp [dotProduct, Fintype.sum_sum_type]
  have himg : (fun z => Sum.elim u 0 ⬝ᵥ z) '' Q = (fun x => u ⬝ᵥ x) '' P := by
    ext t
    simp only [mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hproj z hz, (hdot u z).symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl, hz⟩ := (hmemP x).1 hx
      exact ⟨z, hz, hdot u z⟩
  have hlam : ∀ i, ∃ lam : (Fin p ⊕ Fin p) ⊕ Fin r → ℝ, 0 ≤ lam ∧
      lam ᵥ* A' = Sum.elim (c i) 0 ∧ lam ⬝ᵥ b' = δ i := by
    intro i
    refine valid_ineq_comb A' b' Q rfl (Sum.elim u 0) lo hi (himg ▸ hlo) (himg ▸ hhi) hlohi
      (Sum.elim (c i) 0) (δ i) fun z hz => ?_
    rw [hdot]
    exact hvalid i _ (hproj z hz)
  choose lam hlam0 hlamA hlamb using hlam
  have hlift : ∀ j, ∃ z : ι ⊕ Fin k → ℝ, z ∘ Sum.inl = v j ∧ A' *ᵥ z ≤ b' := fun j =>
    (hmemP _).1 (hv j)
  choose z hzv hzQ using hlift
  refine ⟨Matrix.of fun i l => lam i (Sum.inr l), Matrix.of fun l j => (gle - H *ᵥ z j) l,
    fun i l => hlam0 i _, fun l j => ?_, ?_⟩
  · have := ((hQ (z j)).1 (hzQ j)).2 l
    simp only [Matrix.of_apply, Pi.sub_apply, sub_nonneg]
    exact this
  · ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have hGz := ((hQ (z j)).1 (hzQ j)).1
    -- `δ i - c i ⬝ᵥ v j = lam i ⬝ᵥ (b' - A' z j)`
    have h1 : δ i - c i ⬝ᵥ v j = lam i ⬝ᵥ (b' - A' *ᵥ z j) := by
      rw [dotProduct_sub, dotProduct_mulVec, hlamA, hlamb, hdot, hzv]
    rw [h1, dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h0 : ∀ t, (b' - A' *ᵥ z j) (Sum.inl (Sum.inl t)) = 0 := fun t => by
      rw [Pi.sub_apply, hA']
      simp [b', hGz]
    have h0' : ∀ t, (b' - A' *ᵥ z j) (Sum.inl (Sum.inr t)) = 0 := fun t => by
      rw [Pi.sub_apply, hA']
      simp [b', hGz]
    simp only [h0, h0', mul_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.sub_apply, hA']
    simp [b']

end Yannakakis

end XCT


open Matrix ExtensionComplexity.TSP Set

namespace XCT

section Lemma6

lemma bitVec_mul_self {n : ℕ} (b : Fin n → Bool) (i : Fin n) : bitVec b i * bitVec b i = bitVec b i := by
  unfold bitVec
  split_ifs <;> simp

lemma bitDot_cast {n : ℕ} (a b : Fin n → Bool) :
    (bitDot a b : ℝ) = ∑ i, bitVec a i * bitVec b i := by
  classical
  unfold bitDot
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bitVec
  cases a i <;> cases b i <;> simp

lemma corIneq_dot_outer {n : ℕ} (a b : Fin n → Bool) :
    corIneqCoeff a ⬝ᵥ outerBits b = 2 * (bitDot a b : ℝ) - (bitDot a b : ℝ) ^ 2 := by
  classical
  rw [bitDot_cast]
  simp only [dotProduct, corIneqCoeff, outerBits, Fintype.sum_prod_type, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [bitVec_mul_self]
      ring
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

lemma one_sub_corIneq {n : ℕ} (a b : Fin n → Bool) :
    1 - corIneqCoeff a ⬝ᵥ outerBits b = matM n a b := by
  rw [corIneq_dot_outer, matM]
  ring

lemma mem_corPolytope_iff {n : ℕ} (x : Fin n × Fin n → ℝ) :
    x ∈ corPolytope n ↔ ∃ w : (Fin n → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ ∑ b, w b = 1 ∧
      ∑ b, w b • outerBits b = x := by
  classical
  unfold corPolytope
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
    exact mem_convexHull_of_exists_fintype w _ hw0 hw1 (fun j => mem_range_self j) hx

/-- **Lemma 6**. -/
theorem cor_valid_inequality_slack {n : ℕ} (a : Fin n → Bool) :
    (∀ x ∈ corPolytope n, corIneqCoeff a ⬝ᵥ x ≤ 1) ∧
      ∀ b : Fin n → Bool, 1 - corIneqCoeff a ⬝ᵥ outerBits b = matM n a b := by
  refine ⟨fun x hx => ?_, one_sub_corIneq a⟩
  obtain ⟨w, hw0, hw1, rfl⟩ := (mem_corPolytope_iff x).1 hx
  rw [dotProduct_sum]
  calc ∑ b, corIneqCoeff a ⬝ᵥ (w b • outerBits b) ≤ ∑ b, w b := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        have : corIneqCoeff a ⬝ᵥ outerBits b ≤ 1 := by
          have := one_sub_corIneq a b
          have h0 : 0 ≤ matM n a b := sq_nonneg _
          linarith
        nlinarith [hw0 b]
    _ = 1 := hw1

end Lemma6

section KW

open Classical in
/-- Number of disjoint pairs in a rectangle. -/
noncomputable def disj (n : ℕ) (A B : Set (Fin n → Bool)) : ℕ :=
  ∑ a, ∑ b, if a ∈ A ∧ b ∈ B ∧ bitDot a b = 0 then 1 else 0

lemma bitDot_cons {n : ℕ} (x y : Bool) (a b : Fin n → Bool) :
    bitDot (Fin.cons x a : Fin (n + 1) → Bool) (Fin.cons y b) =
      (if (x && y) then 1 else 0) + bitDot a b := by
  classical
  unfold bitDot
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

lemma sum_cons {n : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → Bool) → M) :
    ∑ a, f a = ∑ x : Bool, ∑ a : Fin n → Bool, f (Fin.cons x a) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma kw_point {a0 a1 b0 b1 : Prop} [Decidable a0] [Decidable a1] [Decidable b0] [Decidable b1]
    (d : ℕ) (hc : a1 → b1 → 1 + d ≠ 1) :
    ((if a1 ∧ b1 ∧ 1 + d = 0 then 1 else 0) + (if a1 ∧ b0 ∧ d = 0 then 1 else 0)) +
        ((if a0 ∧ b1 ∧ d = 0 then 1 else 0) + (if a0 ∧ b0 ∧ d = 0 then 1 else 0)) ≤
      (if a0 ∧ (b0 ∨ b1) ∧ d = 0 then 1 else 0) + (if (a0 ∨ a1) ∧ b0 ∧ d = 0 then 1 else 0) := by
  have h1 : ¬ (1 + d = 0) := by omega
  by_cases hd : d = 0
  · subst hd
    have hc' : ¬ (a1 ∧ b1) := fun h => hc h.1 h.2 rfl
    by_cases a0 <;> by_cases a1 <;> by_cases b0 <;> by_cases b1 <;> simp_all
  · simp [hd]

/-- **Kaibel–Weltge**: a rectangle avoiding `aᵀb = 1` contains at most `2^n` disjoint pairs. -/
theorem disj_le (n : ℕ) : ∀ A B : Set (Fin n → Bool),
    (∀ a ∈ A, ∀ b ∈ B, bitDot a b ≠ 1) → disj n A B ≤ 2 ^ n := by
  classical
  induction n with
  | zero =>
    intro A B _
    unfold disj
    calc _ ≤ ∑ _a : Fin 0 → Bool, ∑ _b : Fin 0 → Bool, 1 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by split_ifs <;> simp
      _ = 1 := by simp
      _ = 2 ^ 0 := rfl
  | succ n ih =>
    intro A B hAB
    let A0 : Set (Fin n → Bool) := {a | (Fin.cons false a : Fin (n + 1) → Bool) ∈ A}
    let A1 : Set (Fin n → Bool) := {a | (Fin.cons true a : Fin (n + 1) → Bool) ∈ A}
    let B0 : Set (Fin n → Bool) := {b | (Fin.cons false b : Fin (n + 1) → Bool) ∈ B}
    let B1 : Set (Fin n → Bool) := {b | (Fin.cons true b : Fin (n + 1) → Bool) ∈ B}
    have h1 : disj n A0 (B0 ∪ B1) ≤ 2 ^ n := by
      refine ih _ _ fun a ha b hb => ?_
      rcases hb with hb | hb
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
    have h2 : disj n (A0 ∪ A1) B0 ≤ 2 ^ n := by
      refine ih _ _ fun a ha b hb => ?_
      rcases ha with ha | ha
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
    have key : disj (n + 1) A B ≤ disj n A0 (B0 ∪ B1) + disj n (A0 ∪ A1) B0 := by
      unfold disj
      simp only [sum_cons (n := n), Fintype.sum_bool]
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      have hc := hAB (Fin.cons true a) (b := Fin.cons true b)
      simp only [bitDot_cons, Bool.and_self, Bool.and_false, Bool.false_and, if_true,
        Bool.false_eq_true, if_false, zero_add] at hc ⊢
      simp only [mem_union, A0, A1, B0, B1, Set.mem_ofPred_eq]
      exact kw_point _ hc
    calc disj (n + 1) A B ≤ disj n A0 (B0 ∪ B1) + disj n (A0 ∪ A1) B0 := key
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add h1 h2
      _ = 2 ^ (n + 1) := by ring

/-- There are `3^n` disjoint pairs. -/
theorem card_disjoint_pairs (n : ℕ) :
    ∑ a : Fin n → Bool, ∑ b : Fin n → Bool, (if bitDot a b = 0 then 1 else 0 : ℕ) = 3 ^ n := by
  induction n with
  | zero => simp [bitDot]
  | succ n ih =>
    simp only [sum_cons (n := n), Fintype.sum_bool]
    simp only [bitDot_cons, Bool.and_self, Bool.and_false, Bool.false_and, if_true,
      Bool.false_eq_true, if_false, zero_add]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, false_and, if_false, Finset.sum_const_zero,
      zero_add]
    have : ∀ x : Fin n → Bool, (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) +
        (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) +
        (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) =
        3 * ∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0 := fun x => by ring
    simp only [Finset.sum_add_distrib, ih] at *
    ring

lemma suppM_iff {n : ℕ} (a b : Fin n → Bool) : suppM n a b ↔ bitDot a b ≠ 1 := by
  unfold suppM matM
  rw [ne_eq, pow_eq_zero_iff two_ne_zero, sub_eq_zero, not_iff_not]
  constructor
  · intro h
    exact_mod_cast h.symm
  · intro h
    rw [h]
    simp

/-- The counting core of Theorem 1: `3^n ≤ k 2^n`. -/
theorem cover_count {n k : ℕ} (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool))
    (hR : IsOneRectangleCover (suppM n) R) : 3 ^ n ≤ k * 2 ^ n := by
  classical
  obtain ⟨hR1, hR2⟩ := hR
  rw [← card_disjoint_pairs]
  calc ∑ a : Fin n → Bool, ∑ b : Fin n → Bool, (if bitDot a b = 0 then 1 else 0 : ℕ)
      ≤ ∑ a, ∑ b, ∑ l : Fin k,
          (if a ∈ (R l).1 ∧ b ∈ (R l).2 ∧ bitDot a b = 0 then 1 else 0 : ℕ) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs with h
        · obtain ⟨l, hl1, hl2⟩ := hR2 a b ((suppM_iff a b).2 (by rw [h]; exact zero_ne_one))
          exact le_trans (by simp [hl1, hl2, h]) (Finset.single_le_sum (f := fun l =>
            (if a ∈ (R l).1 ∧ b ∈ (R l).2 ∧ bitDot a b = 0 then 1 else 0 : ℕ))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))
        · exact Nat.zero_le _
    _ = ∑ l : Fin k, disj n (R l).1 (R l).2 := by
        unfold disj
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ ∑ _l : Fin k, 2 ^ n := Finset.sum_le_sum fun l _ =>
        disj_le n _ _ fun a ha b hb => (suppM_iff a b).1 (hR1 l a ha b hb)
    _ = k * 2 ^ n := by simp

lemma two_rpow_logb (n : ℕ) : (2 : ℝ) ^ (Real.logb 2 (3 / 2) * n) = (3 / 2 : ℝ) ^ n := by
  rw [Real.rpow_mul (x := (2 : ℝ)) (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
    Real.rpow_natCast]

lemma logb_pos' : 0 < Real.logb 2 (3 / 2 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)

/-- **Theorem 1**. -/
theorem rectangle_cover_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ)
      (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool)),
      IsOneRectangleCover (suppM n) R → (2 : ℝ) ^ (C * n) ≤ k := by
  refine ⟨Real.logb 2 (3 / 2), logb_pos', 0, fun n _ k R hR => ?_⟩
  rw [two_rpow_logb]
  have h := cover_count R hR
  have h' : (3 : ℝ) ^ n ≤ k * 2 ^ n := by exact_mod_cast h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_pow, div_le_iff₀ h2]
  exact h'

end KW

end XCT


open Matrix ExtensionComplexity.TSP Set

namespace XCT

lemma isPolytope_range {ι J : Type*} [Fintype J] (f : J → ι → ℝ) :
    IsPolytope (convexHull ℝ (range f)) := by
  classical
  exact ⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ, image_univ]⟩

section COR

lemma corPolytope_coord {n : ℕ} {x : Fin n × Fin n → ℝ} (hx : x ∈ corPolytope n)
    (p : Fin n × Fin n) : 0 ≤ x p ∧ x p ≤ 1 := by
  obtain ⟨w, hw0, hw1, rfl⟩ := (mem_corPolytope_iff x).1 hx
  have hb : ∀ b : Fin n → Bool, 0 ≤ outerBits b p ∧ outerBits b p ≤ 1 := fun b => by
    unfold outerBits bitVec
    split_ifs <;> norm_num
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · exact Finset.sum_nonneg fun b _ => mul_nonneg (hw0 b) (hb b).1
  · calc ∑ b, w b * outerBits b p ≤ ∑ b, w b :=
          Finset.sum_le_sum fun b _ => mul_le_of_le_one_right (hw0 b) (hb b).2
      _ = 1 := hw1

/-- The correlation polytope needs at least `(3/2)^n` inequalities. -/
theorem xc_cor_ge {n : ℕ} (hn : 1 ≤ n) : (3 / 2 : ℝ) ^ n ≤ extensionComplexity (corPolytope n) := by
  classical
  have hpoly : IsPolytope (corPolytope n) := isPolytope_range _
  have hEF := isEF_xc (exists_EF_of_isPolytope hpoly)
  set r := extensionComplexity (corPolytope n)
  let i₀ : Fin n := ⟨0, hn⟩
  let u : Fin n × Fin n → ℝ := fun p => if p = (i₀, i₀) then 1 else 0
  have hu : ∀ x : Fin n × Fin n → ℝ, u ⬝ᵥ x = x (i₀, i₀) := fun x => by
    simp [u, dotProduct]
  have hmem : ∀ b : Fin n → Bool, outerBits b ∈ corPolytope n := fun b =>
    subset_convexHull ℝ _ (mem_range_self b)
  have hlo : IsLeast ((fun x => u ⬝ᵥ x) '' corPolytope n) 0 := by
    refine ⟨⟨outerBits fun _ => false, hmem _, by simp [hu, outerBits, bitVec]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    show 0 ≤ u ⬝ᵥ x
    rw [hu]
    exact (corPolytope_coord hx _).1
  have hhi : IsGreatest ((fun x => u ⬝ᵥ x) '' corPolytope n) 1 := by
    refine ⟨⟨outerBits fun _ => true, hmem _, by simp [hu, outerBits, bitVec]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    show u ⬝ᵥ x ≤ 1
    rw [hu]
    exact (corPolytope_coord hx _).2
  obtain ⟨T, U, hT, hU, hTU⟩ := nonnegFactorization_of_EF hEF u 0 1 hlo hhi one_pos
    corIneqCoeff (fun _ => 1) (fun a => (cor_valid_inequality_slack a).1) outerBits hmem
  have hM : ∀ a b, matM n a b = ∑ l, T a l * U l b := fun a b => by
    have := congrFun (congrFun hTU a) b
    simp only [Matrix.of_apply, Matrix.mul_apply, one_sub_corIneq] at this
    exact this
  let R : Fin r → Set (Fin n → Bool) × Set (Fin n → Bool) := fun l =>
    ({a | T a l ≠ 0}, {b | U l b ≠ 0})
  have hR : IsOneRectangleCover (suppM n) R := by
    refine ⟨fun l a ha b hb => ?_, fun a b hab => ?_⟩
    · unfold suppM
      rw [hM]
      have hpos : 0 < T a l * U l b :=
        mul_pos (lt_of_le_of_ne (hT a l) (Ne.symm ha)) (lt_of_le_of_ne (hU l b) (Ne.symm hb))
      have := Finset.single_le_sum (f := fun l => T a l * U l b)
        (fun l _ => mul_nonneg (hT a l) (hU l b)) (Finset.mem_univ l)
      exact (lt_of_lt_of_le hpos this).ne'
    · unfold suppM at hab
      rw [hM] at hab
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
      exact ⟨l, left_ne_zero_of_mul hl, right_ne_zero_of_mul hl⟩
  have h := cover_count R hR
  have h' : (3 : ℝ) ^ n ≤ r * 2 ^ n := by exact_mod_cast h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_pow, div_le_iff₀ h2]
  exact h'

end COR

section DeSimone

variable {n : ℕ}

/-- The edge `{u, v}` of `K_m`. -/
def mkEdge {m : ℕ} (u v : Fin m) (h : u ≠ v) : Edge m := ⟨s(u, v), by simpa using h⟩

lemma castSucc_ne_last (i : Fin n) : Fin.castSucc i ≠ Fin.last n := (Fin.castSucc_lt_last i).ne

lemma castSucc_ne {i j : Fin n} (h : i ≠ j) : Fin.castSucc i ≠ Fin.castSucc j :=
  fun h' => h (Fin.castSucc_injective _ h')

/-- De Simone's map `ℝ^{E_{n+1}} → ℝ^{n×n}`. -/
noncomputable def lfun (x : Edge (n + 1) → ℝ) (p : Fin n × Fin n) : ℝ :=
  if h : p.1 = p.2 then x (mkEdge _ _ (castSucc_ne_last p.1))
  else (x (mkEdge _ _ (castSucc_ne_last p.1)) + x (mkEdge _ _ (castSucc_ne_last p.2)) -
    x (mkEdge _ _ (castSucc_ne h))) / 2

noncomputable def Lmap (n : ℕ) : (Edge (n + 1) → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun := lfun
  map_add' x y := by
    funext p
    simp only [lfun, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext p
    simp only [lfun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma Lmap_apply (x : Edge (n + 1) → ℝ) (p : Fin n × Fin n) : Lmap n x p = lfun x p := rfl

lemma Lmap_injective : Function.Injective (Lmap n) := by
  intro x y hxy
  have hd : ∀ i, x (mkEdge _ _ (castSucc_ne_last i)) = y (mkEdge _ _ (castSucc_ne_last i)) := by
    intro i
    have := congrFun hxy (i, i)
    simpa [Lmap_apply, lfun] using this
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := by simpa using he
  induction u using Fin.lastCases with
  | last =>
    induction v using Fin.lastCases with
    | last => exact absurd rfl huv
    | cast j =>
      have := hd j
      have he' : (⟨s(Fin.last n, Fin.castSucc j), he⟩ : Edge (n + 1)) =
          mkEdge _ _ (castSucc_ne_last j) := Subtype.ext Sym2.eq_swap
      rw [he']
      exact this
  | cast i =>
    induction v using Fin.lastCases with
    | last => exact hd i
    | cast j =>
      have hij : i ≠ j := fun h => huv (h ▸ rfl)
      have h3 := congrFun hxy (i, j)
      simp only [Lmap_apply, lfun, dif_neg hij] at h3
      have he' : (⟨s(Fin.castSucc i, Fin.castSucc j), he⟩ : Edge (n + 1)) =
          mkEdge _ _ (castSucc_ne hij) := rfl
      rw [he']
      linarith [hd i, hd j]

lemma charVec_cut_mkEdge {m : ℕ} (X : Finset (Fin m)) (u v : Fin m) (h : u ≠ v) :
    charVec (cutSet X) (mkEdge u v h) = if (u ∈ X ↔ v ∈ X) then 0 else 1 := by
  classical
  unfold charVec
  have hmem : mkEdge u v h ∈ cutSet X ↔ ¬ (u ∈ X ↔ v ∈ X) := by
    simp only [cutSet, Set.mem_ofPred_eq, mkEdge, Sym2.eq_iff]
    constructor
    · rintro ⟨u', v', hu', hv', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> tauto
    · intro hn
      by_cases hu : u ∈ X
      · exact ⟨u, v, hu, fun hv => hn ⟨fun _ => hv, fun _ => hu⟩, Or.inl ⟨rfl, rfl⟩⟩
      · have hv : v ∈ X := by by_contra hv; exact hn ⟨fun h => absurd h hu, fun h => absurd h hv⟩
        exact ⟨v, u, hv, hu, Or.inr ⟨rfl, rfl⟩⟩
  by_cases hc : (u ∈ X ↔ v ∈ X)
  · rw [if_neg (by rw [hmem]; exact not_not.2 hc), if_pos hc]
  · rw [if_pos (hmem.2 hc), if_neg hc]

lemma Lmap_cut (X : Finset (Fin (n + 1))) :
    Lmap n (charVec (cutSet X)) =
      outerBits (fun i => decide ¬ (Fin.castSucc i ∈ X ↔ Fin.last n ∈ X)) := by
  classical
  funext p
  obtain ⟨i, j⟩ := p
  simp only [Lmap_apply, lfun, outerBits, bitVec]
  split_ifs with hij <;> simp only [charVec_cut_mkEdge] <;>
    by_cases hi : Fin.castSucc i ∈ X <;> by_cases hl : Fin.last n ∈ X <;>
    simp_all <;> by_cases hj : Fin.castSucc j ∈ X <;> simp_all

/-- **Theorem 5** (De Simone). -/
theorem cor_linearly_isomorphic_cut (n : ℕ) :
    ∃ L : (Edge (n + 1) → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      Function.Injective L ∧ L '' cutPolytope (n + 1) = corPolytope n := by
  classical
  refine ⟨Lmap n, Lmap_injective, ?_⟩
  unfold cutPolytope corPolytope
  rw [LinearMap.image_convexHull, ← range_comp]
  congr 1
  ext y
  simp only [mem_range, Function.comp_apply]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨_, (Lmap_cut X).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(Finset.univ.filter fun i => b i = true).map Fin.castSuccEmb, ?_⟩
    rw [Lmap_cut]
    congr 1
    funext i
    have hl : Fin.last n ∉ (Finset.univ.filter fun i => b i = true).map Fin.castSuccEmb := by
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb, not_exists, not_and]
      intro j _ h
      exact castSucc_ne_last j h
    have hi : Fin.castSucc i ∈ (Finset.univ.filter fun i => b i = true).map Fin.castSuccEmb ↔
        b i = true := by
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      constructor
      · rintro ⟨j, hj, h⟩
        rwa [Fin.castSucc_injective _ h] at hj
      · intro h
        exact ⟨i, h, rfl⟩
    simp only [hl, hi, iff_false]
    cases b i <;> simp

lemma xc_cut_eq_cor (n : ℕ) :
    extensionComplexity (cutPolytope (n + 1)) = extensionComplexity (corPolytope n) := by
  obtain ⟨L, hL, hLim⟩ := cor_linearly_isomorphic_cut n
  have hker : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.2 hL
  obtain ⟨L', hL'⟩ := L.exists_leftInverse_of_injective hker
  have hcut : ∃ r, IsEFOfSize (cutPolytope (n + 1)) r :=
    exists_EF_of_isPolytope (isPolytope_range _)
  have hcor : ∃ r, IsEFOfSize (corPolytope n) r := exists_EF_of_isPolytope (isPolytope_range _)
  refine le_antisymm (xc_image_le hcor L' ?_) (xc_image_le hcut L hLim)
  rw [← hLim, ← image_comp]
  have : (L' ∘ L) = id := by
    funext x
    exact congrFun (congrArg DFunLike.coe hL') x
  rw [this, image_id]

/-- **Theorem 7**. -/
theorem xc_cor_lower_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      extensionComplexity (cutPolytope (n + 1)) = extensionComplexity (corPolytope n) ∧
        (2 : ℝ) ^ (C * n) ≤ (extensionComplexity (corPolytope n) : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ (C * n) ≤ (extensionComplexity (cutPolytope n) : ℝ)) := by
  refine ⟨⟨Real.logb 2 (3 / 2), logb_pos', fun n hn => ⟨xc_cut_eq_cor n, ?_⟩⟩,
    ⟨Real.logb 2 (3 / 2) / 2, by linarith [logb_pos'], 2, fun n hn => ?_⟩⟩
  · rw [two_rpow_logb]
    exact xc_cor_ge hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    rw [xc_cut_eq_cor]
    calc (2 : ℝ) ^ (Real.logb 2 (3 / 2) / 2 * ((m + 1 : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ (Real.logb 2 (3 / 2) * m) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hC := logb_pos'
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          push_cast
          nlinarith
      _ = (3 / 2 : ℝ) ^ m := two_rpow_logb m
      _ ≤ _ := xc_cor_ge hm

end DeSimone

end XCT


open Matrix ExtensionComplexity.TSP Set

namespace XCT

section FaceHull

variable {ι : Type*} [Fintype ι]

/-- The face of `conv S` cut out by a valid inequality is the hull of the tight points of `S`. -/
lemma face_convexHull (S : Set (ι → ℝ)) (c : ι → ℝ) (δ : ℝ) (hv : ∀ s ∈ S, c ⬝ᵥ s ≤ δ) :
    {x | x ∈ convexHull ℝ S ∧ c ⬝ᵥ x = δ} = convexHull ℝ {s | s ∈ S ∧ c ⬝ᵥ s = δ} := by
  classical
  ext x
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hx, hcx⟩
    obtain ⟨J, _, w, z, hw0, hw1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hx
    -- every point with positive weight is tight
    have hsum : ∑ j, w j * (δ - c ⬝ᵥ z j) = 0 := by
      have : ∑ j, w j * (δ - c ⬝ᵥ z j) = δ * ∑ j, w j - c ⬝ᵥ ∑ j, w j • z j := by
        rw [dotProduct_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        ring
      rw [this, hw1, hcx]
      ring
    have hterm : ∀ j, w j * (δ - c ⬝ᵥ z j) = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (hw0 j) (sub_nonneg.2 (hv _ (hz j)))).1 hsum j (Finset.mem_univ j)
    obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hw1
    have htight : ∀ j, w j ≠ 0 → c ⬝ᵥ z j = δ := fun j hj => by
      have := hterm j
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hj
      · linarith
    let z' : J → ι → ℝ := fun j => if w j = 0 then z j₀ else z j
    have hz' : ∀ j, z' j ∈ {s | s ∈ S ∧ c ⬝ᵥ s = δ} := fun j => by
      by_cases hj : w j = 0
      · simp only [z', if_pos hj]; exact ⟨hz j₀, htight j₀ hj₀⟩
      · simp only [z', if_neg hj]; exact ⟨hz j, htight j hj⟩
    refine mem_convexHull_of_exists_fintype w z' hw0 hw1 hz' ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : w j = 0
    · simp [hj]
    · simp [z', hj]
  · intro hx
    refine ⟨convexHull_mono (fun s hs => hs.1) hx, ?_⟩
    obtain ⟨J, _, w, z, hw0, hw1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hx
    rw [dotProduct_sum]
    simp_rw [dotProduct_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => by rw [(hz j).2], ← Finset.sum_mul, hw1, one_mul]

lemma isPolytope_of_finite {S : Set (ι → ℝ)} (hS : S.Finite) : IsPolytope (convexHull ℝ S) :=
  ⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]⟩

lemma isPolytope_image {κ : Type*} {P : Set (ι → ℝ)} (hP : IsPolytope P)
    (π : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : IsPolytope (π '' P) := by
  classical
  obtain ⟨V, rfl⟩ := hP
  exact ⟨V.image π, by rw [LinearMap.image_convexHull, Finset.coe_image]⟩

end FaceHull

section Reindex

variable {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W)

/-- Reindexing of coordinates along `e`. -/
def re : (V → ℝ) →ₗ[ℝ] (W → ℝ) := LinearMap.funLeft ℝ ℝ e.symm

lemma re_apply (x : V → ℝ) (w : W) : re e x w = x (e.symm w) := rfl

lemma re_dot (c x : V → ℝ) : re e c ⬝ᵥ re e x = c ⬝ᵥ x := by
  simp only [dotProduct, re_apply]
  exact Equiv.sum_comp e.symm (fun v => c v * x v)

lemma re_injective : Function.Injective (re e) := by
  intro x y h
  funext v
  have := congrFun h (e v)
  simpa [re_apply] using this

lemma re_symm_re (x : V → ℝ) : re e.symm (re e x) = x := by
  funext v
  simp [re_apply]

lemma isFace_re {P F : Set (V → ℝ)} (h : IsFace P F) : IsFace (re e '' P) (re e '' F) := by
  rcases h with rfl | ⟨c, δ, hc, hv, rfl⟩
  · exact Or.inl rfl
  refine Or.inr ⟨re e c, δ, fun h0 => hc ?_, ?_, ?_⟩
  · have := congrArg (re e.symm) h0
    rwa [re_symm_re, map_zero] at this
  · rintro _ ⟨x, hx, rfl⟩
    rw [re_dot]
    exact hv x hx
  · ext y
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [re_dot]; exact hcx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hcx⟩
      exact ⟨x, ⟨hx, by rw [re_dot] at hcx; exact hcx⟩, rfl⟩

lemma isExtension_re {ι : Type*} {F : Set (V → ℝ)} {P : Set (ι → ℝ)} (h : IsExtension F P) :
    IsExtension (re e '' F) P := by
  obtain ⟨hF, π, hπ⟩ := h
  refine ⟨isPolytope_image hF _, π ∘ₗ re e.symm, ?_⟩
  rw [← hπ, ← image_comp]
  congr 1
  funext x
  simp [re_symm_re]

end Reindex

end XCT


open Set Function

namespace XCT

section TourGen

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a Hamiltonian cycle every vertex has exactly two cycle-neighbours. -/
lemma ham_deg2 {a : V} {c : (⊤ : SimpleGraph V).Walk a a} (hc : c.IsHamiltonianCycle) (v : V) :
    ∃ w₁ w₂, w₁ ≠ w₂ ∧ ∀ w, s(v, w) ∈ c.edges ↔ (w = w₁ ∨ w = w₂) := by
  have h := hc.isCycle.ncard_neighborSet_toSubgraph_eq_two (hc.mem_support v)
  obtain ⟨w₁, w₂, hne, hset⟩ := Set.ncard_eq_two.1 h
  refine ⟨w₁, w₂, hne, fun w => ?_⟩
  rw [← SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  have : w ∈ c.toSubgraph.neighborSet v ↔ w ∈ ({w₁, w₂} : Set V) := by rw [hset]
  simpa using this

/-- A Hamiltonian cycle has an edge leaving every proper nonempty vertex set. -/
lemma ham_cross {a : V} {c : (⊤ : SimpleGraph V).Walk a a} (hc : c.IsHamiltonianCycle)
    (T : Set V) {u w : V} (hu : u ∈ T) (hw : w ∉ T) : ∃ x ∈ T, ∃ y ∉ T, s(x, y) ∈ c.edges := by
  by_cases ha : a ∈ T
  · let p := c.takeUntil w (hc.mem_support w)
    obtain ⟨d, hd, h1, h2⟩ := p.exists_boundary_dart T ha hw
    refine ⟨d.fst, h1, d.snd, h2, c.edges_takeUntil_subset_edges (hc.mem_support w) ?_⟩
    rw [SimpleGraph.Walk.edges_eq_map_darts]
    exact List.mem_map_of_mem hd
  · let p := c.takeUntil u (hc.mem_support u)
    obtain ⟨d, hd, h1, h2⟩ := p.exists_boundary_dart Tᶜ ha (by simpa using hu)
    refine ⟨d.snd, by simpa using h2, d.fst, h1, ?_⟩
    rw [Sym2.eq_swap]
    refine c.edges_takeUntil_subset_edges (hc.mem_support u) ?_
    rw [SimpleGraph.Walk.edges_eq_map_darts]
    exact List.mem_map_of_mem hd

end TourGen

section Build

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The walk `x, σ x, …, σ^k x` in the complete graph. -/
def iterWalk (σ : V → V) (hσ : ∀ x, σ x ≠ x) : (k : ℕ) → (x : V) →
    (⊤ : SimpleGraph V).Walk x (σ^[k] x)
  | 0, _ => SimpleGraph.Walk.nil
  | k + 1, x => SimpleGraph.Walk.cons (by simpa using (hσ x).symm) (iterWalk σ hσ k (σ x))

omit [Fintype V] in
lemma iterWalk_succ_support (σ : V → V) (hσ : ∀ x, σ x ≠ x) (k : ℕ) (x : V) :
    (iterWalk σ hσ (k + 1) x).support = x :: (iterWalk σ hσ k (σ x)).support := rfl

omit [Fintype V] in
lemma iterWalk_succ_edges (σ : V → V) (hσ : ∀ x, σ x ≠ x) (k : ℕ) (x : V) :
    (iterWalk σ hσ (k + 1) x).edges = s(x, σ x) :: (iterWalk σ hσ k (σ x)).edges := rfl

omit [Fintype V] in
lemma iterWalk_support (σ : V → V) (hσ : ∀ x, σ x ≠ x) (k : ℕ) (x : V) :
    (iterWalk σ hσ k x).support = (List.range (k + 1)).map (fun i => σ^[i] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iterWalk_succ_support, ih]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

omit [Fintype V] in
lemma iterWalk_edges (σ : V → V) (hσ : ∀ x, σ x ≠ x) (k : ℕ) (x : V) :
    (iterWalk σ hσ k x).edges = (List.range k).map (fun i => s(σ^[i] x, σ^[i + 1] x)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iterWalk_succ_edges, ih]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

omit [Fintype V] in
lemma iterWalk_length (σ : V → V) (hσ : ∀ x, σ x ≠ x) (k : ℕ) (x : V) :
    (iterWalk σ hσ k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih (σ x))

/-- A successor function with a single orbit through all `≥ 3` vertices gives a Hamiltonian cycle
whose edges are exactly the pairs `{y, σ y}`. -/
theorem exists_ham_of_cycle (σ : V → V) (hinj : Injective σ) (x₀ : V)
    (hreach : ∀ y, ∃ k, σ^[k] x₀ = y) (h3 : 3 ≤ Fintype.card V) :
    ∃ c : (⊤ : SimpleGraph V).Walk x₀ x₀, c.IsHamiltonianCycle ∧
      ∀ e, e ∈ c.edges ↔ ∃ y, e = s(y, σ y) := by
  classical
  set P := minimalPeriod σ x₀ with hPdef
  have hper : x₀ ∈ periodicPts σ := hinj.mem_periodicPts x₀
  have hP0 : 0 < P := minimalPeriod_pos_of_mem_periodicPts hper
  have hinjOn : InjOn (fun i => σ^[i] x₀) (Iio P) := iterate_injOn_Iio_minimalPeriod
  have hI : ∀ i j, i < P → j < P → σ^[i] x₀ = σ^[j] x₀ → i = j := fun i j hi hj h =>
    hinjOn (show i ∈ Iio P from hi) (show j ∈ Iio P from hj) h
  have hsurj : ∀ y, ∃ i < P, σ^[i] x₀ = y := fun y => by
    obtain ⟨k, rfl⟩ := hreach y
    exact ⟨k % P, Nat.mod_lt _ hP0, iterate_mod_minimalPeriod_eq⟩
  have hPN : P = Fintype.card V := by
    let f : Fin P → V := fun i => σ^[i] x₀
    have hf : Bijective f := by
      refine ⟨fun i j h => Fin.ext (hI i j i.2 j.2 h), fun y => ?_⟩
      obtain ⟨i, hi, rfl⟩ := hsurj y
      exact ⟨⟨i, hi⟩, rfl⟩
    rw [← Fintype.card_fin P]
    exact Fintype.card_congr (Equiv.ofBijective f hf)
  have hP3 : 3 ≤ P := hPN ▸ h3
  have hPeq : σ^[P] x₀ = x₀ := iterate_minimalPeriod
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hsurj x
    have hall : ∀ j, σ^[j] (σ^[i] x₀) = σ^[i] x₀ := fun j => by
      induction j with
      | zero => rfl
      | succ j ih => rw [iterate_succ_apply', ih, hx]
    have h0 : σ^[P - i] (σ^[i] x₀) = x₀ := by
      rw [← iterate_add_apply, Nat.sub_add_cancel hi.le, hPeq]
    have hx0 : σ^[i] x₀ = x₀ := (hall _).symm.trans h0
    have h1 : σ^[1] x₀ = σ^[0] x₀ := by
      have := hall 1
      rw [hx0] at this
      exact this
    exact absurd (hI 1 0 (by omega) (by omega) h1) (by norm_num)
  obtain ⟨P', hP'⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  have e0 : σ^[P'] (σ x₀) = x₀ := by
    rw [← iterate_succ_apply, Nat.succ_eq_add_one, ← hP', hPeq]
  have hadj : (⊤ : SimpleGraph V).Adj x₀ (σ x₀) := by simpa using (hfix x₀).symm
  have hshift : ∀ i, σ^[i] (σ x₀) = σ^[i + 1] x₀ := fun i => (iterate_succ_apply σ i x₀).symm
  refine ⟨SimpleGraph.Walk.cons hadj ((iterWalk σ hfix P' (σ x₀)).copy rfl e0), ?_, ?_⟩
  · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
    refine ⟨?_, by rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_copy,
      iterWalk_length, ← hPN, hP']⟩
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · rw [SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.isPath_def, iterWalk_support]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      rw [hshift, hshift] at hij
      have hx : σ^[P] x₀ = σ^[0] x₀ := hPeq
      rcases Nat.lt_or_ge (i + 1) P with hi1 | hi1 <;> rcases Nat.lt_or_ge (j + 1) P with hj1 | hj1
      · have := hI (i + 1) (j + 1) hi1 hj1 hij
        omega
      · have hj2 : j + 1 = P := by omega
        rw [hj2, hx] at hij
        have := hI (i + 1) 0 hi1 hP0 hij
        omega
      · have hi2 : i + 1 = P := by omega
        rw [hi2, hx] at hij
        have := hI 0 (j + 1) hP0 hj1 hij
        omega
      · omega
    · rw [SimpleGraph.Walk.edges_copy, iterWalk_edges]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi heq
      rw [hshift, hshift, Sym2.eq_iff] at heq
      rcases heq with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := hI (i + 1) 0 (by omega) (by omega) h1
        omega
      · have hi0 := hI (i + 1) 1 (by omega) (by omega) h1
        have hi0' : i = 0 := by omega
        subst hi0'
        have := hI 2 0 (by omega) (by omega) h2
        omega
  · intro e
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_copy, iterWalk_edges]
    simp only [List.mem_cons, List.mem_map, List.mem_range]
    constructor
    · rintro (rfl | ⟨i, -, rfl⟩)
      · exact ⟨x₀, rfl⟩
      · exact ⟨σ^[i] (σ x₀), by rw [iterate_succ_apply' σ i (σ x₀)]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨i, hi, rfl⟩ := hsurj y
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact Or.inl rfl
      · refine Or.inr ⟨i - 1, by omega, ?_⟩
        have : σ^[i - 1] (σ x₀) = σ^[i] x₀ := by
          rw [hshift]; congr 1; omega
        rw [iterate_succ_apply' σ (i - 1) (σ x₀), this]

end Build

end XCT


open Matrix ExtensionComplexity.TSP Set Function

namespace XCT

section PathExp

variable {X : Type*} [Fintype X] [DecidableEq X] (A : X → X → Prop) (μ : X → ℕ)

/-- Vertices of the path expansion: node `v` becomes the path `(v,0) - (v,1) - ⋯ - (v, μ v + 1)`. -/
abbrev PV := Σ v : X, Fin (μ v + 2)

variable {μ} in
def pin (v : X) : PV μ := ⟨v, 0⟩

variable {μ} in
def pout (v : X) : PV μ := ⟨v, Fin.last _⟩

/-- Edges of the path expansion: path edges, and `out u - in w` for arcs `u → w`. -/
def gE (a b : PV μ) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
    (a.2.val = μ a.1 + 1 ∧ b.2.val = 0 ∧ A a.1 b.1) ∨
    (b.2.val = μ b.1 + 1 ∧ a.2.val = 0 ∧ A b.1 a.1)

variable {A μ}

lemma gE_symm {a b : PV μ} (h : gE A μ a b) : gE A μ b a := by
  unfold gE at *
  rcases h with ⟨h1, h2 | h2⟩ | h | h
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

section Sound

variable (R : PV μ → PV μ → Prop)
  (hdeg : ∀ a, ∃ w₁ w₂, w₁ ≠ w₂ ∧ ∀ w, R a w ↔ (w = w₁ ∨ w = w₂))
  (hsymm : ∀ a b, R a b → R b a)
  (hsub : ∀ a b, R a b → gE A μ a b)
  (hμ : ∀ v, 1 ≤ μ v)

include hdeg hsub in
/-- A mid vertex is joined to both path neighbours. -/
lemma R_mid (v : X) (i : ℕ) (hi0 : 0 < i) (hi : i < μ v + 1) :
    R ⟨v, ⟨i, by omega⟩⟩ ⟨v, ⟨i - 1, by omega⟩⟩ ∧ R ⟨v, ⟨i, by omega⟩⟩ ⟨v, ⟨i + 1, by omega⟩⟩ := by
  obtain ⟨w₁, w₂, hne, hw⟩ := hdeg ⟨v, ⟨i, by omega⟩⟩
  have hnb : ∀ w, R ⟨v, ⟨i, by omega⟩⟩ w →
      w = ⟨v, ⟨i - 1, by omega⟩⟩ ∨ w = ⟨v, ⟨i + 1, by omega⟩⟩ := by
    intro w hw'
    have h := hsub _ _ hw'
    obtain ⟨wv, wi⟩ := w
    unfold gE at h
    simp only at h
    rcases h with ⟨rfl, h | h⟩ | h | h
    · right; congr 1; ext; simp <;> omega
    · left; congr 1; ext; simp <;> omega
    · omega
    · omega
  have h1 := hnb w₁ ((hw w₁).2 (Or.inl rfl))
  have h2 := hnb w₂ ((hw w₂).2 (Or.inr rfl))
  have hd : (⟨v, ⟨i - 1, by omega⟩⟩ : PV μ) ≠ ⟨v, ⟨i + 1, by omega⟩⟩ := by
    intro h; have := congrArg (fun a : PV μ => a.2.val) h; simp at this <;> omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨(hw _).2 (Or.inl h1.symm), (hw _).2 (Or.inr h2.symm)⟩
  · exact ⟨(hw _).2 (Or.inr h2.symm), (hw _).2 (Or.inl h1.symm)⟩
  · exact absurd (h1.trans h2.symm) hne

include hsub in
lemma R_out_cases {v : X} {w : PV μ} (h : R (pout v) w) :
    w = ⟨v, ⟨μ v, by omega⟩⟩ ∨ (w = pin w.1 ∧ A v w.1) := by
  have h' := hsub _ _ h
  obtain ⟨wv, wi⟩ := w
  have hwi := wi.isLt
  unfold gE pout at h'
  simp only [Fin.val_last] at h'
  rcases h' with ⟨rfl, h | h⟩ | h | h
  · omega
  · left; congr 1; ext; simp <;> omega
  · right; exact ⟨Sigma.ext rfl (heq_of_eq (Fin.ext (by simp only [pin, Fin.val_zero]; exact h.2.1))), h.2.2⟩
  · omega

include hsub hμ in
lemma R_in_cases {v : X} {w : PV μ} (h : R (pin v) w) :
    w = ⟨v, ⟨1, by have := hμ v; omega⟩⟩ ∨ (w = pout w.1 ∧ A w.1 v) := by
  have h' := hsub _ _ h
  obtain ⟨wv, wi⟩ := w
  have hwi := wi.isLt
  have hμv := hμ v
  unfold gE pin at h'
  simp only [Fin.val_zero] at h'
  rcases h' with ⟨rfl, h | h⟩ | h | h
  · left; congr 1; ext; simp <;> omega
  · omega
  · omega
  · right; exact ⟨Sigma.ext rfl (heq_of_eq (Fin.ext (by simp only [pout, Fin.val_last]; exact h.1))), h.2.2⟩

include hdeg hsub hsymm hμ in
/-- From a tour of the path expansion: the successor map on nodes. -/
lemma exists_succ_of_tour :
    ∃ τ : X → X, Injective τ ∧ (∀ v, A v (τ v)) ∧ (∀ v w, R (pout v) (pin w) ↔ τ v = w) := by
  classical
  have hmid : ∀ v, R (pout v) ⟨v, ⟨μ v, by omega⟩⟩ := fun v => by
    have := (R_mid R hdeg hsub v (μ v) (hμ v) (by omega)).2
    exact hsymm _ _ this
  -- the other neighbour of `out v`
  have hother : ∀ v, ∃ w, A v w ∧ R (pout v) (pin w) ∧
      ∀ w', R (pout v) (pin w') → w' = w := by
    intro v
    obtain ⟨w₁, w₂, hne, hw⟩ := hdeg (pout v)
    have hm := (hw _).1 (hmid v)
    -- the neighbour different from the mid vertex
    obtain ⟨x, hx, hxm⟩ : ∃ x, R (pout v) x ∧ x ≠ ⟨v, ⟨μ v, by omega⟩⟩ := by
      rcases hm with hm | hm
      · exact ⟨w₂, (hw _).2 (Or.inr rfl), fun h => hne (hm.symm.trans h.symm)⟩
      · exact ⟨w₁, (hw _).2 (Or.inl rfl), fun h => hne (h.trans hm)⟩
    rcases R_out_cases R hsub hx with h | ⟨hxin, hA⟩
    · exact absurd h hxm
    refine ⟨x.1, hA, hxin ▸ hx, fun w' hw' => ?_⟩
    have hpm : (pin w' : PV μ) ≠ ⟨v, ⟨μ v, by omega⟩⟩ := by
      unfold pin; intro h; have := congrArg (fun a : PV μ => a.2.val) h; simp at this
      have := hμ v; omega
    have h3 := (hw _).1 hw'
    have h4 := (hw _).1 hx
    have h5 := (hw _).1 (hmid v)
    -- `pin w'`, `x`, and the mid vertex are among two values
    have : pin w' = x := by
      rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
        first
        | exact h3.trans h4.symm
        | exact absurd (h3.trans h5.symm) hpm
        | exact absurd (h4.trans h5.symm) hxm
    rw [hxin] at this
    unfold pin at this
    exact (Sigma.mk.inj_iff.1 this).1
  choose τ hτA hτR hτu using hother
  refine ⟨τ, fun v v' h => ?_, hτA, fun v w => ⟨fun h => (hτu v w h).symm, fun h => h ▸ hτR v⟩⟩
  -- injectivity: `in (τ v)` has neighbours `out v`, `out v'`, `(τ v, 1)`
  set w := τ v
  have h1 : R (pin w) (pout v) := hsymm _ _ (hτR v)
  have h2 : R (pin w) (pout v') := hsymm _ _ (h ▸ hτR v')
  have h3 : R (pin w) ⟨w, ⟨1, by have := hμ w; omega⟩⟩ := by
    have := (R_mid R hdeg hsub w 1 (by norm_num) (by have := hμ w; omega)).1
    exact hsymm _ _ this
  obtain ⟨w₁, w₂, hne, hw⟩ := hdeg (pin w)
  have hp1 : (pout v : PV μ) ≠ ⟨w, ⟨1, by have := hμ w; omega⟩⟩ := by
    unfold pout; intro h; have := congrArg (fun a : PV μ => a.2.val) h; simp at this
    have := hμ v; omega
  have hp2 : (pout v' : PV μ) ≠ ⟨w, ⟨1, by have := hμ w; omega⟩⟩ := by
    unfold pout; intro h; have := congrArg (fun a : PV μ => a.2.val) h; simp at this
    have := hμ v'; omega
  have e1 := (hw _).1 h1
  have e2 := (hw _).1 h2
  have e3 := (hw _).1 h3
  have : (pout v : PV μ) = pout v' := by
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3 <;>
      first
      | exact e1.trans e2.symm
      | exact absurd (e1.trans e3.symm) hp1
      | exact absurd (e2.trans e3.symm) hp2
  unfold pout at this
  exact (Sigma.mk.inj_iff.1 this).1

include hsub in
/-- Connectivity of a tour gives connectivity of the successor map. -/
lemma succ_connected (τ : X → X) (hτ : Injective τ) (hR : ∀ v w, R (pout v) (pin w) ↔ τ v = w)
    (hsymm : ∀ a b, R a b → R b a)
    (hconn : ∀ T : Set (PV μ), ∀ u ∈ T, ∀ w ∉ T, ∃ x ∈ T, ∃ y ∉ T, R x y)
    (S : Set X) (hS : S.Nonempty) (hSτ : ∀ v ∈ S, τ v ∈ S) : S = univ := by
  classical
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨v₁, hv₁⟩ : ∃ v, v ∉ S := by
    by_contra h; push Not at h; exact hne (eq_univ_of_forall h)
  -- `τ` restricted to `S` is onto `S`
  have hsurj : ∀ v ∈ S, ∃ u ∈ S, τ u = v := by
    let f : S → S := fun x => ⟨τ x, hSτ x x.2⟩
    have hf : Injective f := fun x y h => Subtype.ext (hτ (congrArg Subtype.val h))
    have hfs := Finite.surjective_of_injective hf
    intro v hv
    obtain ⟨u, hu⟩ := hfs ⟨v, hv⟩
    exact ⟨u, u.2, congrArg Subtype.val hu⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hconn {a | a.1 ∈ S} (pin v₀) hv₀ (pin v₁) hv₁
  simp only [Set.mem_ofPred_eq] at hx hy
  have h := hsub _ _ hxy
  obtain ⟨xv, xi⟩ := x
  obtain ⟨yv, yi⟩ := y
  unfold gE at h
  simp only at h hx hy
  rcases h with ⟨rfl, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact hy hx
  · have hxo : (⟨xv, xi⟩ : PV μ) = pout xv := by
      unfold pout; congr 1; ext; simp [h1]
    have hyi : (⟨yv, yi⟩ : PV μ) = pin yv := by
      unfold pin; congr 1; ext; simp [h2]
    rw [hxo, hyi, hR] at hxy
    exact hy (hxy ▸ hSτ xv hx)
  · have hyo : (⟨yv, yi⟩ : PV μ) = pout yv := by
      unfold pout; congr 1; ext; simp [h1]
    have hxi : (⟨xv, xi⟩ : PV μ) = pin xv := by
      unfold pin; congr 1; ext; simp [h2]
    have := hsymm _ _ hxy
    rw [hyo, hxi, hR] at this
    obtain ⟨u, hu, hτu⟩ := hsurj xv hx
    rw [← this] at hτu
    exact hy (hτ hτu ▸ hu)

end Sound

section Build

variable (τ : X → X)

/-- Successor on the path expansion. -/
def psucc (a : PV μ) : PV μ :=
  if h : a.2.val + 1 < μ a.1 + 2 then ⟨a.1, ⟨a.2.val + 1, h⟩⟩ else pin (τ a.1)

lemma psucc_of_lt {v : X} {i : Fin (μ v + 2)} (h : i.val + 1 < μ v + 2) :
    psucc (μ := μ) τ ⟨v, i⟩ = ⟨v, ⟨i.val + 1, h⟩⟩ := by
  unfold psucc; rw [dif_pos h]

lemma psucc_of_not_lt {v : X} {i : Fin (μ v + 2)} (h : ¬ i.val + 1 < μ v + 2) :
    psucc (μ := μ) τ ⟨v, i⟩ = pin (τ v) := by
  unfold psucc; rw [dif_neg h]

lemma psucc_injective (hτ : Injective τ) : Injective (psucc (μ := μ) τ) := by
  intro a b h
  obtain ⟨av, ai⟩ := a
  obtain ⟨bv, bi⟩ := b
  have hai := ai.isLt
  have hbi := bi.isLt
  by_cases h1 : ai.val + 1 < μ av + 2 <;> by_cases h2 : bi.val + 1 < μ bv + 2
  · rw [psucc_of_lt τ h1, psucc_of_lt τ h2] at h
    have hv := congrArg Sigma.fst h
    have hi := congrArg (fun a : PV μ => a.2.val) h
    simp only at hv hi
    subst hv
    congr 1; ext; omega
  · rw [psucc_of_lt τ h1, psucc_of_not_lt τ h2] at h
    have hi := congrArg (fun a : PV μ => a.2.val) h
    simp [pin] at hi
  · rw [psucc_of_not_lt τ h1, psucc_of_lt τ h2] at h
    have hi := congrArg (fun a : PV μ => a.2.val) h
    simp [pin] at hi
  · rw [psucc_of_not_lt τ h1, psucc_of_not_lt τ h2] at h
    have hv := congrArg Sigma.fst h
    simp only [pin] at hv
    have := hτ hv
    subst this
    congr 1
    ext
    omega

lemma psucc_iter (v : X) (j : ℕ) (hj : j < μ v + 2) :
    (psucc (μ := μ) τ)^[j] (pin v) = ⟨v, ⟨j, hj⟩⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iterate_succ_apply', ih (by omega)]
    unfold psucc
    simp only
    rw [dif_pos (by simpa using hj)]

lemma psucc_jump (v : X) : (psucc (μ := μ) τ)^[μ v + 2] (pin v) = pin (τ v) := by
  rw [show μ v + 2 = (μ v + 1) + 1 by ring, iterate_succ_apply', psucc_iter τ v (μ v + 1) (by omega)]
  unfold psucc
  simp

lemma psucc_reach (v₀ : X) (hreach : ∀ w, ∃ k, τ^[k] v₀ = w) :
    ∀ a : PV μ, ∃ m, (psucc (μ := μ) τ)^[m] (pin v₀) = a := by
  have hin : ∀ k, ∃ m, (psucc (μ := μ) τ)^[m] (pin v₀) = pin (τ^[k] v₀) := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨μ (τ^[k] v₀) + 2 + m, ?_⟩
      rw [iterate_add_apply, hm, psucc_jump, ← iterate_succ_apply' τ k v₀]
  rintro ⟨w, j⟩
  obtain ⟨k, rfl⟩ := hreach w
  obtain ⟨m, hm⟩ := hin k
  exact ⟨j.val + m, by rw [iterate_add_apply, hm, psucc_iter τ _ j.val j.2]⟩

lemma gE_psucc (hA : ∀ v, A v (τ v)) (a : PV μ) : gE A μ a (psucc τ a) := by
  obtain ⟨v, i⟩ := a
  have hi := i.isLt
  by_cases h : i.val + 1 < μ v + 2
  · have e : psucc (μ := μ) τ ⟨v, i⟩ = ⟨v, ⟨i.val + 1, h⟩⟩ := by
      unfold psucc; rw [dif_pos h]
    rw [e]
    exact Or.inl ⟨rfl, Or.inl rfl⟩
  · have e : psucc (μ := μ) τ ⟨v, i⟩ = pin (τ v) := by
      unfold psucc; rw [dif_neg h]
    rw [e]
    exact Or.inr (Or.inl ⟨by simp only; omega, rfl, hA v⟩)

end Build

end PathExp

section Transport

variable {q : ℕ}

/-- A tour as an edge set (as in `IsTour`) is a set `F` with a Hamiltonian cycle. -/
lemma isTour_of_succ (σ : Fin q → Fin q) (hinj : Injective σ) (x₀ : Fin q)
    (hreach : ∀ y, ∃ k, σ^[k] x₀ = y) (h3 : 3 ≤ q) :
    IsTour {e : Edge q | ∃ y, e.1 = s(y, σ y)} := by
  obtain ⟨c, hc, hce⟩ := exists_ham_of_cycle σ hinj x₀ hreach (by simpa using h3)
  exact ⟨x₀, c, hc, fun e => by rw [hce]; rfl⟩

end Transport

section FaceGadget

variable {q : ℕ} {ι : Type*} [Fintype ι]

lemma charVec_nonneg (F : Set (Edge q)) (e : Edge q) : 0 ≤ charVec F e := by
  classical
  unfold charVec; split_ifs <;> norm_num

/-- If the tours using only "gadget" edges project exactly onto `S`, then `TSP(q)` has a face that
is an extension of `conv S`. -/
theorem tsp_face_gadget (Gedge : Sym2 (Fin q) → Prop) (hne : ∃ e : Edge q, ¬ Gedge e.1)
    (π : (Edge q → ℝ) →ₗ[ℝ] (ι → ℝ)) (S : Set (ι → ℝ))
    (hsound : ∀ F : Set (Edge q), IsTour F → (∀ e ∈ F, Gedge e.1) → π (charVec F) ∈ S)
    (hcomp : ∀ s ∈ S, ∃ F, IsTour F ∧ (∀ e ∈ F, Gedge e.1) ∧ π (charVec F) = s) :
    ∃ Fc : Set (Edge q → ℝ), IsFace (tspPolytope q) Fc ∧ IsExtension Fc (convexHull ℝ S) := by
  classical
  let cv : Edge q → ℝ := fun e => if Gedge e.1 then 0 else -1
  let T : Set (Edge q → ℝ) := {x | ∃ F : Set (Edge q), IsTour F ∧ x = charVec F}
  have hcv_le : ∀ F : Set (Edge q), cv ⬝ᵥ charVec F ≤ 0 := fun F => by
    refine Finset.sum_nonpos fun e _ => ?_
    simp only [cv]
    split_ifs
    · simp
    · nlinarith [charVec_nonneg F e]
  have hcv_eq : ∀ F : Set (Edge q), cv ⬝ᵥ charVec F = 0 ↔ ∀ e ∈ F, Gedge e.1 := by
    intro F
    constructor
    · intro h e he
      by_contra hg
      have hterm : ∀ e' ∈ (Finset.univ : Finset (Edge q)), cv e' * charVec F e' ≤ 0 := by
        intro e' _
        simp only [cv]
        split_ifs
        · simp
        · nlinarith [charVec_nonneg F e']
      have := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 h e (Finset.mem_univ _)
      simp [cv, hg, charVec, he] at this
    · intro h
      refine Finset.sum_eq_zero fun e _ => ?_
      simp only [cv, charVec]
      by_cases he : e ∈ F
      · simp [h e he]
      · simp [he]
  have hv : ∀ x ∈ T, cv ⬝ᵥ x ≤ 0 := by
    rintro _ ⟨F, -, rfl⟩
    exact hcv_le F
  have hface := face_convexHull T cv 0 hv
  refine ⟨{x | x ∈ tspPolytope q ∧ cv ⬝ᵥ x = 0}, Or.inr ⟨cv, 0, ?_, ?_, rfl⟩, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hne
    intro h
    have := congrFun h e
    simp [cv, he] at this
  · intro x hx
    have hconv : Convex ℝ {x : Edge q → ℝ | cv ⬝ᵥ x ≤ 0} := by
      have : {x : Edge q → ℝ | cv ⬝ᵥ x ≤ 0} = (fun x => cv ⬝ᵥ x) ⁻¹' Iic 0 := rfl
      rw [this]
      exact (convex_Iic _).linear_preimage (dotProductBilin ℝ ℝ cv)
    exact convexHull_min hv hconv hx
  · unfold tspPolytope
    rw [hface]
    refine isPolytope_of_finite (Set.Finite.subset
      (Set.finite_range (fun F : Set (Edge q) => charVec F)) ?_)
    rintro _ ⟨⟨F, -, rfl⟩, -⟩
    exact mem_range_self F
  · unfold tspPolytope
    rw [hface]
    refine ⟨π, ?_⟩
    rw [LinearMap.image_convexHull]
    congr 1
    ext s
    simp only [mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨⟨F, hF, rfl⟩, hcF⟩, rfl⟩
      exact hsound F hF ((hcv_eq F).1 hcF)
    · intro hs
      obtain ⟨F, hF, hG, rfl⟩ := hcomp s hs
      exact ⟨_, ⟨⟨F, hF, rfl⟩, (hcv_eq F).2 hG⟩, rfl⟩

end FaceGadget

end XCT


open Set Function

namespace XCT

section Gadget

variable (n : ℕ)

/-- Pairs `i < j`. -/
abbrev TPair := {q : Fin n × Fin n // q.1 < q.2}

/-- Variables of the formula: `x_i` and `y_q`. -/
abbrev TVar := Fin n ⊕ TPair n

/-- Clauses: three per pair `q = (i, j)`:
`r = 0 : ¬y ∨ x_i`, `r = 1 : ¬y ∨ x_j`, `r = 2 : y ∨ ¬x_i ∨ ¬x_j`. -/
abbrev TCl := TPair n × Fin 3

variable {n}

/-- Number of slots of a chain. -/
def nslot : TVar n → ℕ
  | Sum.inl _ => 2 * n
  | Sum.inr _ => 3

/-- Length of a chain. -/
def clen (k : TVar n) : ℕ := 3 * nslot k + 3

/-- Last position of a chain. -/
def clast (k : TVar n) : ℕ := 3 * nslot k + 2

lemma clast_lt (k : TVar n) : clast k < clen k := by unfold clast clen; omega

variable (n) in
/-- Nodes of the digraph: junctions, chain nodes, clause nodes. -/
abbrev TNode := TVar n ⊕ ((Σ k : TVar n, Fin (clen k)) ⊕ TCl n)

def J (k : TVar n) : TNode n := Sum.inl k
def nd (k : TVar n) (l : ℕ) (h : l < clen k) : TNode n := Sum.inr (Sum.inl ⟨k, ⟨l, h⟩⟩)
def C (c : TCl n) : TNode n := Sum.inr (Sum.inr c)

lemma nd_eq_nd {k k' : TVar n} {l l' : ℕ} {h : l < clen k} {h' : l' < clen k'} :
    nd k l h = nd k' l' h' ↔ k = k' ∧ l = l' := by
  constructor
  · intro e
    unfold nd at e
    simp only [Sum.inr.injEq, Sum.inl.injEq] at e
    have h1 := congrArg Sigma.fst e
    have h2 := congrArg (fun a : (Σ k : TVar n, Fin (clen k)) => a.2.val) e
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] lemma nd_eq_nd_same {k : TVar n} {l l' : ℕ} {h : l < clen k} {h' : l' < clen k} :
    nd k l h = nd k l' h' ↔ l = l' := by
  rw [nd_eq_nd]; simp

@[simp] lemma J_ne_nd {k k' : TVar n} {l : ℕ} {h : l < clen k'} : J k ≠ nd k' l h := by
  simp [J, nd]
@[simp] lemma nd_ne_J {k k' : TVar n} {l : ℕ} {h : l < clen k'} : nd k' l h ≠ J k := by
  simp [J, nd]
@[simp] lemma C_ne_nd {c : TCl n} {k : TVar n} {l : ℕ} {h : l < clen k} : C c ≠ nd k l h := by
  simp [C, nd]
@[simp] lemma nd_ne_C {c : TCl n} {k : TVar n} {l : ℕ} {h : l < clen k} : nd k l h ≠ C c := by
  simp [C, nd]
@[simp] lemma C_ne_J {c : TCl n} {k : TVar n} : C c ≠ J k := by simp [C, J]
@[simp] lemma J_ne_C {c : TCl n} {k : TVar n} : J k ≠ C c := by simp [C, J]
@[simp] lemma J_inj {k k' : TVar n} : J k = J k' ↔ k = k' := by simp [J]
@[simp] lemma C_inj {c c' : TCl n} : C c = C c' ↔ c = c' := by simp [C]

/-- Every node is a junction, a chain node or a clause node. -/
lemma node_cases (v : TNode n) :
    (∃ k, v = J k) ∨ (∃ k l h, v = nd k l h) ∨ (∃ c, v = C c) := by
  rcases v with k | ⟨k, ⟨l, h⟩⟩ | c
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr (Or.inl ⟨k, l, h, rfl⟩)
  · exact Or.inr (Or.inr ⟨c, rfl⟩)

/-- Occurrences: slot `s` of chain `k` carries a literal of clause `c` with polarity `pol`. -/
def occ : TVar n → ℕ → Option (TCl n × Bool)
  | Sum.inl i, s =>
    if h : s / 2 < n then
      if hi : i = ⟨s / 2, h⟩ then none
      else if hlt : i < ⟨s / 2, h⟩ then
        (if s % 2 = 0 then some ((⟨(i, ⟨s / 2, h⟩), hlt⟩, 0), true)
          else some ((⟨(i, ⟨s / 2, h⟩), hlt⟩, 2), false))
      else
        (if s % 2 = 0 then
          some ((⟨(⟨s / 2, h⟩, i), lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hi)⟩, 1), true)
          else some ((⟨(⟨s / 2, h⟩, i), lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hi)⟩, 2), false))
    else none
  | Sum.inr q, s =>
    if s = 0 then some ((q, 0), false)
    else if s = 1 then some ((q, 1), false)
    else if s = 2 then some ((q, 2), true)
    else none

/-- Source position of a detour from slot `s` (positive: `3s+2 → c → 3s+3`). -/
def src (s : ℕ) (pol : Bool) : ℕ := if pol then 3 * s + 2 else 3 * s + 3
/-- Target position of a detour into slot `s`. -/
def dst (s : ℕ) (pol : Bool) : ℕ := if pol then 3 * s + 3 else 3 * s + 2

lemma occ_lt {k : TVar n} {s : ℕ} {c : TCl n} {pol : Bool} (h : occ k s = some (c, pol)) :
    s < nslot k := by
  rcases k with i | q
  · simp only [occ] at h
    simp only [nslot]
    split_ifs at h with h1 <;> omega
  · simp only [occ] at h
    simp only [nslot]
    split_ifs at h <;> omega

variable (n) in
/-- Cyclic order of the chains. -/
noncomputable def nextV (k : TVar n) : TVar n :=
  (Fintype.equivFin (TVar n)).symm (finRotate _ (Fintype.equivFin (TVar n) k))

lemma nextV_injective : Injective (nextV n) := by
  intro a b h
  unfold nextV at h
  simpa using h

/-- Arcs of the digraph `D`. -/
def arcD : TNode n → TNode n → Prop
  | Sum.inl k, Sum.inr (Sum.inl ⟨k', l⟩) => k' = k ∧ (l.val = 0 ∨ l.val = clast k')
  | Sum.inr (Sum.inl ⟨k, l⟩), Sum.inl k' => k' = nextV n k ∧ (l.val = 0 ∨ l.val = clast k)
  | Sum.inr (Sum.inl ⟨k, l⟩), Sum.inr (Sum.inl ⟨k', l'⟩) =>
      k = k' ∧ (l.val + 1 = l'.val ∨ l'.val + 1 = l.val)
  | Sum.inr (Sum.inl ⟨k, l⟩), Sum.inr (Sum.inr c) =>
      ∃ s pol, occ k s = some (c, pol) ∧ l.val = src s pol
  | Sum.inr (Sum.inr c), Sum.inr (Sum.inl ⟨k, l⟩) =>
      ∃ s pol, occ k s = some (c, pol) ∧ l.val = dst s pol
  | _, _ => False

section ArcLemmas

variable {k : TVar n} {l : ℕ} {h : l < clen k}

lemma arc_from_nd {y : TNode n} (hy : arcD (nd k l h) y) :
    (y = J (nextV n k) ∧ (l = 0 ∨ l = clast k)) ∨
      (∃ l' h', y = nd k l' h' ∧ (l + 1 = l' ∨ l' + 1 = l)) ∨
      (∃ c s pol, y = C c ∧ occ k s = some (c, pol) ∧ l = src s pol) := by
  rcases y with k' | ⟨k', ⟨l', h'⟩⟩ | c
  · simp only [nd, arcD] at hy
    exact Or.inl ⟨by rw [hy.1]; rfl, hy.2⟩
  · simp only [nd, arcD] at hy
    obtain ⟨rfl, hl⟩ := hy
    exact Or.inr (Or.inl ⟨l', h', rfl, hl⟩)
  · simp only [nd, arcD] at hy
    obtain ⟨s, pol, h1, h2⟩ := hy
    exact Or.inr (Or.inr ⟨c, s, pol, rfl, h1, h2⟩)

lemma arc_to_nd {x : TNode n} (hx : arcD x (nd k l h)) :
    (x = J k ∧ (l = 0 ∨ l = clast k)) ∨
      (∃ l' h', x = nd k l' h' ∧ (l' + 1 = l ∨ l + 1 = l')) ∨
      (∃ c s pol, x = C c ∧ occ k s = some (c, pol) ∧ l = dst s pol) := by
  rcases x with k' | ⟨k', ⟨l', h'⟩⟩ | c
  · simp only [nd, arcD] at hx
    obtain ⟨rfl, hl⟩ := hx
    exact Or.inl ⟨rfl, hl⟩
  · simp only [nd, arcD] at hx
    obtain ⟨rfl, hl⟩ := hx
    exact Or.inr (Or.inl ⟨l', h', rfl, hl⟩)
  · simp only [nd, arcD] at hx
    obtain ⟨s, pol, h1, h2⟩ := hx
    exact Or.inr (Or.inr ⟨c, s, pol, rfl, h1, h2⟩)

lemma arc_from_C {c : TCl n} {y : TNode n} (hy : arcD (C c) y) :
    ∃ k s pol, occ k s = some (c, pol) ∧ ∃ h, y = nd k (dst s pol) h := by
  rcases y with k' | ⟨k', ⟨l', h'⟩⟩ | c'
  · simp [C, arcD] at hy
  · simp only [C, arcD] at hy
    obtain ⟨s, pol, h1, h2⟩ := hy
    exact ⟨k', s, pol, h1, h2 ▸ h', by unfold nd; congr⟩
  · simp [C, arcD] at hy

lemma arc_to_C {c : TCl n} {x : TNode n} (hx : arcD x (C c)) :
    ∃ k s pol, occ k s = some (c, pol) ∧ ∃ h, x = nd k (src s pol) h := by
  rcases x with k' | ⟨k', ⟨l', h'⟩⟩ | c'
  · simp [C, arcD] at hx
  · simp only [C, arcD] at hx
    obtain ⟨s, pol, h1, h2⟩ := hx
    exact ⟨k', s, pol, h1, h2 ▸ h', by unfold nd; congr⟩
  · simp [C, arcD] at hx

lemma arc_from_J {y : TNode n} (hy : arcD (J k) y) :
    y = nd k 0 (by unfold clen; omega) ∨ y = nd k (clast k) (clast_lt k) := by
  rcases y with k' | ⟨k', ⟨l', h'⟩⟩ | c'
  · simp [J, arcD] at hy
  · simp only [J, arcD] at hy
    obtain ⟨rfl, hl | hl⟩ := hy
    · left; unfold nd; congr
    · right; unfold nd; congr
  · simp [J, arcD] at hy

lemma arc_to_J {k' : TVar n} {x : TNode n} (hx : arcD x (J k')) :
    ∃ k l h, x = nd k l h ∧ k' = nextV n k ∧ (l = 0 ∨ l = clast k) := by
  rcases x with k | ⟨k, ⟨l, h⟩⟩ | c'
  · simp [J, arcD] at hx
  · simp only [J, arcD] at hx
    exact ⟨k, l, h, rfl, hx⟩
  · simp [J, arcD] at hx

lemma arc_J_nd (hl : l = 0 ∨ l = clast k) : arcD (J k) (nd k l h) := ⟨rfl, hl⟩

lemma arc_nd_J (hl : l = 0 ∨ l = clast k) : arcD (nd k l h) (J (nextV n k)) := ⟨rfl, hl⟩

lemma arc_nd_nd {l' : ℕ} {h' : l' < clen k} (hl : l + 1 = l' ∨ l' + 1 = l) :
    arcD (nd k l h) (nd k l' h') := ⟨rfl, hl⟩

lemma arc_nd_C {c : TCl n} {s : ℕ} {pol : Bool} (ho : occ k s = some (c, pol))
    (hl : l = src s pol) : arcD (nd k l h) (C c) := ⟨s, pol, ho, hl⟩

lemma arc_C_nd {c : TCl n} {s : ℕ} {pol : Bool} (ho : occ k s = some (c, pol))
    (hl : l = dst s pol) : arcD (C c) (nd k l h) := ⟨s, pol, ho, hl⟩

end ArcLemmas

end Gadget

end XCT


open Set Function

namespace XCT

section Detour

variable {α : Type*} [Finite α]

/-- The local argument showing that a detour through a clause node returns to the next position of
the same chain. -/
lemma detour_core (τ : α → α) (hinj : Injective τ) (hno2 : ∀ v, τ (τ v) ≠ v)
    {p0 p1 p2 p3 p4 c : α} (h13 : p1 ≠ p3) (hc1 : c ≠ p1) (hc3 : c ≠ p3)
    (hin3 : ∀ x, τ x = p3 → x = p2 ∨ x = p4 ∨ x = c)
    (hout3 : τ p3 = p2 ∨ τ p3 = p4)
    (hin1 : ∀ x, τ x = p1 → x = p0 ∨ x = p2)
    (hout1 : τ p1 = p0 ∨ τ p1 = p2)
    (hc : τ p2 = c) : τ c = p3 := by
  have hsurj := Finite.surjective_of_injective hinj
  by_contra hne
  obtain ⟨x, hx⟩ := hsurj p3
  have hx4 : x = p4 := by
    rcases hin3 x hx with rfl | rfl | rfl
    · exact absurd (hc.symm.trans hx) hc3
    · rfl
    · exact absurd hx hne
  subst hx4
  have h32 : τ p3 = p2 := by
    rcases hout3 with h | h
    · exact h
    · exact absurd (by rw [h, hx]) (hno2 p3)
  obtain ⟨y, hy⟩ := hsurj p1
  have hy0 : y = p0 := by
    rcases hin1 y hy with rfl | rfl
    · rfl
    · exact absurd (hc.symm.trans hy) hc1
  subst hy0
  rcases hout1 with h | h
  · exact hno2 y (by rw [hy, h])
  · exact h13 (hinj (h.trans h32.symm))

end Detour

section Sound

variable {n : ℕ} (τ : TNode n → TNode n) (hinj : Injective τ) (harc : ∀ v, arcD v (τ v))
  (hno2 : ∀ v, τ (τ v) ≠ v)

include hinj harc hno2

/-- A positive detour `3s+2 → c` returns to `3s+3`. -/
lemma detour_pos {k : TVar n} {s : ℕ} {c : TCl n} (ho : occ k s = some (c, true))
    (h2 : 3 * s + 2 < clen k) (h3 : 3 * s + 3 < clen k)
    (hc : τ (nd k (3 * s + 2) h2) = C c) : τ (C c) = nd k (3 * s + 3) h3 := by
  have hs := occ_lt ho
  have hlen : clen k = 3 * nslot k + 3 := rfl
  have hlast : clast k = 3 * nslot k + 2 := rfl
  refine detour_core τ hinj hno2 (p0 := nd k (3 * s) (by omega)) (p1 := nd k (3 * s + 1) (by omega))
    (p4 := nd k (3 * s + 4) (by omega)) ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hc
  · rw [Ne, nd_eq_nd_same]; omega
  · intro x hx
    have := hx ▸ harc x
    rcases arc_to_nd this with ⟨rfl, hl⟩ | ⟨l', h', rfl, hl⟩ | ⟨c', s', pol, rfl, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · left; rw [nd_eq_nd_same]; omega
      · right; left; rw [nd_eq_nd_same]; omega
    · right; right
      cases pol <;> simp only [dst, if_true, if_false, Bool.false_eq_true] at hl
      · omega
      · have : s' = s := by omega
        subst this
        rw [ho] at ho'
        simp only [Option.some.injEq, Prod.mk.injEq] at ho'
        rw [ho'.1]
  · rcases arc_from_nd (harc (nd k (3 * s + 3) h3)) with ⟨-, hl⟩ | ⟨l', h', he, hl⟩ |
      ⟨c', s', pol, -, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · right; rw [he, nd_eq_nd_same]; omega
      · left; rw [he, nd_eq_nd_same]; omega
    · exfalso
      cases pol <;> simp only [src, if_true, if_false, Bool.false_eq_true] at hl
      · have : s' = s := by omega
        subst this
        rw [ho] at ho'
        simp at ho'
      · omega
  · intro x hx
    have := hx ▸ harc x
    rcases arc_to_nd this with ⟨rfl, hl⟩ | ⟨l', h', rfl, hl⟩ | ⟨c', s', pol, rfl, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · left; rw [nd_eq_nd_same]; omega
      · right; rw [nd_eq_nd_same]; omega
    · exfalso; cases pol <;> simp only [dst, if_true, if_false, Bool.false_eq_true] at hl <;> omega
  · rcases arc_from_nd (harc (nd k (3 * s + 1) (by omega))) with ⟨-, hl⟩ | ⟨l', h', he, hl⟩ |
      ⟨c', s', pol, -, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · right; rw [he, nd_eq_nd_same]; omega
      · left; rw [he, nd_eq_nd_same]; omega
    · exfalso; cases pol <;> simp only [src, if_true, if_false, Bool.false_eq_true] at hl <;> omega

/-- A negative detour `3s+3 → c` returns to `3s+2`. -/
lemma detour_neg {k : TVar n} {s : ℕ} {c : TCl n} (ho : occ k s = some (c, false))
    (h2 : 3 * s + 2 < clen k) (h3 : 3 * s + 3 < clen k)
    (hc : τ (nd k (3 * s + 3) h3) = C c) : τ (C c) = nd k (3 * s + 2) h2 := by
  have hs := occ_lt ho
  have hlen : clen k = 3 * nslot k + 3 := rfl
  have hlast : clast k = 3 * nslot k + 2 := rfl
  refine detour_core τ hinj hno2 (p0 := nd k (3 * s + 5) (by omega))
    (p1 := nd k (3 * s + 4) (by omega)) (p4 := nd k (3 * s + 1) (by omega)) ?_ (by simp) (by simp)
    ?_ ?_ ?_ ?_ hc
  · rw [Ne, nd_eq_nd_same]; omega
  · intro x hx
    have := hx ▸ harc x
    rcases arc_to_nd this with ⟨rfl, hl⟩ | ⟨l', h', rfl, hl⟩ | ⟨c', s', pol, rfl, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · right; left; rw [nd_eq_nd_same]; omega
      · left; rw [nd_eq_nd_same]; omega
    · right; right
      cases pol <;> simp only [dst, if_true, if_false, Bool.false_eq_true] at hl
      · have : s' = s := by omega
        subst this
        rw [ho] at ho'
        simp only [Option.some.injEq, Prod.mk.injEq] at ho'
        rw [ho'.1]
      · omega
  · rcases arc_from_nd (harc (nd k (3 * s + 2) h2)) with ⟨-, hl⟩ | ⟨l', h', he, hl⟩ |
      ⟨c', s', pol, -, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · left; rw [he, nd_eq_nd_same]; omega
      · right; rw [he, nd_eq_nd_same]; omega
    · exfalso
      cases pol <;> simp only [src, if_true, if_false, Bool.false_eq_true] at hl
      · omega
      · have : s' = s := by omega
        subst this
        rw [ho] at ho'
        simp at ho'
  · intro x hx
    have := hx ▸ harc x
    rcases arc_to_nd this with ⟨rfl, hl⟩ | ⟨l', h', rfl, hl⟩ | ⟨c', s', pol, rfl, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · right; rw [nd_eq_nd_same]; omega
      · left; rw [nd_eq_nd_same]; omega
    · exfalso; cases pol <;> simp only [dst, if_true, if_false, Bool.false_eq_true] at hl <;> omega
  · rcases arc_from_nd (harc (nd k (3 * s + 4) (by omega))) with ⟨-, hl⟩ | ⟨l', h', he, hl⟩ |
      ⟨c', s', pol, -, ho', hl⟩
    · omega
    · rcases hl with hl | hl
      · left; rw [he, nd_eq_nd_same]; omega
      · right; rw [he, nd_eq_nd_same]; omega
    · exfalso; cases pol <;> simp only [src, if_true, if_false, Bool.false_eq_true] at hl <;> omega

/-- The successor of the source of a detour through `c` is followed by its partner. -/
lemma detour_any {c : TCl n} {x : TNode n} (hx : τ x = C c) :
    ∃ k s pol, occ k s = some (c, pol) ∧ ∃ h h', x = nd k (src s pol) h ∧
      τ (C c) = nd k (dst s pol) h' := by
  obtain ⟨k, s, pol, ho, h, rfl⟩ := arc_to_C (hx ▸ harc x)
  have hs := occ_lt ho
  have hlen : clen k = 3 * nslot k + 3 := rfl
  refine ⟨k, s, pol, ho, h, by cases pol <;> simp [dst] <;> omega, rfl, ?_⟩
  cases pol
  · simp only [src] at h hx ⊢
    simp only [dst]
    exact detour_neg τ hinj harc hno2 ho (by omega) h hx
  · simp only [src] at h hx ⊢
    simp only [dst]
    exact detour_pos τ hinj harc hno2 ho h (by omega) hx

end Sound

end XCT


open Set Function

namespace XCT

section Traverse

variable {n : ℕ} (τ : TNode n → TNode n) (hinj : Injective τ) (harc : ∀ v, arcD v (τ v))
  (hno2 : ∀ v, τ (τ v) ≠ v)
  (hconn : ∀ S : Set (TNode n), S.Nonempty → (∀ v, τ v ∈ S → v ∈ S) → S = univ)

lemma clen_eq (k : TVar n) : clen k = clast k + 1 := by unfold clen clast; omega

lemma src_lt {k : TVar n} {s : ℕ} {c : TCl n} {pol : Bool} (ho : occ k s = some (c, pol)) :
    2 ≤ src s pol ∧ src s pol + 2 ≤ clast k := by
  have := occ_lt ho
  unfold src clast
  cases pol <;> simp <;> omega

lemma dst_lt {k : TVar n} {s : ℕ} {c : TCl n} {pol : Bool} (ho : occ k s = some (c, pol)) :
    2 ≤ dst s pol ∧ dst s pol + 2 ≤ clast k := by
  have := occ_lt ho
  unfold dst clast
  cases pol <;> simp <;> omega

include hinj harc hno2 hconn

/-- Forward skip is impossible. -/
lemma no_skip_fwd (k : TVar n) (h0 : 0 < clen k)
    (hJ : τ (J k) = nd k 0 h0) (hs : τ (nd k 0 h0) = J (nextV n k)) : False := by
  classical
  let U : Set (TNode n) := {v | (∃ l h, 1 ≤ l ∧ v = nd k l h) ∨
    (∃ c, v = C c ∧ ∃ l h, 1 ≤ l ∧ τ (C c) = nd k l h)}
  have h1 : 1 < clen k := by unfold clen; omega
  have hU := hconn U ⟨nd k 1 h1, Or.inl ⟨1, h1, le_rfl, rfl⟩⟩ ?_
  · have : J k ∈ U := hU ▸ mem_univ _
    rcases this with ⟨l, h, -, he⟩ | ⟨c, he, -⟩
    · exact J_ne_nd he
    · exact J_ne_C he
  intro v hv
  rcases hv with ⟨l, h, hl1, he⟩ | ⟨c, he, l, h, hl1, hc⟩
  · rcases arc_to_nd (he ▸ harc v) with ⟨rfl, -⟩ | ⟨l', h', rfl, hl⟩ | ⟨c, s, pol, rfl, -, -⟩
    · rw [hJ, nd_eq_nd_same] at he; omega
    · by_cases hl0 : l' = 0
      · subst hl0
        rw [hs] at he
        exact absurd he J_ne_nd
      · exact Or.inl ⟨l', h', by omega, rfl⟩
    · exact Or.inr ⟨c, rfl, l, h, hl1, he⟩
  · obtain ⟨k', s, pol, ho, hsrc, hdst, rfl, hτc⟩ := detour_any τ hinj harc hno2 he
    rw [hτc, nd_eq_nd] at hc
    obtain ⟨rfl, -⟩ := hc
    exact Or.inl ⟨src s pol, hsrc, by have := (src_lt ho).1; omega, rfl⟩

/-- Backward skip is impossible. -/
lemma no_skip_bwd (k : TVar n)
    (hJ : τ (J k) = nd k (clast k) (clast_lt k))
    (hs : τ (nd k (clast k) (clast_lt k)) = J (nextV n k)) : False := by
  classical
  let U : Set (TNode n) := {v | (∃ l h, l < clast k ∧ v = nd k l h) ∨
    (∃ c, v = C c ∧ ∃ l h, l < clast k ∧ τ (C c) = nd k l h)}
  have h0 : 0 < clen k := by unfold clen; omega
  have hU := hconn U ⟨nd k 0 h0, Or.inl ⟨0, h0, by unfold clast; omega, rfl⟩⟩ ?_
  · have : J k ∈ U := hU ▸ mem_univ _
    rcases this with ⟨l, h, -, he⟩ | ⟨c, he, -⟩
    · exact J_ne_nd he
    · exact J_ne_C he
  intro v hv
  rcases hv with ⟨l, h, hl1, he⟩ | ⟨c, he, l, h, hl1, hc⟩
  · rcases arc_to_nd (he ▸ harc v) with ⟨rfl, -⟩ | ⟨l', h', rfl, hl⟩ | ⟨c, s, pol, rfl, -, -⟩
    · rw [hJ, nd_eq_nd_same] at he; omega
    · by_cases hl0 : l' = clast k
      · subst hl0
        rw [hs] at he
        exact absurd he J_ne_nd
      · exact Or.inl ⟨l', h', by rw [clen_eq] at h'; omega, rfl⟩
    · exact Or.inr ⟨c, rfl, l, h, hl1, he⟩
  · obtain ⟨k', s, pol, ho, hsrc, hdst, rfl, hτc⟩ := detour_any τ hinj harc hno2 he
    rw [hτc, nd_eq_nd] at hc
    obtain ⟨rfl, -⟩ := hc
    exact Or.inl ⟨src s pol, hsrc, by have := (src_lt ho).2; omega, rfl⟩

/-- Forward advance at position `l`. -/
def AdvF (k : TVar n) (l : ℕ) (h : l < clen k) (h' : l + 1 < clen k) : Prop :=
  τ (nd k l h) = nd k (l + 1) h' ∨ ∃ c, τ (nd k l h) = C c ∧ τ (C c) = nd k (l + 1) h'

/-- Backward advance at position `l`. -/
def AdvB (k : TVar n) (l : ℕ) (h : l < clen k) (h' : l - 1 < clen k) : Prop :=
  τ (nd k l h) = nd k (l - 1) h' ∨ ∃ c, τ (nd k l h) = C c ∧ τ (C c) = nd k (l - 1) h'

/-- Forward traversal of a chain entered at its start. -/
theorem fwd_traverse (k : TVar n) (h0 : 0 < clen k) (hJ : τ (J k) = nd k 0 h0) :
    ∀ l (hl : l < clast k), AdvF τ k l (by rw [clen_eq]; omega) (by rw [clen_eq]; omega) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro hl
  have hlen := clen_eq k
  -- predecessor information for `nd (l-1)`
  have hpred : 1 ≤ l → ∀ z, τ z = nd k (l - 1) (by omega) →
      z ≠ nd k l (by omega) ∧ ∀ c, z = C c → τ (nd k l (by omega)) ≠ C c := by
    intro hl1 z hz
    by_cases hl2 : l = 1
    · subst hl2
      have : z = J k := hinj (hz.trans (by rw [hJ]))
      subst this
      exact ⟨J_ne_nd, fun c h => absurd h J_ne_C⟩
    · rcases ih (l - 2) (by omega) (by omega) with h | ⟨c', hc1, hc2⟩
      · have e : l - 2 + 1 = l - 1 := by omega
        have : z = nd k (l - 2) (by omega) := hinj (hz.trans (by rw [h]; simp only [nd_eq_nd_same]; omega))
        subst this
        exact ⟨by rw [Ne, nd_eq_nd_same]; omega, fun c h => absurd h nd_ne_C⟩
      · have : z = C c' := hinj (hz.trans (by rw [hc2]; simp only [nd_eq_nd_same]; omega))
        subst this
        refine ⟨C_ne_nd, fun c h hc => ?_⟩
        rw [C_inj] at h
        subst h
        have := hinj (hc.trans hc1.symm)
        rw [nd_eq_nd_same] at this
        omega
  rcases arc_from_nd (harc (nd k l (by omega))) with ⟨he, hl0 | hl0⟩ | ⟨l', h', he, hl'⟩ |
      ⟨c, s, pol, he, ho, hls⟩
  · subst hl0
    exact (no_skip_fwd τ hinj harc hno2 hconn k h0 hJ he).elim
  · omega
  · rcases hl' with hl' | hl'
    · left; rw [he, nd_eq_nd_same]; omega
    · exfalso
      have hz := (hpred (by omega) (nd k l (by omega)) (by rw [he]; simp only [nd_eq_nd_same]; omega)).1
      exact hz rfl
  · cases pol
    · -- negative detour: returns to `l - 1`, impossible
      exfalso
      simp only [src, if_false, Bool.false_eq_true] at hls
      subst hls
      have hret := detour_neg τ hinj harc hno2 ho (by omega) (by omega) he
      exact (hpred (by omega) (C c) (by rw [hret]; simp only [nd_eq_nd_same]; omega)).2 c rfl he
    · simp only [src, if_true] at hls
      subst hls
      right
      exact ⟨c, he, detour_pos τ hinj harc hno2 ho (by omega) (by omega) he⟩

/-- Backward traversal of a chain entered at its end. -/
theorem bwd_traverse (k : TVar n) (hJ : τ (J k) = nd k (clast k) (clast_lt k)) :
    ∀ l (hl1 : 1 ≤ l) (hl : l ≤ clast k), AdvB τ k l (by rw [clen_eq]; omega) (by rw [clen_eq]; omega) := by
  have hlen := clen_eq k
  suffices H : ∀ m l (hl1 : 1 ≤ l) (hl : l ≤ clast k), clast k - l = m →
      AdvB τ k l (by omega) (by omega) from fun l hl1 hl => H _ l hl1 hl rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro l hl1 hl hm
  have hpred : ∀ (_ : l + 1 ≤ clast k) z, τ z = nd k (l + 1) (by omega) →
      z ≠ nd k l (by omega) ∧ ∀ c, z = C c → τ (nd k l (by omega)) ≠ C c := by
    intro hl2 z hz
    by_cases hl3 : l + 1 = clast k
    · have : z = J k := hinj (hz.trans (by rw [hJ]; simp only [nd_eq_nd_same]; omega))
      subst this
      exact ⟨J_ne_nd, fun c h => absurd h J_ne_C⟩
    · rcases ih (clast k - (l + 2)) (by omega) (l + 2) (by omega) (by omega) rfl with h | ⟨c', hc1, hc2⟩
      · have : z = nd k (l + 2) (by omega) :=
          hinj (hz.trans (by rw [h]; simp only [nd_eq_nd_same]; omega))
        subst this
        exact ⟨by rw [Ne, nd_eq_nd_same]; omega, fun c h => absurd h nd_ne_C⟩
      · have : z = C c' := hinj (hz.trans (by rw [hc2]; simp only [nd_eq_nd_same]; omega))
        subst this
        refine ⟨C_ne_nd, fun c h hc => ?_⟩
        rw [C_inj] at h
        subst h
        have := hinj (hc.trans hc1.symm)
        rw [nd_eq_nd_same] at this
        omega
  rcases arc_from_nd (harc (nd k l (by omega))) with ⟨he, hl0 | hl0⟩ | ⟨l', h', he, hl'⟩ |
      ⟨c, s, pol, he, ho, hls⟩
  · omega
  · subst hl0
    exact (no_skip_bwd τ hinj harc hno2 hconn k hJ he).elim
  · rcases hl' with hl' | hl'
    · exfalso
      have hz := (hpred (by rw [clen_eq] at h'; omega) (nd k l (by omega))
        (by rw [he]; simp only [nd_eq_nd_same]; omega)).1
      exact hz rfl
    · left; rw [he, nd_eq_nd_same]; omega
  · have := src_lt ho
    cases pol
    · simp only [src, if_false, Bool.false_eq_true] at hls this
      subst hls
      right
      refine ⟨c, he, ?_⟩
      have := detour_neg τ hinj harc hno2 ho (by omega) (by omega) he
      rw [this, nd_eq_nd_same]
      omega
    · exfalso
      simp only [src, if_true] at hls this
      subst hls
      have hret := detour_pos τ hinj harc hno2 ho (by omega) (by omega) he
      exact (hpred (by omega) (C c) (by rw [hret])).2 c rfl he

end Traverse

end XCT


open Set Function

namespace XCT

section Readout

variable {n : ℕ}

lemma clen_pos (k : TVar n) : 0 < clen k := by unfold clen; omega

lemma arc_from_J' {k : TVar n} {y : TNode n} (hy : arcD (J k) y) :
    y = nd k 0 (clen_pos k) ∨ y = nd k (clast k) (clast_lt k) := by
  rcases y with k' | ⟨k', ⟨l', h'⟩⟩ | c'
  · simp [J, arcD] at hy
  · simp only [J, arcD] at hy
    obtain ⟨rfl, hl | hl⟩ := hy
    · left; unfold nd; congr
    · right; unfold nd; congr
  · simp [J, arcD] at hy

/-- Which chains carry literals of clause `(q, r)`. -/
lemma occ_some {k : TVar n} {s : ℕ} {q : TPair n} {r : Fin 3} {pol : Bool}
    (h : occ k s = some ((q, r), pol)) :
    (k = Sum.inr q ∧ ((r = 0 ∧ pol = false) ∨ (r = 1 ∧ pol = false) ∨ (r = 2 ∧ pol = true))) ∨
    (k = Sum.inl q.1.1 ∧ ((r = 0 ∧ pol = true) ∨ (r = 2 ∧ pol = false))) ∨
    (k = Sum.inl q.1.2 ∧ ((r = 1 ∧ pol = true) ∨ (r = 2 ∧ pol = false))) := by
  rcases k with i | q'
  · simp only [occ] at h
    split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h <;> simp
  · simp only [occ] at h
    split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h <;> simp

/-- If every clause has a true literal, then `y_q = x_i ∧ x_j`. -/
lemma prod_law (val : TVar n → Bool)
    (hsat : ∀ c : TCl n, ∃ k s pol, occ k s = some (c, pol) ∧ val k = pol) (q : TPair n) :
    val (Sum.inr q) = (val (Sum.inl q.1.1) && val (Sum.inl q.1.2)) := by
  have h0 : val (Sum.inr q) = false ∨ val (Sum.inl q.1.1) = true := by
    obtain ⟨k, s, pol, ho, hv⟩ := hsat (q, 0)
    rcases occ_some ho with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;>
      simp only [Fin.isValue, Fin.reduceEq, false_and, or_false, true_and, false_or] at hr <;>
      first | (left; rw [hv, hr]) | (right; rw [hv, hr]) | (exfalso; exact hr)
  have h1 : val (Sum.inr q) = false ∨ val (Sum.inl q.1.2) = true := by
    obtain ⟨k, s, pol, ho, hv⟩ := hsat (q, 1)
    rcases occ_some ho with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;>
      simp only [Fin.isValue, Fin.reduceEq, false_and, or_false, true_and, false_or] at hr <;>
      first | (left; rw [hv, hr]) | (right; rw [hv, hr]) | (exfalso; exact hr)
  have h2 : val (Sum.inr q) = true ∨ val (Sum.inl q.1.1) = false ∨ val (Sum.inl q.1.2) = false := by
    obtain ⟨k, s, pol, ho, hv⟩ := hsat (q, 2)
    rcases occ_some ho with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;>
      simp only [Fin.isValue, Fin.reduceEq, false_and, or_false, true_and, false_or] at hr <;>
      first | (left; rw [hv, hr]) | (right; left; rw [hv, hr]) | (right; right; rw [hv, hr])
  revert h0 h1 h2
  cases val (Sum.inr q) <;> cases val (Sum.inl q.1.1) <;> cases val (Sum.inl q.1.2) <;> simp

variable (τ : TNode n → TNode n) (hinj : Injective τ) (harc : ∀ v, arcD v (τ v))
  (hconn : ∀ S : Set (TNode n), S.Nonempty → (∀ v, τ v ∈ S → v ∈ S) → S = univ)

include hinj hconn in
lemma no_two_cycle (hn : 1 ≤ n) : ∀ v, τ (τ v) ≠ v := by
  intro v hv
  let k₀ : TVar n := Sum.inl ⟨0, hn⟩
  have h1 : 1 < clen k₀ := by unfold clen; omega
  have hS := hconn {v, τ v} ⟨v, by simp⟩ (by
    intro x hx
    rcases hx with hx | hx
    · right; exact hinj (hx.trans hv.symm)
    · left; exact hinj hx)
  have m1 : J k₀ ∈ ({v, τ v} : Set (TNode n)) := hS ▸ mem_univ _
  have m2 : nd k₀ 0 (clen_pos k₀) ∈ ({v, τ v} : Set (TNode n)) := hS ▸ mem_univ _
  have m3 : nd k₀ 1 h1 ∈ ({v, τ v} : Set (TNode n)) := hS ▸ mem_univ _
  simp only [mem_insert_iff, mem_singleton_iff] at m1 m2 m3
  have d12 : J k₀ ≠ nd k₀ 0 (clen_pos k₀) := J_ne_nd
  have d13 : J k₀ ≠ nd k₀ 1 h1 := J_ne_nd
  have d23 : nd k₀ 0 (clen_pos k₀) ≠ nd k₀ 1 h1 := by rw [Ne, nd_eq_nd_same]; omega
  rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2 <;> rcases m3 with m3 | m3 <;>
    first
    | exact d12 (m1.trans m2.symm)
    | exact d13 (m1.trans m3.symm)
    | exact d23 (m2.trans m3.symm)

/-- The truth value read off chain `k`: forward traversal. -/
noncomputable def val (k : TVar n) : Bool :=
  open Classical in decide (τ (J k) = nd k 0 (clen_pos k))

include hinj harc hconn in
/-- Every clause node is entered from a literal that is true under `val`. -/
lemma clause_sat (hn : 1 ≤ n) (c : TCl n) :
    ∃ k s pol, occ k s = some (c, pol) ∧ val τ k = pol := by
  classical
  have hno2 := no_two_cycle τ hinj hconn hn
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj (C c)
  obtain ⟨k, s, pol, ho, hsrc, hdst, rfl, hτc⟩ := detour_any τ hinj harc hno2 hx
  refine ⟨k, s, pol, ho, ?_⟩
  have hb := src_lt ho
  have hd := dst_lt ho
  rcases arc_from_J' (harc (J k)) with hJ | hJ
  · -- forward
    have hv : val τ k = true := by simp [val, hJ]
    rw [hv]
    cases pol
    · exfalso
      simp only [src, dst, if_false, Bool.false_eq_true] at hb hd hsrc hdst hx hτc
      rcases fwd_traverse τ hinj harc hno2 hconn k (clen_pos k) hJ (3 * s + 3) (by omega) with h | ⟨c', h1, h2⟩
      · rw [hx] at h; exact C_ne_nd h
      · rw [hx, C_inj] at h1
        subst h1
        rw [hτc, nd_eq_nd_same] at h2
        omega
    · rfl
  · -- backward
    have hv : val τ k = false := by
      simp only [val, decide_eq_false_iff_not]
      rw [hJ, nd_eq_nd_same]
      unfold clast; omega
    rw [hv]
    cases pol
    · rfl
    · exfalso
      simp only [src, dst, if_true] at hb hd hsrc hdst hx hτc
      rcases bwd_traverse τ hinj harc hno2 hconn k hJ (3 * s + 2) (by omega) (by omega) with h | ⟨c', h1, h2⟩
      · rw [hx] at h; exact C_ne_nd h
      · rw [hx, C_inj] at h1
        subst h1
        rw [hτc, nd_eq_nd_same] at h2
        omega

include hinj harc hconn in
/-- **Soundness of the gadget**: any Hamiltonian successor map encodes some `b ∈ {0,1}^n`
through the first arcs of the chains. -/
theorem gadget_sound (hn : 1 ≤ n) :
    ∃ b : Fin n → Bool,
      (∀ i, τ (J (Sum.inl i)) = nd (Sum.inl i) 0 (clen_pos _) ↔ b i = true) ∧
      (∀ q : TPair n, τ (J (Sum.inr q)) = nd (Sum.inr q) 0 (clen_pos _) ↔
        (b q.1.1 && b q.1.2) = true) := by
  classical
  refine ⟨fun i => val τ (Sum.inl i), fun i => by simp [val], fun q => ?_⟩
  rw [← prod_law (val τ) (clause_sat τ hinj harc hconn hn) q]
  simp [val]

end Readout

end XCT


open Set Function

namespace XCT

section Witness

variable {n : ℕ}

lemma occ_inl_lt {i j : Fin n} (hij : i < j) :
    occ (Sum.inl i) (2 * j.val) = some ((⟨(i, j), hij⟩, 0), true) ∧
      occ (Sum.inl i) (2 * j.val + 1) = some ((⟨(i, j), hij⟩, 2), false) := by
  have hne : i ≠ j := ne_of_lt hij
  constructor
  · simp only [occ]
    have e : 2 * j.val / 2 = j.val := by omega
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2.trans (Fin.ext (by simp [e]))) hne
    · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      exact Subtype.ext (Prod.ext rfl (Fin.ext (by simp [e])))
    · omega
    · exact absurd (Fin.lt_def.2 (by simp [e]; exact hij)) h3
    · omega
    · exact absurd (by omega : 2 * j.val / 2 < n) h1
  · simp only [occ]
    have e : (2 * j.val + 1) / 2 = j.val := by omega
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2.trans (Fin.ext (by simp [e]))) hne
    · omega
    · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      exact Subtype.ext (Prod.ext rfl (Fin.ext (by simp [e])))
    · omega
    · exact absurd (Fin.lt_def.2 (by simp [e]; exact hij)) h3
    · exact absurd (by omega : (2 * j.val + 1) / 2 < n) h1

lemma occ_inl_gt {i j : Fin n} (hij : j < i) :
    occ (Sum.inl i) (2 * j.val) = some ((⟨(j, i), hij⟩, 1), true) ∧
      occ (Sum.inl i) (2 * j.val + 1) = some ((⟨(j, i), hij⟩, 2), false) := by
  have hne : i ≠ j := ne_of_gt hij
  constructor
  · simp only [occ]
    have e : 2 * j.val / 2 = j.val := by omega
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2.trans (Fin.ext (by simp [e]))) hne
    · exfalso; rw [Fin.lt_def] at h3 hij; simp only [e] at h3; omega
    · omega
    · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      exact Subtype.ext (Prod.ext (Fin.ext (by simp [e])) rfl)
    · omega
    · exact absurd (by omega : 2 * j.val / 2 < n) h1
  · simp only [occ]
    have e : (2 * j.val + 1) / 2 = j.val := by omega
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2.trans (Fin.ext (by simp [e]))) hne
    · omega
    · exfalso; rw [Fin.lt_def] at h3 hij; simp only [e] at h3; omega
    · omega
    · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      exact Subtype.ext (Prod.ext (Fin.ext (by simp [e])) rfl)
    · exact absurd (by omega : (2 * j.val + 1) / 2 < n) h1

lemma occ_inr (q : TPair n) :
    occ (Sum.inr q) 0 = some ((q, 0), false) ∧ occ (Sum.inr q) 1 = some ((q, 1), false) ∧
      occ (Sum.inr q) 2 = some ((q, 2), true) := by
  simp [occ]

/-- The assignment attached to `b`. -/
def vb (b : Fin n → Bool) : TVar n → Bool := Sum.elim b (fun q => b q.1.1 && b q.1.2)

/-- A true literal for every clause. -/
def wit (b : Fin n → Bool) : TCl n → TVar n × ℕ × Bool
  | (q, r) =>
    if r = 0 then
      (if b q.1.1 && b q.1.2 then (Sum.inl q.1.1, 2 * q.1.2.val, true) else (Sum.inr q, 0, false))
    else if r = 1 then
      (if b q.1.1 && b q.1.2 then (Sum.inl q.1.2, 2 * q.1.1.val, true) else (Sum.inr q, 1, false))
    else
      (if b q.1.1 && b q.1.2 then (Sum.inr q, 2, true)
        else if b q.1.1 = false then (Sum.inl q.1.1, 2 * q.1.2.val + 1, false)
        else (Sum.inl q.1.2, 2 * q.1.1.val + 1, false))

lemma wit_spec (b : Fin n → Bool) (c : TCl n) :
    occ (wit b c).1 (wit b c).2.1 = some (c, (wit b c).2.2) ∧ vb b (wit b c).1 = (wit b c).2.2 := by
  obtain ⟨q, r⟩ := c
  obtain ⟨⟨i, j⟩, hij⟩ := q
  have hlt := occ_inl_lt hij
  have hgt := occ_inl_gt hij
  have hy := occ_inr (⟨(i, j), hij⟩ : TPair n)
  fin_cases r <;> simp only [wit, vb] <;>
    cases hbi : b i <;> cases hbj : b j <;> simp_all

lemma src_inj {s s' : ℕ} {p p' : Bool} (h : src s p = src s' p') : s = s' ∧ p = p' := by
  cases p <;> cases p' <;> simp only [src, if_true, if_false, Bool.false_eq_true] at h <;>
    constructor <;> first | omega | rfl | (exfalso; omega)

lemma dst_inj {s s' : ℕ} {p p' : Bool} (h : dst s p = dst s' p') : s = s' ∧ p = p' := by
  cases p <;> cases p' <;> simp only [dst, if_true, if_false, Bool.false_eq_true] at h <;>
    constructor <;> first | omega | rfl | (exfalso; omega)

variable (b : Fin n → Bool)

lemma wit_unique_src {c c' : TCl n} (hk : (wit b c).1 = (wit b c').1)
    (hs : src (wit b c).2.1 (wit b c).2.2 = src (wit b c').2.1 (wit b c').2.2) : c = c' := by
  obtain ⟨h1, h2⟩ := src_inj hs
  have e1 := (wit_spec b c).1
  have e2 := (wit_spec b c').1
  rw [hk, h1, h2, e2] at e1
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at e1
  exact e1.symm

lemma wit_unique_dst {c c' : TCl n} (hk : (wit b c).1 = (wit b c').1)
    (hs : dst (wit b c).2.1 (wit b c).2.2 = dst (wit b c').2.1 (wit b c').2.2) : c = c' := by
  obtain ⟨h1, h2⟩ := dst_inj hs
  have e1 := (wit_spec b c).1
  have e2 := (wit_spec b c').1
  rw [hk, h1, h2, e2] at e1
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at e1
  exact e1.symm

open Classical in
/-- The clause whose detour starts at position `l` of chain `k`. -/
noncomputable def detAt (k : TVar n) (l : ℕ) : Option (TCl n) :=
  if h : ∃ c, (wit b c).1 = k ∧ src (wit b c).2.1 (wit b c).2.2 = l then some h.choose else none

open Classical in
/-- The clause whose detour ends at position `l` of chain `k`. -/
noncomputable def detIn (k : TVar n) (l : ℕ) : Option (TCl n) :=
  if h : ∃ c, (wit b c).1 = k ∧ dst (wit b c).2.1 (wit b c).2.2 = l then some h.choose else none

lemma detAt_eq_some {k : TVar n} {l : ℕ} {c : TCl n} :
    detAt b k l = some c ↔ (wit b c).1 = k ∧ src (wit b c).2.1 (wit b c).2.2 = l := by
  classical
  unfold detAt
  constructor
  · intro h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact h1.choose_spec
  · intro h
    have h1 : ∃ c, (wit b c).1 = k ∧ src (wit b c).2.1 (wit b c).2.2 = l := ⟨c, h⟩
    rw [dif_pos h1]
    congr 1
    obtain ⟨e1, e2⟩ := h1.choose_spec
    exact wit_unique_src b (e1.trans h.1.symm) (e2.trans h.2.symm)

lemma detIn_eq_some {k : TVar n} {l : ℕ} {c : TCl n} :
    detIn b k l = some c ↔ (wit b c).1 = k ∧ dst (wit b c).2.1 (wit b c).2.2 = l := by
  classical
  unfold detIn
  constructor
  · intro h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact h1.choose_spec
  · intro h
    have h1 : ∃ c, (wit b c).1 = k ∧ dst (wit b c).2.1 (wit b c).2.2 = l := ⟨c, h⟩
    rw [dif_pos h1]
    congr 1
    obtain ⟨e1, e2⟩ := h1.choose_spec
    exact wit_unique_dst b (e1.trans h.1.symm) (e2.trans h.2.symm)

lemma wit_pol {c : TCl n} : (wit b c).2.2 = vb b (wit b c).1 := (wit_spec b c).2.symm

/-- In a forward chain a detour ends right after it starts. -/
lemma detIn_fwd {k : TVar n} (hv : vb b k = true) (l : ℕ) :
    detIn b k (l + 1) = detAt b k l := by
  classical
  rcases h : detAt b k l with _ | c
  · rcases h' : detIn b k (l + 1) with _ | c'
    · rfl
    · exfalso
      obtain ⟨e1, e2⟩ := (detIn_eq_some b).1 h'
      have hp : (wit b c').2.2 = true := by rw [wit_pol, e1, hv]
      have : detAt b k l = some c' := (detAt_eq_some b).2 ⟨e1, by
        rw [hp] at e2 ⊢; simp only [src, dst, if_true] at e2 ⊢; omega⟩
      rw [h] at this; simp at this
  · obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 h
    have hp : (wit b c).2.2 = true := by rw [wit_pol, e1, hv]
    exact (detIn_eq_some b).2 ⟨e1, by
      rw [hp] at e2 ⊢; simp only [src, dst, if_true] at e2 ⊢; omega⟩

/-- In a backward chain a detour ends right before it starts. -/
lemma detIn_bwd {k : TVar n} (hv : vb b k = false) (l : ℕ) (hl : 1 ≤ l) :
    detIn b k (l - 1) = detAt b k l := by
  classical
  rcases h : detAt b k l with _ | c
  · rcases h' : detIn b k (l - 1) with _ | c'
    · rfl
    · exfalso
      obtain ⟨e1, e2⟩ := (detIn_eq_some b).1 h'
      have hp : (wit b c').2.2 = false := by rw [wit_pol, e1, hv]
      have : detAt b k l = some c' := (detAt_eq_some b).2 ⟨e1, by
        rw [hp] at e2 ⊢; simp only [src, dst, if_false, Bool.false_eq_true] at e2 ⊢; omega⟩
      rw [h] at this; simp at this
  · obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 h
    have hp : (wit b c).2.2 = false := by rw [wit_pol, e1, hv]
    exact (detIn_eq_some b).2 ⟨e1, by
      rw [hp] at e2 ⊢; simp only [src, dst, if_false, Bool.false_eq_true] at e2 ⊢; omega⟩

lemma wit_dst_lt (c : TCl n) : dst (wit b c).2.1 (wit b c).2.2 < clen (wit b c).1 := by
  have := dst_lt (wit_spec b c).1
  rw [clen_eq]; omega

lemma wit_src_lt (c : TCl n) : src (wit b c).2.1 (wit b c).2.2 < clen (wit b c).1 := by
  have := src_lt (wit_spec b c).1
  rw [clen_eq]; omega

/-- Successor of a chain node in the tour attached to `b`. -/
noncomputable def tbN (k : TVar n) (l : ℕ) (hl : l < clen k) : TNode n :=
  if vb b k = true then
    if he : l = clast k then J (nextV n k) else
      match detAt b k l with
      | some c => C c
      | none => nd k (l + 1) (by have := clen_eq k; omega)
  else
    if he : l = 0 then J (nextV n k) else
      match detAt b k l with
      | some c => C c
      | none => nd k (l - 1) (by omega)

/-- The tour attached to `b`, as a successor map on the nodes of `D`. -/
noncomputable def tb : TNode n → TNode n
  | Sum.inl k => if vb b k = true then nd k 0 (clen_pos k) else nd k (clast k) (clast_lt k)
  | Sum.inr (Sum.inl ⟨k, l⟩) => tbN b k l.val l.isLt
  | Sum.inr (Sum.inr c) => nd (wit b c).1 (dst (wit b c).2.1 (wit b c).2.2) (wit_dst_lt b c)

variable (n) in
noncomputable def prevV (k : TVar n) : TVar n :=
  (Fintype.equivFin (TVar n)).symm ((finRotate _).symm (Fintype.equivFin (TVar n) k))

lemma prevV_nextV (k : TVar n) : prevV n (nextV n k) = k := by
  simp only [prevV, nextV, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Predecessor of a chain node. -/
noncomputable def rbN (k : TVar n) (l : ℕ) (hl : l < clen k) : TNode n :=
  if vb b k = true then
    if he : l = 0 then J k else
      match detIn b k l with
      | some c => C c
      | none => nd k (l - 1) (by omega)
  else
    if he : l = clast k then J k else
      match detIn b k l with
      | some c => C c
      | none => nd k (l + 1) (by have := clen_eq k; omega)

/-- The inverse of `tb`. -/
noncomputable def rb : TNode n → TNode n
  | Sum.inl k' =>
    if vb b (prevV n k') = true then nd (prevV n k') (clast _) (clast_lt _)
    else nd (prevV n k') 0 (clen_pos _)
  | Sum.inr (Sum.inl ⟨k, l⟩) => rbN b k l.val l.isLt
  | Sum.inr (Sum.inr c) => nd (wit b c).1 (src (wit b c).2.1 (wit b c).2.2) (wit_src_lt b c)

lemma tb_J (k : TVar n) : tb b (J k) = if vb b k = true then nd k 0 (clen_pos k)
    else nd k (clast k) (clast_lt k) := rfl

lemma tb_nd (k : TVar n) (l : ℕ) (h : l < clen k) : tb b (nd k l h) = tbN b k l h := rfl

lemma tb_C (c : TCl n) : tb b (C c) = nd (wit b c).1 (dst (wit b c).2.1 (wit b c).2.2)
    (wit_dst_lt b c) := rfl

lemma rb_J (k' : TVar n) : rb b (J k') = if vb b (prevV n k') = true then
    nd (prevV n k') (clast _) (clast_lt _) else nd (prevV n k') 0 (clen_pos _) := rfl

lemma rb_nd (k : TVar n) (l : ℕ) (h : l < clen k) : rb b (nd k l h) = rbN b k l h := rfl

lemma rb_C (c : TCl n) : rb b (C c) = nd (wit b c).1 (src (wit b c).2.1 (wit b c).2.2)
    (wit_src_lt b c) := rfl

lemma rb_tb (v : TNode n) : rb b (tb b v) = v := by
  classical
  rcases node_cases v with ⟨k, rfl⟩ | ⟨k, l, h, rfl⟩ | ⟨c, rfl⟩
  · rw [tb_J]
    by_cases hv : vb b k = true
    · rw [if_pos hv, rb_nd]; unfold rbN; rw [if_pos hv, dif_pos rfl]
    · rw [if_neg hv, rb_nd]; unfold rbN; rw [if_neg hv, dif_pos rfl]
  · have hlen := clen_eq k
    rw [tb_nd]
    unfold tbN
    by_cases hv : vb b k = true
    · rw [if_pos hv]
      by_cases he : l = clast k
      · rw [dif_pos he, rb_J, prevV_nextV, if_pos hv]; subst he; rfl
      · rw [dif_neg he]
        rcases hd : detAt b k l with _ | c
        · simp only
          rw [rb_nd]; unfold rbN
          rw [if_pos hv, dif_neg (by omega), detIn_fwd b hv, hd]
          simp only [nd_eq_nd_same]; omega
        · simp only
          rw [rb_C]
          obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
          subst e1; subst e2; rfl
    · rw [if_neg hv]
      have hv' : vb b k = false := by simpa using hv
      by_cases he : l = 0
      · rw [dif_pos he, rb_J, prevV_nextV, if_neg hv]; subst he; rfl
      · rw [dif_neg he]
        rcases hd : detAt b k l with _ | c
        · simp only
          rw [rb_nd]; unfold rbN
          rw [if_neg hv, dif_neg (by omega), detIn_bwd b hv' l (by omega), hd]
          simp only [nd_eq_nd_same]; omega
        · simp only
          rw [rb_C]
          obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
          subst e1; subst e2; rfl
  · rw [tb_C, rb_nd]
    unfold rbN
    have hd := dst_lt (wit_spec b c).1
    have hin : detIn b (wit b c).1 (dst (wit b c).2.1 (wit b c).2.2) = some c :=
      (detIn_eq_some b).2 ⟨rfl, rfl⟩
    split_ifs with h1 h2 h3
    · omega
    · rw [hin]
    · omega
    · rw [hin]

lemma tb_injective : Injective (tb b) := Function.LeftInverse.injective (rb_tb b)

lemma tb_arc (v : TNode n) : arcD v (tb b v) := by
  classical
  rcases node_cases v with ⟨k, rfl⟩ | ⟨k, l, h, rfl⟩ | ⟨c, rfl⟩
  · rw [tb_J]
    split_ifs
    · exact arc_J_nd (Or.inl rfl)
    · exact arc_J_nd (Or.inr rfl)
  · rw [tb_nd]
    unfold tbN
    split_ifs with hv he he
    · exact arc_nd_J (Or.inr he)
    · rcases hd : detAt b k l with _ | c
      · exact arc_nd_nd (Or.inl rfl)
      · obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
        subst e1
        exact arc_nd_C (wit_spec b c).1 e2.symm
    · exact arc_nd_J (Or.inl he)
    · rcases hd : detAt b k l with _ | c
      · exact arc_nd_nd (Or.inr (by omega))
      · obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
        subst e1
        exact arc_nd_C (wit_spec b c).1 e2.symm
  · rw [tb_C]
    exact arc_C_nd (wit_spec b c).1 rfl

lemma tb_J_iff (k : TVar n) : tb b (J k) = nd k 0 (clen_pos k) ↔ vb b k = true := by
  rw [tb_J]
  split_ifs with hv
  · exact ⟨fun _ => hv, fun _ => rfl⟩
  · constructor
    · intro h; rw [nd_eq_nd_same] at h; unfold clast at h; omega
    · intro h; exact absurd h hv

end Witness

section Reach

variable {n : ℕ} (b : Fin n → Bool)

/-- Reachability along `tb`. -/
def Rch (x y : TNode n) : Prop := ∃ m, (tb b)^[m] x = y

lemma Rch.refl (x : TNode n) : Rch b x x := ⟨0, rfl⟩

lemma Rch.trans {x y z : TNode n} (h1 : Rch b x y) (h2 : Rch b y z) : Rch b x z := by
  obtain ⟨m1, rfl⟩ := h1
  obtain ⟨m2, rfl⟩ := h2
  exact ⟨m2 + m1, by rw [iterate_add_apply]⟩

lemma Rch.step {x y : TNode n} (h : tb b x = y) : Rch b x y := ⟨1, h⟩

/-- Along a forward chain each node reaches the next one. -/
lemma rch_fwd (k : TVar n) (hv : vb b k = true) (l : ℕ) (hl : l < clast k) :
    Rch b (nd k l (by rw [clen_eq]; omega)) (nd k (l + 1) (by rw [clen_eq]; omega)) := by
  classical
  have hlen := clen_eq k
  rcases hd : detAt b k l with _ | c
  · refine Rch.step b ?_
    rw [tb_nd]; unfold tbN
    rw [if_pos hv, dif_neg (by omega), hd]
  · refine Rch.trans b (y := C c) (Rch.step b ?_) (Rch.step b ?_)
    · rw [tb_nd]; unfold tbN
      rw [if_pos hv, dif_neg (by omega), hd]
    · rw [tb_C]
      obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
      have hp : (wit b c).2.2 = true := by rw [wit_pol, e1, hv]
      subst e1
      rw [nd_eq_nd_same]
      rw [hp] at e2 ⊢
      simp only [src, dst, if_true] at e2 ⊢
      omega

lemma rch_bwd (k : TVar n) (hv : vb b k = false) (l : ℕ) (hl1 : 1 ≤ l) (hl : l ≤ clast k) :
    Rch b (nd k l (by rw [clen_eq]; omega)) (nd k (l - 1) (by rw [clen_eq]; omega)) := by
  classical
  have hlen := clen_eq k
  have hv' : ¬ vb b k = true := by simp [hv]
  rcases hd : detAt b k l with _ | c
  · refine Rch.step b ?_
    rw [tb_nd]; unfold tbN
    rw [if_neg hv', dif_neg (by omega), hd]
  · refine Rch.trans b (y := C c) (Rch.step b ?_) (Rch.step b ?_)
    · rw [tb_nd]; unfold tbN
      rw [if_neg hv', dif_neg (by omega), hd]
    · rw [tb_C]
      obtain ⟨e1, e2⟩ := (detAt_eq_some b).1 hd
      have hp : (wit b c).2.2 = false := by rw [wit_pol, e1, hv]
      subst e1
      rw [nd_eq_nd_same]
      rw [hp] at e2 ⊢
      simp only [src, dst, if_false, Bool.false_eq_true] at e2 ⊢
      omega

/-- From the junction `J k` every node of chain `k` and the next junction are reachable. -/
lemma rch_chain (k : TVar n) :
    (∀ l (h : l < clen k), Rch b (J k) (nd k l h)) ∧ Rch b (J k) (J (nextV n k)) := by
  classical
  have hlen := clen_eq k
  by_cases hv : vb b k = true
  · have h0 : Rch b (J k) (nd k 0 (clen_pos k)) := Rch.step b (by rw [tb_J, if_pos hv])
    have hall : ∀ l (h : l < clen k), Rch b (J k) (nd k l h) := by
      intro l
      induction l with
      | zero => intro h; exact h0
      | succ l ih => intro h; exact Rch.trans b (ih (by omega)) (rch_fwd b k hv l (by omega))
    refine ⟨hall, Rch.trans b (hall (clast k) (clast_lt k)) (Rch.step b ?_)⟩
    rw [tb_nd]; unfold tbN
    rw [if_pos hv, dif_pos rfl]
  · have hv' : vb b k = false := by simpa using hv
    have h0 : Rch b (J k) (nd k (clast k) (clast_lt k)) := Rch.step b (by rw [tb_J, if_neg hv])
    have hall : ∀ m (l : ℕ) (h : l < clen k), clast k - l = m → Rch b (J k) (nd k l h) := by
      intro m
      induction m with
      | zero =>
        intro l h hm
        have : l = clast k := by omega
        subst this; exact h0
      | succ m ih =>
        intro l h hm
        exact Rch.trans b (ih (l + 1) (by omega) (by omega))
          (by have := rch_bwd b k hv' (l + 1) (by omega) (by omega); simpa using this)
    refine ⟨fun l h => hall _ l h rfl, Rch.trans b (hall _ 0 (clen_pos k) rfl) (Rch.step b ?_)⟩
    rw [tb_nd]; unfold tbN
    rw [if_neg hv, dif_pos rfl]

lemma finRotate_reach : ∀ (N : ℕ) (x y : Fin N), ∃ m, (finRotate N)^[m] x = y
  | 0, x, _ => x.elim0
  | 1, x, y => ⟨0, Subsingleton.elim _ _⟩
  | N' + 2, x, y => by
    have hx : finRotate (N' + 2) x ≠ x := by
      rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _
    have hy : finRotate (N' + 2) y ≠ y := by
      rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _
    obtain ⟨i, hi⟩ := (isCycle_finRotate (n := N')).exists_pow_eq hx hy
    exact ⟨i, by rw [← Equiv.Perm.coe_pow]; exact hi⟩

lemma nextV_iter_reach (k₀ k : TVar n) : ∃ m, (nextV n)^[m] k₀ = k := by
  classical
  let e := Fintype.equivFin (TVar n)
  have hiter : ∀ m x, (nextV n)^[m] x = e.symm ((finRotate _)^[m] (e x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [iterate_succ_apply', ih, iterate_succ_apply']
      simp [nextV, e]
  obtain ⟨m, hm⟩ := finRotate_reach _ (e k₀) (e k)
  exact ⟨m, by rw [hiter, hm, Equiv.symm_apply_apply]⟩

/-- Every node is reachable from any junction. -/
lemma tb_reach (k₀ : TVar n) : ∀ v, ∃ m, (tb b)^[m] (J k₀) = v := by
  classical
  have hJ : ∀ k, Rch b (J k₀) (J k) := by
    intro k
    obtain ⟨m, rfl⟩ := nextV_iter_reach k₀ k
    induction m with
    | zero => exact Rch.refl b _
    | succ m ih => rw [iterate_succ_apply']; exact Rch.trans b ih (rch_chain b _).2
  intro v
  rcases node_cases v with ⟨k, rfl⟩ | ⟨k, l, h, rfl⟩ | ⟨c, rfl⟩
  · exact hJ k
  · exact Rch.trans b (hJ k) ((rch_chain b k).1 l h)
  · refine Rch.trans b (hJ (wit b c).1) (Rch.trans b ((rch_chain b _).1 _ (wit_src_lt b c))
      (Rch.step b ?_))
    have hd : detAt b (wit b c).1 (src (wit b c).2.1 (wit b c).2.2) = some c :=
      (detAt_eq_some b).2 ⟨rfl, rfl⟩
    have hs := src_lt (wit_spec b c).1
    rw [tb_nd]; unfold tbN
    split_ifs with h1 h2 h3
    · omega
    · rw [hd]
    · omega
    · rw [hd]

end Reach

end XCT


open Matrix ExtensionComplexity.TSP Set Function

namespace XCT

section Assembly

variable {n : ℕ}

/-- The chain read off for entry `(i, j)` of the correlation matrix. -/
def kij (p : Fin n × Fin n) : TVar n :=
  if h : p.1 < p.2 then Sum.inr ⟨p, h⟩
  else if h' : p.2 < p.1 then Sum.inr ⟨(p.2, p.1), h'⟩ else Sum.inl p.1

lemma vb_kij (b : Fin n → Bool) (p : Fin n × Fin n) : vb b (kij p) = (b p.1 && b p.2) := by
  unfold kij
  split_ifs with h h'
  · rfl
  · simp [vb, Bool.and_comm]
  · have : p.1 = p.2 := le_antisymm (not_lt.1 h') (not_lt.1 h)
    simp only [vb, Sum.elim_inl]; rw [← this, Bool.and_self]

lemma outerBits_eq (b : Fin n → Bool) (p : Fin n × Fin n) :
    outerBits b p = if vb b (kij p) = true then 1 else 0 := by
  rw [vb_kij]; unfold outerBits bitVec
  cases b p.1 <;> cases b p.2 <;> simp

variable (μ : TNode n → ℕ) (hμ : ∀ v, 1 ≤ μ v) {N : ℕ} (e : PV μ ≃ Fin N)

/-- Edges of `K_N` coming from the path expansion of the gadget digraph. -/
def Gedge (s : Sym2 (Fin N)) : Prop := ∃ a b : PV μ, gE arcD μ a b ∧ s = s(e a, e b)

lemma pout_ne_pin (k : TVar n) : (pout (J k) : PV μ) ≠ pin (nd k 0 (clen_pos k)) := by
  intro h
  exact J_ne_nd (congrArg Sigma.fst h)

/-- The read-off edge for entry `(i, j)`. -/
def eg (p : Fin n × Fin n) : Edge N :=
  ⟨s(e (pout (J (kij p))), e (pin (nd (kij p) 0 (clen_pos _)))), by
    rw [Sym2.mk_isDiag_iff]; exact fun h => pout_ne_pin μ _ (e.injective h)⟩

/-- The projection `ℝ^{E_N} → ℝ^{n×n}`. -/
noncomputable def piL : (Edge N → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) := LinearMap.funLeft ℝ ℝ (eg μ e)

lemma psucc_pout (τ : TNode n → TNode n) (v : TNode n) :
    psucc (μ := μ) τ (pout v) = pin (τ v) :=
  psucc_of_not_lt τ (by rw [Fin.val_last]; omega)

lemma psucc_pin_fst (τ : TNode n → TNode n) (v : TNode n) : (psucc (μ := μ) τ (pin v)).1 = v := by
  unfold psucc pin
  rw [dif_pos (by rw [Fin.val_zero]; omega)]

include hμ in
/-- Soundness: a tour inside the gadget projects to some `bbᵀ`. -/
lemma gadget_tour_sound (hn : 1 ≤ n) (F : Set (Edge N)) (hF : IsTour F)
    (hG : ∀ x ∈ F, Gedge μ e x.1) :
    piL μ e (charVec F) ∈ range (fun b : Fin n → Bool => outerBits b) := by
  classical
  obtain ⟨v₀, c, hc, hFc⟩ := hF
  let R : PV μ → PV μ → Prop := fun a b => s(e a, e b) ∈ c.edges
  have hdeg : ∀ a, ∃ w₁ w₂, w₁ ≠ w₂ ∧ ∀ w, R a w ↔ (w = w₁ ∨ w = w₂) := by
    intro a
    obtain ⟨w₁, w₂, hne, hw⟩ := ham_deg2 hc (e a)
    refine ⟨e.symm w₁, e.symm w₂, fun h => hne (e.symm.injective h), fun w => ?_⟩
    simp only [R, hw, Equiv.eq_symm_apply]
  have hsymm : ∀ a b, R a b → R b a := fun a b h => by simpa only [R, Sym2.eq_swap] using h
  have hsub : ∀ a b, R a b → gE arcD μ a b := by
    intro a b h
    have hadj := c.adj_of_mem_edges h
    rw [SimpleGraph.top_adj] at hadj
    have hmem : (⟨s(e a, e b), by rw [Sym2.mk_isDiag_iff]; exact hadj⟩ : Edge N) ∈ F := (hFc _).2 h
    obtain ⟨a', b', hg, heq⟩ := hG _ hmem
    rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [e.injective h1, e.injective h2]; exact hg
    · rw [e.injective h1, e.injective h2]; exact gE_symm hg
  have hconn : ∀ T : Set (PV μ), ∀ u ∈ T, ∀ w ∉ T, ∃ x ∈ T, ∃ y ∉ T, R x y := by
    intro T u hu w hw
    obtain ⟨x, hx, y, hy, hxy⟩ := ham_cross hc (e.symm ⁻¹' T) (u := e u) (w := e w)
      (by simpa using hu) (by simpa using hw)
    exact ⟨e.symm x, hx, e.symm y, hy, by simpa [R] using hxy⟩
  obtain ⟨τ, hτ, harc, hR⟩ := exists_succ_of_tour R hdeg hsymm hsub hμ
  have hconn' : ∀ S : Set (TNode n), S.Nonempty → (∀ v, τ v ∈ S → v ∈ S) → S = univ := by
    intro S hS hpre
    by_contra hne
    have hx : ∃ x, x ∉ S := by
      by_contra h
      exact hne (eq_univ_of_forall fun x => by_contra fun hx => h ⟨x, hx⟩)
    obtain ⟨x, hx⟩ := hx
    have hU := succ_connected R hsub τ hτ hR hsymm hconn Sᶜ ⟨x, hx⟩
      (fun v hv hτv => hv (hpre v hτv))
    obtain ⟨y, hy⟩ := hS
    have : y ∈ Sᶜ := hU ▸ mem_univ y
    exact this hy
  obtain ⟨b, hb1, hb2⟩ := gadget_sound τ hτ harc hconn' hn
  have hb : ∀ k, τ (J k) = nd k 0 (clen_pos k) ↔ vb b k = true := by
    rintro (i | q)
    · exact hb1 i
    · exact hb2 q
  refine ⟨b, ?_⟩
  funext p
  show outerBits b p = charVec F (eg μ e p)
  rw [outerBits_eq]
  have hmem : eg μ e p ∈ F ↔ τ (J (kij p)) = nd (kij p) 0 (clen_pos _) := by
    rw [hFc, ← hR]; rfl
  unfold charVec
  by_cases h : vb b (kij p) = true
  · rw [if_pos h, if_pos (hmem.2 ((hb _).2 h))]
  · rw [if_neg h, if_neg (fun h' => h ((hb _).1 (hmem.1 h')))]

include hμ in
/-- Completeness: every `bbᵀ` is the projection of a tour inside the gadget. -/
lemma gadget_tour_complete (hn : 1 ≤ n) (b : Fin n → Bool) :
    ∃ F : Set (Edge N), IsTour F ∧ (∀ x ∈ F, Gedge μ e x.1) ∧ piL μ e (charVec F) = outerBits b := by
  classical
  let σ : Fin N → Fin N := fun y => e (psucc (μ := μ) (tb b) (e.symm y))
  have hσ : Injective σ := fun y y' h =>
    e.symm.injective (psucc_injective (tb b) (tb_injective b) (e.injective h))
  let k₀ : TVar n := Sum.inl ⟨0, hn⟩
  have hiter : ∀ m a, σ^[m] (e a) = e ((psucc (μ := μ) (tb b))^[m] a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih => intro a; rw [iterate_succ_apply', ih, iterate_succ_apply']; simp [σ]
  have hreach : ∀ y, ∃ m, σ^[m] (e (pin (J k₀))) = y := by
    intro y
    obtain ⟨m, hm⟩ := psucc_reach (μ := μ) (tb b) (J k₀) (tb_reach b k₀) (e.symm y)
    exact ⟨m, by rw [hiter, hm, Equiv.apply_symm_apply]⟩
  have h3 : 3 ≤ N := by
    have h3' : 3 ≤ μ (J k₀) + 2 := by have := hμ (J k₀); omega
    have := Fintype.card_le_of_injective
      (fun i : Fin 3 => e (⟨J k₀, Fin.castLE h3' i⟩ : PV μ)) (by
        intro i j h
        have := congrArg (fun a : PV μ => a.2.val) (e.injective h)
        exact Fin.ext (by simpa using this))
    simpa using this
  refine ⟨_, isTour_of_succ σ hσ _ hreach h3, ?_, ?_⟩
  · rintro x ⟨y, hy⟩
    refine ⟨e.symm y, psucc (μ := μ) (tb b) (e.symm y), gE_psucc (tb b) (tb_arc b) _, ?_⟩
    rw [hy]; simp [σ]
  · funext p
    show charVec _ (eg μ e p) = _
    rw [outerBits_eq]
    have hmem : (eg μ e p ∈ {x : Edge N | ∃ y, x.1 = s(y, σ y)}) ↔
        tb b (J (kij p)) = nd (kij p) 0 (clen_pos _) := by
      constructor
      · rintro ⟨y, hy⟩
        simp only [eg] at hy
        rcases Sym2.eq_iff.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1] at h2
          simp only [σ, Equiv.symm_apply_apply, psucc_pout] at h2
          exact (congrArg Sigma.fst (e.injective h2)).symm
        · rw [← h2] at h1
          simp only [σ, Equiv.symm_apply_apply] at h1
          have := congrArg Sigma.fst (e.injective h1)
          rw [psucc_pin_fst] at this
          exact absurd this J_ne_nd
      · intro h
        refine ⟨e (pout (J (kij p))), ?_⟩
        simp only [eg, σ, Equiv.symm_apply_apply, psucc_pout, h]
    unfold charVec
    by_cases h : vb b (kij p) = true
    · rw [if_pos h, if_pos (hmem.2 ((tb_J_iff b _).2 h))]
    · rw [if_neg h, if_neg (fun h' => h ((tb_J_iff b _).1 (hmem.1 h')))]

lemma gadget_hne (hn : 1 ≤ n) : ∃ x : Edge N, ¬ Gedge μ e x.1 := by
  let k₀ : TVar n := Sum.inl ⟨0, hn⟩
  have hne : (pin (J k₀) : PV μ) ≠ pin (nd k₀ 0 (clen_pos _)) := fun h =>
    J_ne_nd (congrArg Sigma.fst h)
  refine ⟨⟨s(e (pin (J k₀)), e (pin (nd k₀ 0 (clen_pos _)))), by
    rw [Sym2.mk_isDiag_iff]; exact fun h => hne (e.injective h)⟩, ?_⟩
  have key : ∀ u w : TNode n, u ≠ w → ¬ gE arcD μ (pin u) (pin w) := by
    intro u w huw h
    unfold gE pin at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact huw h1
    · simp at h1
    · simp at h1
  rintro ⟨a, b, hab, heq⟩
  rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← e.injective h1, ← e.injective h2] at hab
    exact key _ _ J_ne_nd hab
  · rw [← e.injective h1, ← e.injective h2] at hab
    exact key _ _ nd_ne_J hab

include hμ e in
/-- `TSP(N)` has a face that is an extension of `COR(n)`, for any expansion of the gadget with
`N` vertices. -/
theorem tsp_face_of_gadget (hn : 1 ≤ n) :
    ∃ Fc : Set (Edge N → ℝ), IsFace (tspPolytope N) Fc ∧ IsExtension Fc (corPolytope n) :=
  tsp_face_gadget (Gedge μ e) (gadget_hne μ e hn) (piL μ e)
    (range fun b : Fin n → Bool => outerBits b)
    (fun F hF hG => gadget_tour_sound μ hμ e hn F hF hG)
    (by rintro _ ⟨b, rfl⟩; exact gadget_tour_complete μ hμ e hn b)

end Assembly

section Count

/-- Path lengths: all `1`, except `1 + t` on one junction (padding). -/
def muPad (n t : ℕ) (hn : 1 ≤ n) : TNode n → ℕ :=
  fun v => 1 + if v = J (Sum.inl ⟨0, hn⟩) then t else 0

lemma card_PV_pad (n t : ℕ) (hn : 1 ≤ n) :
    Fintype.card (PV (muPad n t hn)) = 3 * Fintype.card (TNode n) + t := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp only [muPad]
  have : ∀ v : TNode n, 1 + (if v = J (Sum.inl ⟨0, hn⟩) then t else 0) + 2 =
      3 + (if v = J (Sum.inl ⟨0, hn⟩) then t else 0) := fun v => by omega
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma card_TPair_le (n : ℕ) : Fintype.card (TPair n) ≤ n ^ 2 := by
  have := Fintype.card_subtype_le (fun q : Fin n × Fin n => q.1 < q.2)
  simpa [Fintype.card_prod, sq] using this

lemma card_TNode (n : ℕ) :
    Fintype.card (TNode n) = 6 * n ^ 2 + 4 * n + 16 * Fintype.card (TPair n) := by
  simp only [TNode, TVar, TCl, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_prod, Fintype.sum_sum_type]
  simp only [clen, nslot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

lemma isPolytope_tsp (q : ℕ) : IsPolytope (tspPolytope q) := by
  classical
  refine isPolytope_of_finite (Set.Finite.subset (Set.finite_range fun F : Set (Edge q) => charVec F) ?_)
  rintro x ⟨F, -, rfl⟩
  exact ⟨F, rfl⟩

/-- **Lemma 11**. -/
theorem tsp_face_cor :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ, 0 < q ∧ q ≤ c * n ^ 2 ∧
      ∃ F : Set (Edge q → ℝ), IsFace (tspPolytope q) F ∧ IsExtension F (corPolytope n) := by
  refine ⟨78, fun n hn => ?_⟩
  have hc := card_PV_pad n 0 hn
  have hT := card_TNode n
  have hP := card_TPair_le n
  have hnn : n ≤ n ^ 2 := by nlinarith
  refine ⟨Fintype.card (PV (muPad n 0 hn)), ?_, ?_,
    tsp_face_of_gadget (muPad n 0 hn) (fun v => Nat.le_add_right _ _) (Fintype.equivFin _) hn⟩
  · rw [hc, hT]; nlinarith
  · rw [hc, hT]; nlinarith

/-- **Theorem 12**. -/
theorem xc_tsp_lb :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ (C * Real.sqrt n) ≤ (extensionComplexity (tspPolytope n) : ℝ) := by
  refine ⟨Real.logb 2 (3 / 2) / 18, by linarith [logb_pos'], 78, fun n hn => ?_⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = Nat.sqrt (n / 78) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef, Nat.le_sqrt]
    omega
  have hsq1 := Nat.sqrt_le' (n / 78)
  have hsq2 := Nat.lt_succ_sqrt' (n / 78)
  rw [← hpdef] at hsq1 hsq2
  have hp2 : 78 * p ^ 2 ≤ n := by omega
  have hp3 : n < 78 * (p + 1) ^ 2 := by
    have h6 : n < 78 * (n / 78) + 78 := by omega
    have : n / 78 + 1 ≤ (p + 1) ^ 2 := hsq2
    nlinarith
  have hT := card_TNode p
  have hP := card_TPair_le p
  have hf : 3 * Fintype.card (TNode p) ≤ n := by
    have : p ≤ p ^ 2 := by nlinarith
    rw [hT]; nlinarith
  have hc := card_PV_pad p (n - 3 * Fintype.card (TNode p)) hp1
  have e : PV (muPad p (n - 3 * Fintype.card (TNode p)) hp1) ≃ Fin n :=
    Fintype.equivFinOfCardEq (by rw [hc]; omega)
  obtain ⟨Fc, hF, hext⟩ := tsp_face_of_gadget _ (fun v => Nat.le_add_right _ _) e hp1
  have hxc : extensionComplexity (corPolytope p) ≤ extensionComplexity (tspPolytope n) :=
    (xc_extension_mono _ Fc hext.1 hext).trans
      (xc_face_le (exists_EF_of_isPolytope (isPolytope_tsp n)) hF)
  calc (2 : ℝ) ^ (Real.logb 2 (3 / 2) / 18 * Real.sqrt n)
      ≤ (2 : ℝ) ^ (Real.logb 2 (3 / 2) * p) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hC := logb_pos'
        have hsq : Real.sqrt n ≤ 18 * p := by
          rw [Real.sqrt_le_left (by positivity)]
          have : (n : ℝ) < 78 * (p + 1) ^ 2 := by exact_mod_cast hp3
          have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
          nlinarith
        nlinarith
    _ = (3 / 2 : ℝ) ^ p := two_rpow_logb p
    _ ≤ extensionComplexity (corPolytope p) := xc_cor_ge hp1
    _ ≤ _ := by exact_mod_cast hxc

end Count

end XCT

open Matrix ExtensionComplexity.TSP

theorem solution :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ, 0 < q ∧ q ≤ c * n ^ 2 ∧
      ∃ F : Set (Edge q → ℝ), IsFace (tspPolytope q) F ∧ IsExtension F (corPolytope n) :=
  XCT.tsp_face_cor
