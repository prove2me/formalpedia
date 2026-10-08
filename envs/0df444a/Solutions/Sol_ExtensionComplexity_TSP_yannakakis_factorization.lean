-- Prove2me | solution 1 for ExtensionComplexity.TSP.yannakakis_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T09:50:18.333807+00:00
-- url     : https://prove2.me/submissions/b2b48f51-3059-458e-ac91-540ce21b105b

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


open Matrix ExtensionComplexity.TSP Set Filter Topology

namespace XCT

section VFacets

variable {κ : Type*} [Fintype κ]

/-- A face of `conv W` cut out by a valid hyperplane is the hull of the generators on it. -/
lemma face_subset_hull (W : Finset (κ → ℝ)) (c : κ → ℝ) (δ : ℝ)
    (hv : ∀ x ∈ convexHull ℝ (W : Set (κ → ℝ)), c ⬝ᵥ x ≤ δ) :
    {x | x ∈ convexHull ℝ (W : Set (κ → ℝ)) ∧ c ⬝ᵥ x = δ} =
      convexHull ℝ ((W.filter fun w => c ⬝ᵥ w = δ : Finset (κ → ℝ)) : Set (κ → ℝ)) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hcx⟩
    obtain ⟨μ, hμ0, hμ1, hμx⟩ := Finset.mem_convexHull'.1 hx
    have hW : ∀ w ∈ W, c ⬝ᵥ w ≤ δ := fun w hw => hv w (subset_convexHull ℝ _ hw)
    -- every generator with positive weight lies on the hyperplane
    have hsum : ∑ w ∈ W, μ w * (δ - c ⬝ᵥ w) = 0 := by
      have : c ⬝ᵥ x = ∑ w ∈ W, μ w * (c ⬝ᵥ w) := by
        rw [← hμx, dotProduct_sum]
        simp [dotProduct_smul]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ1, one_mul, ← this, hcx,
        sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun w hw =>
      mul_nonneg (hμ0 w hw) (sub_nonneg.2 (hW w hw))).1 hsum
    refine Finset.mem_convexHull'.2 ⟨μ, fun w hw => hμ0 w (Finset.mem_filter.1 hw).1, ?_, ?_⟩
    · rw [← hμ1, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w hw => ?_
      split_ifs with h
      · rfl
      · rcases mul_eq_zero.1 (hz w hw) with h' | h'
        · exact h'.symm
        · exact absurd (by linarith) h
    · rw [← hμx, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w hw => ?_
      split_ifs with h
      · rfl
      · rcases mul_eq_zero.1 (hz w hw) with h' | h'
        · simp [h']
        · exact absurd (by linarith) h
  · intro hx
    have hsub : ((W.filter fun w => c ⬝ᵥ w = δ : Finset (κ → ℝ)) : Set (κ → ℝ)) ⊆
        {x | x ∈ convexHull ℝ (W : Set (κ → ℝ)) ∧ c ⬝ᵥ x = δ} := by
      intro w hw
      rw [Finset.coe_filter] at hw
      exact ⟨subset_convexHull ℝ _ hw.1, hw.2⟩
    have hconv : Convex ℝ {x | x ∈ convexHull ℝ (W : Set (κ → ℝ)) ∧ c ⬝ᵥ x = δ} := by
      intro a ha b hb s t hs ht hst
      refine ⟨convex_convexHull ℝ _ ha.1 hb.1 hs ht hst, ?_⟩
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, ha.2, hb.2, smul_eq_mul,
        smul_eq_mul, ← add_mul, hst, one_mul]
    exact convexHull_min hsub hconv hx

/-- A polytope has finitely many faces. -/
lemma faces_finite (W : Finset (κ → ℝ)) :
    {F : Set (κ → ℝ) | IsFace (convexHull ℝ (W : Set (κ → ℝ))) F}.Finite := by
  classical
  refine ((W.powerset.finite_toSet).image
    (fun s : Finset (κ → ℝ) => convexHull ℝ (s : Set (κ → ℝ)))).subset ?_
  rintro F (rfl | ⟨c, δ, -, hv, rfl⟩)
  · exact ⟨W, Finset.mem_powerset.2 subset_rfl, rfl⟩
  · exact ⟨_, Finset.mem_powerset.2 (Finset.filter_subset _ _),
      (face_subset_hull W c δ hv).symm⟩

/-- Every proper face of a polytope lies in a facet. -/
lemma exists_facet_superset (W : Finset (κ → ℝ)) {F : Set (κ → ℝ)}
    (hF : IsFace (convexHull ℝ (W : Set (κ → ℝ))) F) (hFQ : F ≠ convexHull ℝ (W : Set (κ → ℝ))) :
    ∃ G, IsFacet (convexHull ℝ (W : Set (κ → ℝ))) G ∧ F ⊆ G := by
  classical
  set Q := convexHull ℝ (W : Set (κ → ℝ))
  have hfin : {G | IsFace Q G ∧ G ≠ Q ∧ F ⊆ G}.Finite :=
    (faces_finite W).subset fun G hG => hG.1
  obtain ⟨G, hG⟩ := Finset.exists_maximal (s := hfin.toFinset) ⟨F, by simp [hF, hFQ]⟩
  have hGm := hG.1
  simp only [Finite.mem_toFinset, mem_setOf_eq] at hGm
  refine ⟨G, ⟨hGm.1, hGm.2.1, fun G' hG' hG'Q hGG' => ?_⟩, hGm.2.2⟩
  have hG'm : G' ∈ hfin.toFinset := by
    simp only [Finite.mem_toFinset, mem_setOf_eq]
    exact ⟨hG', hG'Q, hGm.2.2.trans hGG'⟩
  exact le_antisymm (hG.2 hG'm hGG') hGG'

/-- A strictly positive convex combination of all generators lies in no proper face. -/
lemma face_eq_of_pos (W : Finset (κ → ℝ)) (μ : (κ → ℝ) → ℝ) (hμ0 : ∀ w ∈ W, 0 < μ w)
    (hμ1 : ∑ w ∈ W, μ w = 1) (c : κ → ℝ) (δ : ℝ)
    (hv : ∀ x ∈ convexHull ℝ (W : Set (κ → ℝ)), c ⬝ᵥ x ≤ δ)
    (hq : c ⬝ᵥ (∑ w ∈ W, μ w • w) = δ) :
    {x | x ∈ convexHull ℝ (W : Set (κ → ℝ)) ∧ c ⬝ᵥ x = δ} = convexHull ℝ (W : Set (κ → ℝ)) := by
  classical
  have hW : ∀ w ∈ W, c ⬝ᵥ w ≤ δ := fun w hw => hv w (subset_convexHull ℝ _ hw)
  have hall : ∀ w ∈ W, c ⬝ᵥ w = δ := by
    by_contra h
    push Not at h
    obtain ⟨w₀, hw₀, hne⟩ := h
    have hlt : ∑ w ∈ W, μ w * (c ⬝ᵥ w) < ∑ w ∈ W, μ w * δ :=
      Finset.sum_lt_sum (fun w hw => mul_le_mul_of_nonneg_left (hW w hw) (hμ0 w hw).le)
        ⟨w₀, hw₀, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hW w₀ hw₀) hne) (hμ0 w₀ hw₀)⟩
    rw [← Finset.sum_mul, hμ1, one_mul] at hlt
    rw [dotProduct_sum] at hq
    simp only [dotProduct_smul, smul_eq_mul] at hq
    linarith
  rw [face_subset_hull W c δ hv, Finset.filter_true_of_mem hall]

/-- **Relative interior via Farkas**: a point of `conv W` lying on no proper face is a strictly
positive convex combination of all generators. -/
lemma pos_rep_of_no_face (W : Finset (κ → ℝ)) {z : κ → ℝ}
    (hz : z ∈ convexHull ℝ (W : Set (κ → ℝ)))
    (hnf : ∀ (c : κ → ℝ) (δ : ℝ), (∀ x ∈ convexHull ℝ (W : Set (κ → ℝ)), c ⬝ᵥ x ≤ δ) →
      c ⬝ᵥ z = δ → ∀ w ∈ W, c ⬝ᵥ w = δ) :
    ∃ μ : (κ → ℝ) → ℝ, (∀ w ∈ W, 0 < μ w) ∧ ∑ w ∈ W, μ w = 1 ∧ ∑ w ∈ W, μ w • w = z := by
  classical
  -- Step 1: for each generator `w₀`, a representation of `z` giving `w₀` positive weight.
  have step : ∀ w₀ ∈ W, ∃ μ : (κ → ℝ) → ℝ, (∀ w ∈ W, 0 ≤ μ w) ∧ 0 < μ w₀ ∧
      ∑ w ∈ W, μ w = 1 ∧ ∑ w ∈ W, μ w • w = z := by
    intro w₀ hw₀
    -- generators `(w, 1)` for `w ∈ W` and `-(z, 1)`, in `Option κ → ℝ`
    let lift : (κ → ℝ) → Option κ → ℝ := fun v o => o.elim 1 v
    let a : Option W → Option κ → ℝ := fun i => i.elim (-lift z) (fun w => lift w)
    have hdot : ∀ (v : κ → ℝ) (y : Option κ → ℝ),
        lift v ⬝ᵥ y = y none + v ⬝ᵥ (fun k => y (some k)) := by
      intro v y
      simp [lift, dotProduct, Fintype.sum_option]
    by_cases hc : -lift w₀ ∈ cone a
    · obtain ⟨l, hl0, hl⟩ := hc
      have hcoord : ∀ o, ∑ i, l i * a i o = -lift w₀ o := by
        intro o
        have := congrFun hl o
        simpa [Finset.sum_apply] using this
      have hnone := hcoord none
      simp only [Fintype.sum_option, a, lift, Option.elim, Pi.neg_apply, mul_neg, mul_one]
        at hnone
      set L := l none
      set sW := ∑ w : W, l (some w)
      have hsW : 0 ≤ sW := Finset.sum_nonneg fun w _ => hl0 _
      have hL : L = 1 + sW := by linarith
      have hLpos : 0 < L := by linarith
      refine ⟨fun v => (if h : v ∈ W then l (some ⟨v, h⟩) else 0) / L +
        (if v = w₀ then 1 / L else 0), fun w hw => ?_, ?_, ?_, ?_⟩
      · apply add_nonneg
        · simp only [hw, dif_pos]
          exact div_nonneg (hl0 _) hLpos.le
        · split_ifs
          · exact div_nonneg zero_le_one hLpos.le
          · exact le_rfl
      · simp only [if_pos rfl]
        apply add_pos_of_nonneg_of_pos
        · simp only [hw₀, dif_pos]
          exact div_nonneg (hl0 _) hLpos.le
        · exact div_pos one_pos hLpos
      · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' W w₀, if_pos hw₀, ← Finset.sum_div,
          ← Finset.sum_coe_sort W]
        simp only [Finset.coe_mem, dif_pos, Subtype.coe_eta]
        field_simp
        linarith
      · funext k
        have hk := hcoord (some k)
        simp only [Fintype.sum_option, a, lift, Option.elim, Pi.neg_apply, mul_neg] at hk
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul,
          zero_mul, Finset.sum_ite_eq' W w₀, if_pos hw₀]
        rw [← Finset.sum_coe_sort W]
        simp only [Finset.coe_mem, dif_pos, Subtype.coe_eta]
        have : ∑ w : W, l (some w) / L * (w : κ → ℝ) k = (∑ w : W, l (some w) * (w : κ → ℝ) k) / L := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [this]
        field_simp
        linarith
    · obtain ⟨y, hy, hcy⟩ := farkas a hc
      set u : κ → ℝ := fun k => y (some k)
      set s := y none
      have hW : ∀ w ∈ W, 0 ≤ s + w ⬝ᵥ u := fun w hw => by
        have := hy (some ⟨w, hw⟩)
        simpa [a, hdot] using this
      have hzz : s + z ⬝ᵥ u ≤ 0 := by
        have := hy none
        simp only [a, Option.elim, neg_dotProduct, hdot] at this
        linarith
      have hw0 : 0 < s + w₀ ⬝ᵥ u := by
        simp only [neg_dotProduct, hdot] at hcy
        linarith
      -- the valid inequality `(-u) ⬝ x ≤ s` is tight at `z` but not at `w₀`
      have hvalid : ∀ x ∈ convexHull ℝ (W : Set (κ → ℝ)), (-u) ⬝ᵥ x ≤ s := by
        intro x hx
        obtain ⟨μ, hμ0, hμ1, rfl⟩ := Finset.mem_convexHull'.1 hx
        rw [dotProduct_sum]
        calc ∑ w ∈ W, (-u) ⬝ᵥ (μ w • w) ≤ ∑ w ∈ W, μ w * s :=
              Finset.sum_le_sum fun w hw => by
                rw [dotProduct_smul, smul_eq_mul, neg_dotProduct, dotProduct_comm]
                have := hW w hw
                exact mul_le_mul_of_nonneg_left (by linarith) (hμ0 w hw)
          _ = s := by rw [← Finset.sum_mul, hμ1, one_mul]
      have hzt : (-u) ⬝ᵥ z = s := by
        have := hvalid z hz
        rw [neg_dotProduct, dotProduct_comm] at this ⊢
        linarith
      have := hnf (-u) s hvalid hzt w₀ hw₀
      rw [neg_dotProduct, dotProduct_comm] at this
      linarith
  -- Step 2: average the representations.
  choose! μs hμs0 hμspos hμs1 hμsz using step
  have hne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · subst h; simp at hz
    · exact h
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast hne.card_pos
  refine ⟨fun w => (∑ w₀ ∈ W, μs w₀ w) / W.card, fun w hw => ?_, ?_, ?_⟩
  · apply div_pos _ hcard
    exact Finset.sum_pos' (fun w₀ hw₀ => hμs0 w₀ hw₀ w hw) ⟨w, hw, hμspos w hw⟩
  · rw [← Finset.sum_div, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun w₀ hw₀ => hμs1 w₀ hw₀]
    simp [hcard.ne']
  · simp only [div_eq_mul_inv, mul_comm _ (W.card : ℝ)⁻¹, mul_smul, ← Finset.smul_sum,
      Finset.sum_smul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun w₀ hw₀ => hμsz w₀ hw₀]
    simp only [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [inv_mul_cancel₀ hcard.ne', one_smul]

/-- A polytope is cut out of its affine hull by any family of valid inequalities containing a
defining inequality for each facet. -/
lemma mem_hull_of_facets (W : Finset (κ → ℝ)) {I : Type*} (c : I → κ → ℝ) (δ : I → ℝ)
    (hv : ∀ i, ∀ x ∈ convexHull ℝ (W : Set (κ → ℝ)), c i ⬝ᵥ x ≤ δ i)
    (hF : ∀ G, IsFacet (convexHull ℝ (W : Set (κ → ℝ))) G →
      ∃ i, G = {x | x ∈ convexHull ℝ (W : Set (κ → ℝ)) ∧ c i ⬝ᵥ x = δ i})
    {y : κ → ℝ} (ν : (κ → ℝ) → ℝ) (hν1 : ∑ w ∈ W, ν w = 1) (hνy : ∑ w ∈ W, ν w • w = y)
    (hy : ∀ i, c i ⬝ᵥ y ≤ δ i) : y ∈ convexHull ℝ (W : Set (κ → ℝ)) := by
  classical
  set Q := convexHull ℝ (W : Set (κ → ℝ)) with hQdef
  by_contra hyQ
  have hne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · subst h; simp at hν1
    · exact h
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast hne.card_pos
  -- the barycenter `q` of the generators lies in no proper face
  let β : (κ → ℝ) → ℝ := fun _ => (W.card : ℝ)⁻¹
  have hβ0 : ∀ w ∈ W, 0 < β w := fun _ _ => inv_pos.2 hcard
  have hβ1 : ∑ w ∈ W, β w = 1 := by simp [β, Finset.sum_const, hcard.ne']
  set q := ∑ w ∈ W, β w • w with hqdef
  have hq : q ∈ Q := Finset.mem_convexHull'.2 ⟨β, fun w hw => (hβ0 w hw).le, hβ1, rfl⟩
  have hQc : IsClosed Q := Set.Finite.isClosed_convexHull (𝕜 := ℝ) W.finite_toSet
  have hpc : Continuous fun t : ℝ => q + t • (y - q) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- the last point `z` of the segment `[q, y]` inside `Q`
  set S := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ q + t • (y - q) ∈ Q} with hSdef
  have hSc : IsClosed S := isClosed_Icc.inter (hQc.preimage hpc)
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by simpa using hq⟩
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  set t := sSup S with htdef
  have htS : t ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hbdd
  have ht0 : 0 ≤ t := htS.1.1
  have ht1 : t < 1 := by
    refine lt_of_le_of_ne htS.1.2 fun h => hyQ ?_
    have := htS.2
    rw [h] at this
    simpa using this
  have hzQ : q + t • (y - q) ∈ Q := htS.2
  by_cases hface : ∀ (c' : κ → ℝ) (δ' : ℝ), (∀ x ∈ Q, c' ⬝ᵥ x ≤ δ') →
      c' ⬝ᵥ (q + t • (y - q)) = δ' → ∀ w ∈ W, c' ⬝ᵥ w = δ'
  · -- `z` is relatively interior, so the segment continues inside `Q`
    obtain ⟨μ, hμ0, hμ1, hμz⟩ := pos_rep_of_no_face W hzQ hface
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∀ w ∈ W, 0 ≤ μ w + s * (ν w - μ w)) ∧ s < 1 := by
      refine Filter.Eventually.and (nhdsWithin_le_nhds ?_)
        (nhdsWithin_le_nhds (eventually_lt_nhds one_pos))
      refine (Filter.eventually_all_finset W).2 fun w hw => ?_
      have hT : Tendsto (fun s : ℝ => μ w + s * (ν w - μ w)) (𝓝 0) (𝓝 (μ w)) := by
        have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (ν w - μ w)).const_add (μ w)
        simpa using this
      exact (hT.eventually (lt_mem_nhds (hμ0 w hw))).mono fun s hs => hs.le
    obtain ⟨s, ⟨hs0w, hs1⟩, hspos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hspos' : 0 < s := hspos
    have hsum : ∑ w ∈ W, (μ w + s * (ν w - μ w)) = 1 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hμ1, hν1,
        sub_self, mul_zero, add_zero]
    have heq : ∑ w ∈ W, (μ w + s * (ν w - μ w)) • w = q + (t + s * (1 - t)) • (y - q) := by
      simp only [add_smul, mul_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum]
      rw [hμz, hνy]
      module
    have hmem : t + s * (1 - t) ∈ S := by
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      rw [← heq]
      exact Finset.mem_convexHull'.2 ⟨_, hs0w, hsum, rfl⟩
    have := le_csSup hbdd hmem
    nlinarith [mul_pos hspos' (by linarith : (0 : ℝ) < 1 - t)]
  · -- `z` lies on a proper face, hence on a facet, whose inequality `y` violates
    push Not at hface
    obtain ⟨c', δ', hv', hz', w, hw, hw'⟩ := hface
    have hc' : c' ≠ 0 := by
      rintro rfl
      simp only [zero_dotProduct] at hz' hw'
      exact hw' hz'
    have hF0 : IsFace Q {x | x ∈ Q ∧ c' ⬝ᵥ x = δ'} := Or.inr ⟨c', δ', hc', hv', rfl⟩
    have hF0Q : {x | x ∈ Q ∧ c' ⬝ᵥ x = δ'} ≠ Q := by
      intro h
      have hwQ : w ∈ Q := subset_convexHull ℝ _ hw
      rw [← h] at hwQ
      exact hw' hwQ.2
    obtain ⟨G, hG, hFG⟩ := exists_facet_superset W hF0 hF0Q
    obtain ⟨i, rfl⟩ := hF G hG
    have hzi : c i ⬝ᵥ (q + t • (y - q)) = δ i := (hFG ⟨hzQ, hz'⟩).2
    have hqi : c i ⬝ᵥ q < δ i := by
      refine lt_of_le_of_ne (hv i q hq) fun h => hG.2.1 ?_
      exact face_eq_of_pos W β hβ0 hβ1 (c i) (δ i) (hv i) h
    rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at hzi
    have := hy i
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) (by linarith : 0 < δ i - c i ⬝ᵥ q),
      mul_le_mul_of_nonneg_left this ht0]

/-- **(ii) ⇒ (iii), core**: a polytope with `f` facets has an EF of size `f`: keep the affine
hull (through auxiliary convex-combination variables) and one inequality per facet. -/
lemma isEF_of_facets (W : Finset (κ → ℝ)) {fs : Finset (Set (κ → ℝ))}
    (hfs : ∀ F, IsFacet (convexHull ℝ (W : Set (κ → ℝ))) F ↔ F ∈ fs) :
    IsEFOfSize (convexHull ℝ (W : Set (κ → ℝ))) fs.card := by
  classical
  set Q := convexHull ℝ (W : Set (κ → ℝ)) with hQdef
  have hrep : ∀ F : fs, ∃ (c : κ → ℝ) (δ : ℝ), (∀ x ∈ Q, c ⬝ᵥ x ≤ δ) ∧
      (F : Set (κ → ℝ)) = {x | x ∈ Q ∧ c ⬝ᵥ x = δ} := by
    intro F
    have hF := (hfs F).2 F.2
    rcases hF.1 with h | ⟨c, δ, -, hv, h⟩
    · exact absurd h hF.2.1
    · exact ⟨c, δ, hv, h⟩
  choose c δ hcv hcF using hrep
  let Eeq : Matrix (κ ⊕ Unit) κ ℝ :=
    Matrix.of fun r i => Sum.elim (fun j => if j = i then (1 : ℝ) else 0) (fun _ => 0) r
  let Feq : Matrix (κ ⊕ Unit) W ℝ :=
    Matrix.of fun r (v : W) => Sum.elim (fun j => -(v : κ → ℝ) j) (fun _ => (1 : ℝ)) r
  let geq : κ ⊕ Unit → ℝ := Sum.elim 0 (fun _ => 1)
  let Ele : Matrix fs κ ℝ := Matrix.of fun F k => c F k
  have hcard : Fintype.card fs = fs.card := Fintype.card_coe fs
  rw [← hcard]
  refine isEF_of (K := W) Eeq Feq geq Ele 0 δ fun x => ?_
  have key : ∀ y : W → ℝ, (Eeq *ᵥ x + Feq *ᵥ y = geq ↔
      (∑ v, y v = 1 ∧ ∑ v, y v • (v : κ → ℝ) = x)) := by
    intro y
    have hl : ∀ i, (Eeq *ᵥ x + Feq *ᵥ y) (Sum.inl i) = x i - ∑ v : W, y v * (v : κ → ℝ) i := by
      intro i
      simp only [Pi.add_apply, Eeq, Feq, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, neg_mul,
        Finset.sum_neg_distrib]
      rw [sub_eq_add_neg]
      congr 2
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hr : (Eeq *ᵥ x + Feq *ᵥ y) (Sum.inr ()) = ∑ v : W, y v := by
      simp [Eeq, Feq, mulVec, dotProduct]
    have hs : ∀ i, (∑ v : W, y v • (v : κ → ℝ)) i = ∑ v : W, y v * (v : κ → ℝ) i := by
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
  have hle : ∀ y : W → ℝ, (Ele *ᵥ x + (0 : Matrix fs W ℝ) *ᵥ y ≤ δ ↔ ∀ F, c F ⬝ᵥ x ≤ δ F) := by
    intro y
    simp only [zero_mulVec, add_zero]
    exact Iff.rfl
  constructor
  · intro hx
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
    refine ⟨fun v => w v, (key _).2 ⟨?_, ?_⟩, (hle _).2 fun F => hcv F x hx⟩
    · rw [← hw1]
      exact Finset.sum_coe_sort W w
    · rw [← hwx]
      exact Finset.sum_coe_sort W (fun v => w v • v)
  · rintro ⟨y, h1, h2⟩
    obtain ⟨hs, hx⟩ := (key y).1 h1
    refine mem_hull_of_facets W c δ hcv (fun G hG => ⟨⟨G, (hfs G).1 hG⟩, hcF ⟨G, _⟩⟩)
      (fun v => if hv : v ∈ W then y ⟨v, hv⟩ else 0) ?_ ?_ ((hle y).1 h2)
    · rw [← hs, ← Finset.sum_coe_sort W]
      simp
    · rw [← hx, ← Finset.sum_coe_sort W]
      simp

/-- **Theorem 3, (ii) ⇒ (iii)**. -/
theorem ef_of_extension {ι : Type*} [Fintype ι] {P : Set (ι → ℝ)} {e r : ℕ}
    {Q : Set (Fin e → ℝ)} (hext : IsExtension Q P) (hfac : HasAtMostFacets Q r) :
    ∃ r' ≤ r, IsEFOfSize P r' := by
  obtain ⟨⟨W, rfl⟩, π, hπ⟩ := hext
  obtain ⟨fs, hfs, hcard⟩ := hfac
  exact ⟨fs.card, hcard, isEF_image (isEF_of_facets W hfs) π hπ⟩

end VFacets

section HFacets

variable {κ R : Type*} [Fintype κ] [Fintype R]

lemma hpoly_convex (G : Matrix R κ ℝ) (k : R → ℝ) : Convex ℝ {z : κ → ℝ | G *ᵥ z ≤ k} := by
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk : k i = a * k i + b * k i := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma hpoly_closed (G : Matrix R κ ℝ) (k : R → ℝ) : IsClosed {z : κ → ℝ | G *ᵥ z ≤ k} :=
  isClosed_le (continuous_const.matrix_mulVec continuous_id) continuous_const

/-- An `H`-polyhedron has finitely many extreme points: an extreme point is determined by the set
of constraints tight at it. -/
lemma hpoly_extremePoints_finite (G : Matrix R κ ℝ) (k : R → ℝ) :
    ({z : κ → ℝ | G *ᵥ z ≤ k}.extremePoints ℝ).Finite := by
  classical
  let tight : (κ → ℝ) → Finset R := fun z => Finset.univ.filter fun i => (G *ᵥ z) i = k i
  refine Set.Finite.of_finite_image (f := tight) (Set.toFinite _) ?_
  intro z₁ hz₁ z₂ hz₂ heq
  have hz₁Q : G *ᵥ z₁ ≤ k := (mem_extremePoints.1 hz₁).1
  have htight : ∀ i, (G *ᵥ z₁) i = k i ↔ (G *ᵥ z₂) i = k i := fun i => by
    have := congrArg (i ∈ ·) heq
    simpa [tight] using this
  set d := z₁ - z₂ with hd
  have hdt : ∀ i, (G *ᵥ z₁) i = k i → (G *ᵥ d) i = 0 := by
    intro i h
    simp [d, mulVec_sub, h, (htight i).1 h]
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, (G *ᵥ (z₁ + s • d)) i ≤ k i ∧ (G *ᵥ (z₁ - s • d)) i ≤ k i := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases h : (G *ᵥ z₁) i = k i
    · refine Filter.Eventually.of_forall fun s => ?_
      simp [mulVec_add, mulVec_sub, mulVec_smul, hdt i h, h]
    · have hlt : (G *ᵥ z₁) i < k i := lt_of_le_of_ne (hz₁Q i) h
      have h1 : Tendsto (fun s : ℝ => (G *ᵥ (z₁ + s • d)) i) (𝓝 0) (𝓝 ((G *ᵥ z₁) i)) := by
        simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const ((G *ᵥ d) i)).const_add ((G *ᵥ z₁) i)
        simpa using this
      have h2 : Tendsto (fun s : ℝ => (G *ᵥ (z₁ - s • d)) i) (𝓝 0) (𝓝 ((G *ᵥ z₁) i)) := by
        simp only [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const ((G *ᵥ d) i)).const_sub ((G *ᵥ z₁) i)
        simpa using this
      exact ((h1.eventually (gt_mem_nhds hlt)).and (h2.eventually (gt_mem_nhds hlt))).mono
        fun s hs => ⟨hs.1.le, hs.2.le⟩
  obtain ⟨s, hs, hspos⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hspos' : (0 : ℝ) < s := hspos
  have hseg : z₁ ∈ openSegment ℝ (z₁ - s • d) (z₁ + s • d) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := ((mem_extremePoints.1 hz₁).2 (z₁ - s • d) (fun i => (hs i).2) (z₁ + s • d)
    (fun i => (hs i).1) hseg).1
  have hsd : s • d = 0 := by
    have h' : z₁ - s • d - z₁ = 0 := by rw [this, sub_self]
    simpa using h'
  rcases smul_eq_zero.1 hsd with h | h
  · exact absurd h hspos'.ne'
  · exact sub_eq_zero.1 h

/-- A bounded `H`-polyhedron is a polytope (Krein–Milman plus finiteness of extreme points). -/
lemma isPolytope_hpoly (G : Matrix R κ ℝ) (k : R → ℝ)
    (hb : Bornology.IsBounded {z : κ → ℝ | G *ᵥ z ≤ k}) : IsPolytope {z : κ → ℝ | G *ᵥ z ≤ k} := by
  have hc : IsCompact {z : κ → ℝ | G *ᵥ z ≤ k} :=
    Metric.isCompact_of_isClosed_isBounded (hpoly_closed G k) hb
  have hK := closure_convexHull_extremePoints hc (hpoly_convex G k)
  have hfin := hpoly_extremePoints_finite G k
  rw [(Set.Finite.isClosed_convexHull (𝕜 := ℝ) hfin).closure_eq] at hK
  exact ⟨hfin.toFinset, by rw [Finite.coe_toFinset]; exact hK.symm⟩

/-- Every facet of a compact `H`-polyhedron with two distinct points is cut out by a single
non-implicit constraint. -/
lemma facet_is_row (G : Matrix R κ ℝ) (k : R → ℝ) (hc : IsCompact {z : κ → ℝ | G *ᵥ z ≤ k})
    {y₁ y₂ : κ → ℝ} (hy₁ : G *ᵥ y₁ ≤ k) (hy₂ : G *ᵥ y₂ ≤ k) (hne : y₁ ≠ y₂) {F : Set (κ → ℝ)}
    (hF : IsFacet {z : κ → ℝ | G *ᵥ z ≤ k} F) :
    ∃ i, (∃ z, G *ᵥ z ≤ k ∧ (G *ᵥ z) i < k i) ∧
      F = {z | z ∈ {z : κ → ℝ | G *ᵥ z ≤ k} ∧ (G *ᵥ z) i = k i} := by
  classical
  set Q := {z : κ → ℝ | G *ᵥ z ≤ k} with hQ
  rcases F.eq_empty_or_nonempty with hFe | ⟨z₀, hz₀⟩
  · -- the empty set is not a facet: `Q` has a nonempty proper face
    exfalso
    set c := y₁ - y₂ with hcdef
    have hcont : Continuous fun x : κ → ℝ => c ⬝ᵥ x := continuous_const.dotProduct continuous_id
    obtain ⟨xm, hxm, hmax⟩ := hc.exists_isMaxOn ⟨y₁, hy₁⟩ hcont.continuousOn
    have hface : IsFace Q {x | x ∈ Q ∧ c ⬝ᵥ x = c ⬝ᵥ xm} :=
      Or.inr ⟨c, c ⬝ᵥ xm, sub_ne_zero.2 hne, fun x hx => isMaxOn_iff.1 hmax x hx, rfl⟩
    have hneQ : {x | x ∈ Q ∧ c ⬝ᵥ x = c ⬝ᵥ xm} ≠ Q := by
      intro h
      have h1 : y₁ ∈ {x | x ∈ Q ∧ c ⬝ᵥ x = c ⬝ᵥ xm} := by rw [h]; exact hy₁
      have h2 : y₂ ∈ {x | x ∈ Q ∧ c ⬝ᵥ x = c ⬝ᵥ xm} := by rw [h]; exact hy₂
      have hcc : c ⬝ᵥ c = 0 := by
        rw [hcdef, dotProduct_sub, h1.2, h2.2, sub_self]
      exact sub_ne_zero.2 hne (dotProduct_self_eq_zero.1 hcc)
    have := hF.2.2 _ hface hneQ (by rw [hFe]; exact empty_subset _)
    rw [hFe] at this
    have hxm' : xm ∈ {x | x ∈ Q ∧ c ⬝ᵥ x = c ⬝ᵥ xm} := ⟨hxm, rfl⟩
    rw [this] at hxm'
    exact hxm'
  · rcases hF.1 with h | ⟨c, δ, -, hv, hFdef⟩
    · exact absurd h hF.2.1
    have hz₀' : z₀ ∈ Q ∧ c ⬝ᵥ z₀ = δ := by rw [hFdef] at hz₀; exact hz₀
    obtain ⟨lam, hlam0, hlamc, hlamk⟩ := affine_farkas G k ⟨z₀, hz₀'.1⟩ c δ (fun x hx => hv x hx)
    have hcx : ∀ x, c ⬝ᵥ x = lam ⬝ᵥ (G *ᵥ x) := fun x => by rw [dotProduct_mulVec, hlamc]
    have hslack : ∀ x, lam ⬝ᵥ k - c ⬝ᵥ x = ∑ i, lam i * (k i - (G *ᵥ x) i) := by
      intro x
      rw [hcx]
      simp [dotProduct, mul_sub, Finset.sum_sub_distrib]
    have hlk : lam ⬝ᵥ k = δ := by
      refine le_antisymm hlamk ?_
      rw [← hz₀'.2]
      have := weak_duality hlam0 hz₀'.1
      rwa [hlamc] at this
    obtain ⟨y₀, hy₀Q, hy₀δ⟩ : ∃ y₀ ∈ Q, c ⬝ᵥ y₀ ≠ δ := by
      by_contra h
      push Not at h
      apply hF.2.1
      rw [hFdef]
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx⟩⟩
    have hy₀lt : c ⬝ᵥ y₀ < δ := lt_of_le_of_ne (hv y₀ hy₀Q) hy₀δ
    have hpos : 0 < ∑ i, lam i * (k i - (G *ᵥ y₀) i) := by rw [← hslack, hlk]; linarith
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < lam i * (k i - (G *ᵥ y₀) i) := by
      by_contra h
      push Not at h
      exact absurd (Finset.sum_nonpos h) (not_le.2 hpos)
    have hli : 0 < lam i := by
      by_contra h
      have h0 : lam i = 0 := le_antisymm (not_lt.1 h) (hlam0 i)
      rw [h0, zero_mul] at hi
      exact lt_irrefl _ hi
    have hsl : (G *ᵥ y₀) i < k i := by
      rcases (hy₀Q i).eq_or_lt with h | h
      · rw [h, sub_self, mul_zero] at hi; exact absurd hi (lt_irrefl 0)
      · exact h
    have hsub : F ⊆ {z | z ∈ Q ∧ (G *ᵥ z) i = k i} := by
      intro x hx
      rw [hFdef] at hx
      have h0 : ∑ j, lam j * (k j - (G *ᵥ x) j) = 0 := by rw [← hslack, hlk, hx.2, sub_self]
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (hlam0 j) (sub_nonneg.2 (hx.1 j))).1 h0 i (Finset.mem_univ _)
      rcases mul_eq_zero.1 hj with h | h
      · exact absurd h hli.ne'
      · exact ⟨hx.1, by linarith⟩
    have hrow : (fun j => G i j) ≠ 0 := by
      intro h
      have e1 : (G *ᵥ y₀) i = 0 := by simp [mulVec, h]
      have hz : (G *ᵥ z₀) i = k i := (hsub hz₀).2
      have e2 : (G *ᵥ z₀) i = 0 := by simp [mulVec, h]
      linarith
    have hface : IsFace Q {z | z ∈ Q ∧ (G *ᵥ z) i = k i} :=
      Or.inr ⟨fun j => G i j, k i, hrow, fun x hx => hx i, rfl⟩
    have hneQ : {z | z ∈ Q ∧ (G *ᵥ z) i = k i} ≠ Q := by
      intro h
      have : y₀ ∈ {z | z ∈ Q ∧ (G *ᵥ z) i = k i} := by rw [h]; exact hy₀Q
      exact hsl.ne this.2
    exact ⟨i, ⟨y₀, hy₀Q, hsl⟩, (hF.2.2 _ hface hneQ hsub).symm⟩

/-- A compact `H`-polyhedron with two distinct points has at most as many facets as it has
non-implicit constraints. -/
lemma hasAtMostFacets_hpoly (G : Matrix R κ ℝ) (k : R → ℝ) (hc : IsCompact {z : κ → ℝ | G *ᵥ z ≤ k})
    {y₁ y₂ : κ → ℝ} (hy₁ : G *ᵥ y₁ ≤ k) (hy₂ : G *ᵥ y₂ ≤ k) (hne : y₁ ≠ y₂) (S : Finset R)
    (hS : ∀ i, (∃ z, G *ᵥ z ≤ k ∧ (G *ᵥ z) i < k i) → i ∈ S) :
    HasAtMostFacets {z : κ → ℝ | G *ᵥ z ≤ k} S.card := by
  classical
  set Q := {z : κ → ℝ | G *ᵥ z ≤ k} with hQ
  let Fr : R → Set (κ → ℝ) := fun i => {z | z ∈ Q ∧ (G *ᵥ z) i = k i}
  refine ⟨(Finset.univ.filter fun i => IsFacet Q (Fr i)).image Fr, fun F => ?_, ?_⟩
  · constructor
    · intro hF
      obtain ⟨i, -, rfl⟩ := facet_is_row G k hc hy₁ hy₂ hne hF
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hF⟩, rfl⟩
    · intro hF
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hF
      exact (Finset.mem_filter.1 hi).2
  · refine Finset.card_image_le.trans (Finset.card_le_card fun i hi => hS i ?_)
    have hF := (Finset.mem_filter.1 hi).2
    obtain ⟨j, ⟨z, hz, hzj⟩, hFj⟩ := facet_is_row G k hc hy₁ hy₂ hne hF
    by_contra h
    push Not at h
    apply hF.2.1
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, le_antisymm (hx i) (h x hx)⟩⟩

end HFacets

section Yannakakis

variable {ι : Type*} [Fintype ι]

lemma exists_lo_hi {P : Set (ι → ℝ)} (hc : IsCompact P) {x y : ι → ℝ} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : x ≠ y) : ∃ (u : ι → ℝ) (lo hi : ℝ), IsLeast ((fun x => u ⬝ᵥ x) '' P) lo ∧
      IsGreatest ((fun x => u ⬝ᵥ x) '' P) hi ∧ lo < hi := by
  set u := x - y with hu
  have hcont : Continuous fun z : ι → ℝ => u ⬝ᵥ z := continuous_const.dotProduct continuous_id
  obtain ⟨xl, hxl, hmin⟩ := hc.exists_isMinOn ⟨x, hx⟩ hcont.continuousOn
  obtain ⟨xh, hxh, hmax⟩ := hc.exists_isMaxOn ⟨x, hx⟩ hcont.continuousOn
  refine ⟨u, u ⬝ᵥ xl, u ⬝ᵥ xh, ⟨⟨xl, hxl, rfl⟩, ?_⟩, ⟨⟨xh, hxh, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact isMinOn_iff.1 hmin z hz
  · rintro _ ⟨z, hz, rfl⟩
    exact isMaxOn_iff.1 hmax z hz
  · have h1 := isMinOn_iff.1 hmin y hy
    have h2 := isMaxOn_iff.1 hmax x hx
    have hpos : 0 < u ⬝ᵥ u := by
      rcases (show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun i _ => mul_self_nonneg _).eq_or_lt
        with h | h
      · exact absurd (dotProduct_self_eq_zero.1 h.symm) (sub_ne_zero.2 hxy)
      · exact h
    have : u ⬝ᵥ x - u ⬝ᵥ y = u ⬝ᵥ u := by rw [hu, ← dotProduct_sub]
    linarith

/-- **Theorem 3, (i) ⇒ (ii), core**: from a nonnegative factorization `S = T U` of the slack
matrix in which every column of `T` has a positive entry, the polytope
`Q = {(x, y) | Ax + Ty = b, y ≥ 0}` is an extension of `P` with at most `r` facets. -/
theorem extension_of_factorization {m N r : ℕ} (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ)
    (V : Fin N → ι → ℝ) (P : Set (ι → ℝ)) (hPA : P = {x | A *ᵥ x ≤ b})
    (hPV : P = convexHull ℝ (Set.range V)) (hdim : ∃ x ∈ P, ∃ y ∈ P, x ≠ y)
    (T : Matrix (Fin m) (Fin r) ℝ) (U : Matrix (Fin r) (Fin N) ℝ) (hT : ∀ i l, 0 ≤ T i l)
    (hU : ∀ l j, 0 ≤ U l j) (hTU : slackMatrix A b V = T * U) (hcol : ∀ l, ∃ i, 0 < T i l) :
    ∃ (e : ℕ) (Q : Set (Fin e → ℝ)), IsExtension Q P ∧ HasAtMostFacets Q r := by
  classical
  let σ := Fintype.equivFin (ι ⊕ Fin r)
  set e := Fintype.card (ι ⊕ Fin r)
  let xp : (Fin e → ℝ) → ι → ℝ := fun z a => z (σ (Sum.inl a))
  let yp : (Fin e → ℝ) → Fin r → ℝ := fun z l => z (σ (Sum.inr l))
  let G0 : Matrix ((Fin m ⊕ Fin m) ⊕ Fin r) (ι ⊕ Fin r) ℝ :=
    fromRows (fromRows (fromCols A T) (-fromCols A T)) (fromCols 0 (-1))
  let G : Matrix ((Fin m ⊕ Fin m) ⊕ Fin r) (Fin e) ℝ := G0.submatrix id σ.symm
  let k : (Fin m ⊕ Fin m) ⊕ Fin r → ℝ := Sum.elim (Sum.elim b (-b)) 0
  have hGz : ∀ z, G *ᵥ z = Sum.elim (Sum.elim (A *ᵥ xp z + T *ᵥ yp z)
      (-(A *ᵥ xp z + T *ᵥ yp z))) (-(yp z)) := by
    intro z
    simp only [G, G0, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id,
      fromRows_mulVec, fromCols_mulVec, neg_mulVec, zero_mulVec, one_mulVec, zero_add]
    rfl
  have hmem : ∀ z, G *ᵥ z ≤ k ↔ A *ᵥ xp z + T *ᵥ yp z = b ∧ ∀ l, 0 ≤ yp z l := by
    intro z
    rw [hGz]
    simp only [k, Pi.le_def, Sum.forall, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      neg_le_neg_iff, Pi.zero_apply, neg_nonpos]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨funext fun i => le_antisymm (h1 i) (h2 i), h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨fun i => (congrFun h1 i).le, fun i => (congrFun h1 i).ge⟩, h3⟩
  have hTy : ∀ y : Fin r → ℝ, (∀ l, 0 ≤ y l) → ∀ i, 0 ≤ (T *ᵥ y) i := fun y hy i => by
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hT i l) (hy l)
  -- projection
  have hproj : ∀ z, G *ᵥ z ≤ k → xp z ∈ P := by
    intro z hz
    obtain ⟨h1, h2⟩ := (hmem z).1 hz
    rw [hPA]
    intro i
    have := congrFun h1 i
    have := hTy _ h2 i
    simp only [Pi.add_apply] at *
    linarith
  -- lifting
  have hlift : ∀ x ∈ P, ∃ z, G *ᵥ z ≤ k ∧ xp z = x := by
    intro x hx
    rw [hPV] at hx
    obtain ⟨w, hw0, hw1, hwx⟩ := (mem_convexHull_range_iff V x).1 hx
    let z : Fin e → ℝ := Sum.elim x (U *ᵥ w) ∘ σ.symm
    have hxz : xp z = x := funext fun a => by simp [xp, z]
    have hyz : yp z = U *ᵥ w := funext fun l => by simp [yp, z]
    refine ⟨z, (hmem z).2 ⟨?_, fun l => ?_⟩, hxz⟩
    · rw [hxz, hyz, mulVec_mulVec, ← hTU]
      funext i
      have hAx : (A *ᵥ x) i = ∑ j, w j * (A *ᵥ V j) i := by
        rw [← hwx, mulVec_sum]
        simp [mulVec_smul, Finset.sum_apply]
      have hS : (slackMatrix A b V *ᵥ w) i = ∑ j, (b i - (A *ᵥ V j) i) * w j := rfl
      have : ∑ j, (b i - (A *ᵥ V j) i) * w j = b i * ∑ j, w j - ∑ j, w j * (A *ᵥ V j) i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [Pi.add_apply, hS, this, hw1, hAx]
      ring
    · rw [hyz]
      simp only [mulVec, dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hU l j) (hw0 j)
  -- boundedness
  have hPc : IsCompact P := by
    rw [hPV]
    exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range V)
  obtain ⟨R1, hR1⟩ := isBounded_iff_forall_norm_le.1 hPc.isBounded
  have hB : ∀ i, ∃ B, ∀ x ∈ P, b i - (A *ᵥ x) i ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := hPc.bddAbove_image (f := fun x => b i - (A *ᵥ x) i)
      ((continuous_const.sub ((continuous_apply i).comp
        (continuous_const.matrix_mulVec continuous_id))).continuousOn)
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose B hB using hB
  choose il hil using hcol
  set Rb := |R1| + ∑ l, |B (il l) / T (il l) l|
  have hRb : 0 ≤ Rb := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hbdd : Bornology.IsBounded {z : Fin e → ℝ | G *ᵥ z ≤ k} := by
    refine isBounded_iff_forall_norm_le.2 ⟨Rb, fun z hz => ?_⟩
    have hz' := (hmem z).1 hz
    have hxP := hproj z hz
    refine (pi_norm_le_iff_of_nonneg hRb).2 fun q => ?_
    have hq : q = σ (σ.symm q) := (σ.apply_symm_apply q).symm
    rcases hσ : σ.symm q with a | l
    · rw [hq, hσ]
      calc ‖z (σ (Sum.inl a))‖ = ‖xp z a‖ := rfl
        _ ≤ ‖xp z‖ := norm_le_pi_norm (xp z) a
        _ ≤ R1 := hR1 _ hxP
        _ ≤ |R1| := le_abs_self _
        _ ≤ Rb := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    · rw [hq, hσ]
      have hy0 := hz'.2 l
      have hTl : T (il l) l * yp z l ≤ B (il l) := by
        have h1 : T (il l) l * yp z l ≤ (T *ᵥ yp z) (il l) :=
          Finset.single_le_sum (f := fun l' => T (il l) l' * yp z l')
            (fun l' _ => mul_nonneg (hT _ l') (hz'.2 l')) (Finset.mem_univ l)
        have h2 := congrFun hz'.1 (il l)
        have h3 := hB (il l) _ hxP
        simp only [Pi.add_apply] at h2
        linarith
      calc ‖z (σ (Sum.inr l))‖ = yp z l := Real.norm_of_nonneg hy0
        _ ≤ B (il l) / T (il l) l := by rw [le_div_iff₀ (hil l)]; linarith
        _ ≤ |B (il l) / T (il l) l| := le_abs_self _
        _ ≤ ∑ l', |B (il l') / T (il l') l'| :=
          Finset.single_le_sum (f := fun l' => |B (il l') / T (il l') l'|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
        _ ≤ Rb := le_add_of_nonneg_left (abs_nonneg _)
  have hQc : IsCompact {z : Fin e → ℝ | G *ᵥ z ≤ k} :=
    Metric.isCompact_of_isClosed_isBounded (hpoly_closed G k) hbdd
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁₂⟩ := hdim
  obtain ⟨z₁, hz₁, rfl⟩ := hlift x₁ hx₁
  obtain ⟨z₂, hz₂, rfl⟩ := hlift x₂ hx₂
  have hz₁₂ : z₁ ≠ z₂ := fun h => hx₁₂ (by rw [h])
  refine ⟨e, {z | G *ᵥ z ≤ k}, ⟨isPolytope_hpoly G k hbdd,
    LinearMap.funLeft ℝ ℝ (σ ∘ Sum.inl), ?_⟩, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hproj z hz
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hlift x hx
      exact ⟨z, hz, rfl⟩
  · have h := hasAtMostFacets_hpoly G k hQc hz₁ hz₂ hz₁₂
      (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) fun i ⟨z, hz, hzi⟩ => ?_
    · rwa [Finset.card_map, Finset.card_univ, Fintype.card_fin] at h
    · have hz' := (hmem z).1 hz
      rw [hGz] at hzi
      rcases i with (i | i) | l
      · simp only [k, Sum.elim_inl, hz'.1, lt_irrefl] at hzi
      · simp only [k, Sum.elim_inl, Sum.elim_inr, hz'.1, lt_irrefl] at hzi
      · exact Finset.mem_map_of_mem _ (Finset.mem_univ l)

/-- **Theorem 3** [Yannakakis 1991]. -/
theorem yannakakis_tfae {m N : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (V : Fin N → ι → ℝ) (P : Set (ι → ℝ))
    (hPA : P = {x | A *ᵥ x ≤ b}) (hPV : P = convexHull ℝ (Set.range V))
    (hdim : ∃ x ∈ P, ∃ y ∈ P, x ≠ y) (r : ℕ) :
    List.TFAE
      [nonnegRank (slackMatrix A b V) ≤ r,
       ∃ (e : ℕ) (Q : Set (Fin e → ℝ)), IsExtension Q P ∧ HasAtMostFacets Q r,
       ∃ r' ≤ r, IsEFOfSize P r'] := by
  classical
  have hPc : IsCompact P := by
    rw [hPV]
    exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range V)
  have hVP : ∀ j, V j ∈ P := fun j => hPV ▸ subset_convexHull ℝ _ (mem_range_self j)
  tfae_have 1 → 2 := by
    intro h
    -- `S ≥ 0`, so `S = S · 1` and the infimum is attained
    have hS0 : ∀ i j, 0 ≤ slackMatrix A b V i j := fun i j => by
      have := (show V j ∈ {x | A *ᵥ x ≤ b} by rw [← hPA]; exact hVP j) i
      simp only [slackMatrix]
      linarith
    have hne : HasNonnegFactorization (slackMatrix A b V) N :=
      ⟨slackMatrix A b V, 1, hS0, fun l j => by
        rw [Matrix.one_apply]; split_ifs <;> norm_num, (Matrix.mul_one _).symm⟩
    obtain ⟨T, U, hT, hU, hTU⟩ := Nat.sInf_mem (s := {r | HasNonnegFactorization
      (slackMatrix A b V) r}) ⟨N, hne⟩
    -- `m ≥ 1`: otherwise `P` would be the whole (nontrivial) space
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        exfalso
        obtain ⟨x, -, y, -, hxy⟩ := hdim
        have : Nontrivial (ι → ℝ) := ⟨⟨x, y, hxy⟩⟩
        have : P = univ := by
          rw [hPA]
          exact eq_univ_of_forall fun x i => i.elim0
        exact NormedSpace.unbounded_univ ℝ (ι → ℝ) (this ▸ hPc.isBounded)
      · exact hm
    -- make every column of `T` nonzero
    let zc : Fin (nonnegRank (slackMatrix A b V)) → Prop := fun l => ∀ i, T i l = 0
    let T' : Matrix (Fin m) (Fin (nonnegRank (slackMatrix A b V))) ℝ :=
      fun i l => if zc l then 1 else T i l
    let U' : Matrix (Fin (nonnegRank (slackMatrix A b V))) (Fin N) ℝ :=
      fun l j => if zc l then 0 else U l j
    have hT'U' : slackMatrix A b V = T' * U' := by
      refine hTU.trans ?_
      ext i j
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : zc l
      · simp [T', U', h, h i]
      · simp [T', U', h]
    have hcol : ∀ l, ∃ i, 0 < T' i l := by
      intro l
      by_cases h : zc l
      · exact ⟨⟨0, hm⟩, by simp [T', h]⟩
      · simp only [zc, not_forall] at h
        obtain ⟨i, hi⟩ := h
        exact ⟨i, by simpa [T', zc, show ¬ ∀ i, T i l = 0 from fun h' => hi (h' i)] using
          lt_of_le_of_ne (hT i l) (Ne.symm hi)⟩
    obtain ⟨e, Q, hext, fs, hfs, hcard⟩ := extension_of_factorization A b V P hPA hPV hdim T' U'
      (fun i l => by by_cases h : zc l <;> simp [T', h, hT i l])
      (fun l j => by by_cases h : zc l <;> simp [U', h, hU l j]) hT'U' hcol
    exact ⟨e, Q, hext, fs, hfs, hcard.trans h⟩
  tfae_have 2 → 3 := fun ⟨e, Q, hext, hfac⟩ => ef_of_extension hext hfac
  tfae_have 3 → 1 := by
    rintro ⟨r', hr', hEF⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hdim
    obtain ⟨u, lo, hi, hlo, hhi, hlohi⟩ := exists_lo_hi hPc hx hy hxy
    have hval : ∀ i, ∀ x ∈ P, (fun a => A i a) ⬝ᵥ x ≤ b i := fun i x hx =>
      (show x ∈ {x | A *ᵥ x ≤ b} by rw [← hPA]; exact hx) i
    have := nonnegFactorization_of_EF hEF u lo hi hlo hhi hlohi (fun i a => A i a) b hval V hVP
    exact (Nat.sInf_le this).trans hr'
  tfae_finish

end Yannakakis

end XCT

open Matrix ExtensionComplexity.TSP

theorem solution {ι : Type*} [Fintype ι] {m N : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (V : Fin N → ι → ℝ) (P : Set (ι → ℝ))
    (hPA : P = {x | A *ᵥ x ≤ b}) (hPV : P = convexHull ℝ (Set.range V))
    (hdim : ∃ x ∈ P, ∃ y ∈ P, x ≠ y) (r : ℕ) (hr : 1 ≤ r) :
    List.TFAE
      [nonnegRank (slackMatrix A b V) ≤ r,
       ∃ (e : ℕ) (Q : Set (Fin e → ℝ)), IsExtension Q P ∧ HasAtMostFacets Q r,
       ∃ r' ≤ r, IsEFOfSize P r'] :=
  XCT.yannakakis_tfae A b V P hPA hPV hdim r
