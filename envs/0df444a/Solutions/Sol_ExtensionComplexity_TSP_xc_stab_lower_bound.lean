-- Prove2me | solution 1 for ExtensionComplexity.TSP.xc_stab_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T23:12:07.444461+00:00
-- url     : https://prove2.me/submissions/51fe952b-0cf1-4bcc-a525-42231f197816

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope


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


open Matrix ExtensionComplexity.TSP Set ChvatalPolytopes.Shared

namespace XCT

section Stab

variable (p k : ℕ)

/-- Pairs `i < j` (edges of `K_p`). -/
abbrev Pair := {q : Fin p × Fin p // q.1 < q.2}

/-- Vertices of `H_p`, padded with `k` isolated vertices: vertex cliques `(i, x)`, edge cliques
`(q, (α, β))`, isolated vertices. -/
abbrev SV := (Fin p × Bool) ⊕ ((Pair p × (Bool × Bool)) ⊕ Fin k)

variable {p k}

/-- One direction of the adjacency relation of `H_p`. -/
def srel : SV p k → SV p k → Prop
  | Sum.inl (i, x), Sum.inl (j, y) => i = j ∧ x ≠ y
  | Sum.inr (Sum.inl (q, t)), Sum.inr (Sum.inl (q', t')) => q = q' ∧ t ≠ t'
  | Sum.inl (i, x), Sum.inr (Sum.inl (q, (α, β))) =>
      (i = q.1.1 ∧ x ≠ α) ∨ (i = q.1.2 ∧ x ≠ β)
  | _, _ => False

variable (p k) in
/-- The graph `H_p` (Lemma 8) with `k` isolated vertices added. -/
def SG : SimpleGraph (SV p k) := SimpleGraph.fromRel srel

/-- Membership indicator. -/
noncomputable def ind {α : Type*} [DecidableEq α] (s : Finset α) (v : α) : ℝ :=
  if v ∈ s then 1 else 0

/-- The weight vector of the face: `1` on the cliques, `-1` on the isolated vertices. -/
def cw : SV p k → ℝ
  | Sum.inr (Sum.inr _) => -1
  | _ => 1

variable (p) in
/-- Number of cliques. -/
noncomputable def ncl : ℝ := p + Fintype.card (Pair p)

/-- Vertex-clique count. -/
noncomputable def Acnt (s : Finset (SV p k)) (i : Fin p) : ℝ :=
  ∑ x : Bool, ind s (Sum.inl (i, x))

/-- Edge-clique count. -/
noncomputable def Ecnt (s : Finset (SV p k)) (q : Pair p) : ℝ :=
  ∑ t : Bool × Bool, ind s (Sum.inr (Sum.inl (q, t)))

lemma ind_nonneg {α : Type*} [DecidableEq α] (s : Finset α) (v : α) : 0 ≤ ind s v := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one {α : Type*} [DecidableEq α] (s : Finset α) (v : α) : ind s v ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma cw_dot (s : Finset (SV p k)) :
    cw ⬝ᵥ incidenceVector s = ∑ i, Acnt s i + ∑ q, Ecnt s q - ∑ j, ind s (Sum.inr (Sum.inr j)) := by
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, cw,
    incidenceVector, Acnt, Ecnt, ind, one_mul, neg_one_mul, Finset.sum_neg_distrib]
  ring

lemma adj_iff (a b : SV p k) : (SG p k).Adj a b ↔ a ≠ b ∧ (srel a b ∨ srel b a) :=
  SimpleGraph.fromRel_adj _ _ _

lemma Acnt_le {s : Finset (SV p k)} (hs : (SG p k).IsIndepSet (s : Set (SV p k))) (i : Fin p) :
    Acnt s i ≤ 1 := by
  unfold Acnt ind
  rw [Fintype.sum_bool]
  by_cases h0 : (Sum.inl (i, false) : SV p k) ∈ s <;> by_cases h1 : (Sum.inl (i, true) : SV p k) ∈ s
  · exfalso
    refine hs h0 h1 (by simp) ?_
    rw [adj_iff]
    exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
  all_goals simp [h0, h1]

lemma sum_ind_le_one {T : Type*} [Fintype T] (P : T → Prop) [DecidablePred P]
    (h : ∀ t t', P t → P t' → t = t') : (∑ t, if P t then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  exact_mod_cast Finset.card_le_one.2 fun a ha b hb =>
    h a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2

lemma Ecnt_le {s : Finset (SV p k)} (hs : (SG p k).IsIndepSet (s : Set (SV p k))) (q : Pair p) :
    Ecnt s q ≤ 1 := by
  simp only [Ecnt, ind]
  refine @sum_ind_le_one _ _ (fun t => (Sum.inr (Sum.inl (q, t)) : SV p k) ∈ s)
    (fun t => Finset.decidableMem _ s) fun t t' ht ht' => ?_
  by_contra hne
  refine hs ht ht' (by simpa using hne) ?_
  rw [adj_iff]
  exact ⟨by simpa using hne, Or.inl ⟨rfl, hne⟩⟩

lemma cw_le {s : Finset (SV p k)} (hs : (SG p k).IsIndepSet (s : Set (SV p k))) :
    cw ⬝ᵥ incidenceVector s ≤ ncl p := by
  rw [cw_dot, ncl]
  have h1 : ∑ i, Acnt s i ≤ p := by
    calc ∑ i, Acnt s i ≤ ∑ _i : Fin p, (1 : ℝ) := Finset.sum_le_sum fun i _ => Acnt_le hs i
      _ = p := by simp
  have h2 : ∑ q, Ecnt s q ≤ Fintype.card (Pair p) := by
    calc ∑ q, Ecnt s q ≤ ∑ _q : Pair p, (1 : ℝ) := Finset.sum_le_sum fun q _ => Ecnt_le hs q
      _ = Fintype.card (Pair p) := by simp
  have h3 : 0 ≤ ∑ j, ind s (Sum.inr (Sum.inr j) : SV p k) :=
    Finset.sum_nonneg fun j _ => ind_nonneg _ _
  linarith

lemma cw_tight {s : Finset (SV p k)} (hs : (SG p k).IsIndepSet (s : Set (SV p k)))
    (h : cw ⬝ᵥ incidenceVector s = ncl p) :
    (∀ i, Acnt s i = 1) ∧ (∀ q, Ecnt s q = 1) := by
  rw [cw_dot, ncl] at h
  have hA : ∀ i, 0 ≤ 1 - Acnt s i := fun i => sub_nonneg.2 (Acnt_le hs i)
  have hE : ∀ q, 0 ≤ 1 - Ecnt s q := fun q => sub_nonneg.2 (Ecnt_le hs q)
  have hP : ∀ j, 0 ≤ ind s (Sum.inr (Sum.inr j) : SV p k) := fun j => ind_nonneg _ _
  have htot : ∑ i, (1 - Acnt s i) + ∑ q, (1 - Ecnt s q) +
      ∑ j, ind s (Sum.inr (Sum.inr j) : SV p k) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    linarith
  have hs1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hA i
  have hs2 := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => hE q
  have hs3 := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hP j
  have e1 : ∑ i, (1 - Acnt s i) = 0 := by linarith
  have e2 : ∑ q, (1 - Ecnt s q) = 0 := by linarith
  refine ⟨fun i => ?_, fun q => ?_⟩
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hA i).1 e1 i (Finset.mem_univ _)
    linarith
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hE q).1 e2 q (Finset.mem_univ _)
    linarith

/-- The projection to `ℝ^{p×p}`. -/
noncomputable def spi (x : SV p k → ℝ) (ij : Fin p × Fin p) : ℝ :=
  if h : ij.1 = ij.2 then x (Sum.inl (ij.1, true))
  else if h' : ij.1 < ij.2 then x (Sum.inr (Sum.inl (⟨ij, h'⟩, (true, true))))
  else x (Sum.inr (Sum.inl (⟨(ij.2, ij.1), lt_of_le_of_ne (not_lt.1 h') (Ne.symm h)⟩,
    (true, true))))

variable (p k) in
noncomputable def spiL : (SV p k → ℝ) →ₗ[ℝ] (Fin p × Fin p → ℝ) where
  toFun := spi
  map_add' x y := by
    funext ij
    simp only [spi, Pi.add_apply]
    split_ifs <;> rfl
  map_smul' c x := by
    funext ij
    simp only [spi, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

open Classical in
/-- The stable set of `H_p` attached to `b`. -/
noncomputable def sset (b : Fin p → Bool) : Finset (SV p k) :=
  Finset.univ.filter fun v => match v with
    | Sum.inl (i, x) => x = b i
    | Sum.inr (Sum.inl (q, (α, β))) => α = b q.1.1 ∧ β = b q.1.2
    | Sum.inr (Sum.inr _) => False

lemma sset_indep (b : Fin p → Bool) : (SG p k).IsIndepSet (sset (k := k) b : Set (SV p k)) := by
  intro u hu v hv huv hadj
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, sset] at hu hv
  rw [adj_iff] at hadj
  obtain ⟨-, hr⟩ := hadj
  rcases u with ⟨i, x⟩ | ⟨⟨q, ⟨α, β⟩⟩⟩ | j <;> rcases v with ⟨i', x'⟩ | ⟨⟨q', ⟨α', β'⟩⟩⟩ | j' <;>
    simp only [srel] at hr hu hv <;> try simp_all
  all_goals first
    | (rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all)
    | (obtain ⟨rfl, h⟩ := hr; simp_all)
    | (rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all)

lemma spi_sset (b : Fin p → Bool) :
    spi (incidenceVector (sset (k := k) b)) = outerBits b := by
  funext ⟨i, j⟩
  simp only [spi, outerBits, bitVec, incidenceVector, sset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  split_ifs <;> simp_all <;> cases b i <;> cases b j <;> simp_all

lemma sset_tight (b : Fin p → Bool) : cw ⬝ᵥ incidenceVector (sset (k := k) b) = ncl p := by
  rw [cw_dot, ncl]
  have hA : ∀ i, Acnt (sset (k := k) b) i = 1 := fun i => by
    simp only [Acnt, ind, sset, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.sum_bool]
    cases b i <;> simp
  have hE : ∀ q, Ecnt (sset (k := k) b) q = 1 := fun q => by
    simp only [Ecnt, ind, sset, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases b q.1.1 <;> cases b q.1.2 <;> simp
  have hP : ∀ j, ind (sset (k := k) b) (Sum.inr (Sum.inr j) : SV p k) = 0 := fun j => by
    simp [ind, sset]
  simp [hA, hE, hP]

/-- A tight stable set is the stable set of some `b`. -/
lemma tight_eq_sset {s : Finset (SV p k)} (hs : (SG p k).IsIndepSet (s : Set (SV p k)))
    (h : cw ⬝ᵥ incidenceVector s = ncl p) :
    spi (incidenceVector s) = outerBits (fun i => decide ((Sum.inl (i, true) : SV p k) ∈ s)) := by
  classical
  obtain ⟨hA, hE⟩ := cw_tight hs h
  set b : Fin p → Bool := fun i => decide ((Sum.inl (i, true) : SV p k) ∈ s)
  -- the vertex `(i, b i)` lies in `s`, the other one does not
  have hv : ∀ i x, (Sum.inl (i, x) : SV p k) ∈ s ↔ x = b i := by
    intro i x
    have := hA i
    simp only [Acnt, ind, Fintype.sum_bool] at this
    by_cases h0 : (Sum.inl (i, false) : SV p k) ∈ s <;>
      by_cases h1 : (Sum.inl (i, true) : SV p k) ∈ s <;> simp [h0, h1] at this <;>
      cases x <;> simp [b, h0, h1]
  -- in the edge clique of `q`, the chosen vertex is `(b i, b j)`
  have he : ∀ (q : Pair p) (t : Bool × Bool), (Sum.inr (Sum.inl (q, t)) : SV p k) ∈ s →
      t = (b q.1.1, b q.1.2) := by
    intro q ⟨α, β⟩ ht
    have hi := (hv q.1.1 (b q.1.1)).2 rfl
    have hj := (hv q.1.2 (b q.1.2)).2 rfl
    by_contra hne
    have : α ≠ b q.1.1 ∨ β ≠ b q.1.2 := by
      by_contra h'
      push Not at h'
      exact hne (by rw [h'.1, h'.2])
    rcases this with h' | h'
    · refine hs hi ht (by simp) ?_
      rw [adj_iff]
      exact ⟨by simp, Or.inl (Or.inl ⟨rfl, Ne.symm h'⟩)⟩
    · refine hs hj ht (by simp) ?_
      rw [adj_iff]
      exact ⟨by simp, Or.inl (Or.inr ⟨rfl, Ne.symm h'⟩)⟩
  have hmemE : ∀ q : Pair p, (Sum.inr (Sum.inl (q, (b q.1.1, b q.1.2))) : SV p k) ∈ s := by
    intro q
    by_contra hn
    have := hE q
    simp only [Ecnt, ind] at this
    have h0 : ∀ t : Bool × Bool, (if (Sum.inr (Sum.inl (q, t)) : SV p k) ∈ s then (1 : ℝ) else 0) = 0 :=
      fun t => by
        rw [if_neg]
        intro ht
        exact hn (he q t ht ▸ ht)
    simp [h0] at this
  have hTT : ∀ q : Pair p, (Sum.inr (Sum.inl (q, (true, true))) : SV p k) ∈ s ↔
      (b q.1.1 = true ∧ b q.1.2 = true) := by
    intro q
    constructor
    · intro h
      have := he q _ h
      simp only [Prod.mk.injEq] at this
      exact ⟨this.1.symm, this.2.symm⟩
    · rintro ⟨h1, h2⟩
      have := hmemE q
      rwa [h1, h2] at this
  have hbm : ∀ i j : Fin p, bitVec b i * bitVec b j = if (b i = true ∧ b j = true) then 1 else 0 :=
    fun i j => by unfold bitVec; cases b i <;> cases b j <;> simp
  funext ⟨i, j⟩
  simp only [outerBits, hbm, spi]
  by_cases hij : i = j
  · subst hij
    simp only [dif_pos rfl, incidenceVector, and_self]
    by_cases hm : (Sum.inl (i, true) : SV p k) ∈ s
    · simp [hm, b]
    · simp [hm, b]
  · by_cases hlt : i < j
    · simp only [dif_neg hij, dif_pos hlt, incidenceVector]
      have := hTT ⟨(i, j), hlt⟩
      by_cases hm : (Sum.inr (Sum.inl (⟨(i, j), hlt⟩, (true, true))) : SV p k) ∈ s
      · rw [if_pos hm, if_pos (this.1 hm)]
      · rw [if_neg hm, if_neg (fun h => hm (this.2 h))]
    · simp only [dif_neg hij, dif_neg hlt, incidenceVector]
      have := hTT ⟨(j, i), lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij)⟩
      by_cases hm : (Sum.inr (Sum.inl (⟨(j, i), lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij)⟩,
        (true, true))) : SV p k) ∈ s
      · rw [if_pos hm, if_pos (And.symm (this.1 hm))]
      · rw [if_neg hm, if_neg (fun h => hm (this.2 (And.symm h)))]

/-- The face of `STAB(H_p ⊕ K̄_k)` of maximum stable sets avoiding the isolated vertices projects
onto `COR(p)`. -/
lemma stab_face (hp : 1 ≤ p) :
    ∃ F : Set (SV p k → ℝ), IsFace (stablePolytope (SG p k)) F ∧ IsExtension F (corPolytope p) := by
  classical
  have hv : ∀ x ∈ stableVectors (SG p k), cw ⬝ᵥ x ≤ ncl p := by
    rintro _ ⟨s, hs, rfl⟩
    exact cw_le hs
  have hcw : (cw : SV p k → ℝ) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl (⟨0, hp⟩, true))
    simp [cw] at this
  refine ⟨{x | x ∈ stablePolytope (SG p k) ∧ cw ⬝ᵥ x = ncl p}, Or.inr ⟨cw, ncl p, hcw, ?_, rfl⟩, ?_⟩
  · intro x hx
    unfold stablePolytope at hx
    have hconv : Convex ℝ {x : SV p k → ℝ | cw ⬝ᵥ x ≤ ncl p} := by
      have : {x : SV p k → ℝ | cw ⬝ᵥ x ≤ ncl p} = (fun x => cw ⬝ᵥ x) ⁻¹' Iic (ncl p) := rfl
      rw [this]
      exact (convex_Iic _).linear_preimage (dotProductBilin ℝ ℝ cw)
    exact convexHull_min hv hconv hx
  have hface := face_convexHull (stableVectors (SG p k)) cw (ncl p) hv
  unfold stablePolytope
  rw [hface]
  refine ⟨isPolytope_of_finite ?_, spiL p k, ?_⟩
  · refine Set.Finite.subset (Set.finite_range (fun s : Finset (SV p k) => incidenceVector s)) ?_
    rintro _ ⟨⟨s, -, rfl⟩, -⟩
    exact mem_range_self s
  rw [LinearMap.image_convexHull]
  unfold corPolytope
  congr 1
  ext y
  simp only [mem_image, Set.mem_ofPred_eq, mem_range]
  constructor
  · rintro ⟨_, ⟨⟨s, hs, rfl⟩, ht⟩, rfl⟩
    exact ⟨_, (tight_eq_sset hs ht).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨⟨sset b, sset_indep b, rfl⟩, sset_tight b⟩, spi_sset b⟩

end Stab

end XCT


open Matrix ExtensionComplexity.TSP Set ChvatalPolytopes.Shared

namespace XCT

section StabTransport

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

lemma stablePolytope_comap (G : SimpleGraph V) (e : V ≃ W) :
    stablePolytope (G.comap e.symm) = re e '' stablePolytope G := by
  classical
  unfold stablePolytope
  rw [LinearMap.image_convexHull]
  congr 1
  ext y
  simp only [stableVectors, mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s', hs', rfl⟩
    refine ⟨incidenceVector (s'.map e.symm.toEmbedding), ⟨_, ?_, rfl⟩, ?_⟩
    · intro u hu v hv huv hadj
      simp only [Finset.coe_map, Equiv.coe_toEmbedding, mem_image, Finset.mem_coe] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      refine hs' hu' hv' (fun h => huv (by rw [h])) ?_
      simpa using hadj
    · funext w
      simp only [re_apply, incidenceVector, Finset.mem_map_equiv, Equiv.symm_symm,
        Equiv.apply_symm_apply]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s.map e.toEmbedding, ?_, ?_⟩
    · intro u hu v hv huv hadj
      simp only [Finset.coe_map, Equiv.coe_toEmbedding, mem_image, Finset.mem_coe] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      refine hs hu' hv' (fun h => huv (by rw [h])) ?_
      simpa using hadj
    · funext w
      simp only [re_apply, incidenceVector, Finset.mem_map_equiv]

lemma isPolytope_stablePolytope (G : SimpleGraph V) : IsPolytope (stablePolytope G) := by
  classical
  refine isPolytope_of_finite (Set.Finite.subset
    (Set.finite_range (fun s : Finset V => incidenceVector s)) ?_)
  rintro _ ⟨s, -, rfl⟩
  exact mem_range_self s

end StabTransport

lemma card_SV (p k : ℕ) : Fintype.card (SV p k) = 2 * p + 4 * Fintype.card (Pair p) + k := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

lemma card_Pair_le (p : ℕ) : Fintype.card (Pair p) ≤ p ^ 2 := by
  calc Fintype.card (Pair p) ≤ Fintype.card (Fin p × Fin p) := Fintype.card_subtype_le _
    _ = p ^ 2 := by simp [sq]

/-- Core of Lemma 8 / Theorem 10: a graph on `Fin m` (`m = |V(H_p)| + k`) whose stable set polytope
has a face that is an extension of `COR(p)`. -/
lemma stab_face_fin (p k : ℕ) (hp : 1 ≤ p) {m : ℕ} (hm : Fintype.card (SV p k) = m) :
    ∃ H : SimpleGraph (Fin m), ∃ F : Set (Fin m → ℝ),
      IsFace (stablePolytope H) F ∧ IsExtension F (corPolytope p) := by
  classical
  let e : SV p k ≃ Fin m := Fintype.equivFinOfCardEq hm
  obtain ⟨F, hF, hext⟩ := stab_face (k := k) hp
  refine ⟨(SG p k).comap e.symm, re e '' F, ?_, isExtension_re e hext⟩
  rw [stablePolytope_comap]
  exact isFace_re e hF

/-- **Lemma 8**. -/
theorem stab_face_extends_cor :
    ∃ c : ℕ, ∀ n : ℕ, ∃ m : ℕ, m ≤ c * n ^ 2 ∧ ∃ H : SimpleGraph (Fin m),
      ∃ F : Set (Fin m → ℝ), IsFace (ChvatalPolytopes.Shared.stablePolytope H) F ∧
        IsExtension F (corPolytope n) := by
  classical
  refine ⟨6, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: everything is a point
    refine ⟨0, le_rfl, ⊥, stablePolytope ⊥, Or.inl rfl, isPolytope_stablePolytope _, 0, ?_⟩
    have hne : (stablePolytope (⊥ : SimpleGraph (Fin 0))).Nonempty :=
      ⟨incidenceVector ∅, subset_convexHull ℝ _ ⟨∅, by simp, rfl⟩⟩
    have hcor : (corPolytope 0).Nonempty :=
      ⟨outerBits (fun _ => false), subset_convexHull ℝ _ (mem_range_self _)⟩
    ext y
    constructor
    · rintro -
      obtain ⟨z, hz⟩ := hcor
      have : y = z := Subsingleton.elim _ _
      rw [this]; exact hz
    · intro _
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, Subsingleton.elim _ _⟩
  · obtain ⟨H, F, hF, hext⟩ := stab_face_fin n 0 hn rfl
    refine ⟨_, ?_, H, F, hF, hext⟩
    rw [card_SV]
    have := card_Pair_le n
    have : n ≤ n ^ 2 := by nlinarith
    nlinarith

lemma xc_stab_ge_cor {m p : ℕ} (H : SimpleGraph (Fin m)) (F : Set (Fin m → ℝ))
    (hF : IsFace (stablePolytope H) F) (hext : IsExtension F (corPolytope p)) :
    extensionComplexity (corPolytope p) ≤ extensionComplexity (stablePolytope H) :=
  (xc_extension_mono _ F hext.1 hext).trans
    (xc_face_le (exists_EF_of_isPolytope (isPolytope_stablePolytope H)) hF)

/-- **Theorem 10**. -/
theorem xc_stab_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n),
      (2 : ℝ) ^ (C * Real.sqrt n) ≤
        (extensionComplexity (ChvatalPolytopes.Shared.stablePolytope G) : ℝ) := by
  classical
  refine ⟨Real.logb 2 (3 / 2) / 5, by linarith [logb_pos'], 6, fun n hn => ?_⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = Nat.sqrt (n / 6) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef, Nat.le_sqrt]
    omega
  have hsq1 := Nat.sqrt_le' (n / 6)
  have hsq2 := Nat.lt_succ_sqrt' (n / 6)
  rw [← hpdef] at hsq1 hsq2
  have hp2 : 6 * p ^ 2 ≤ n := by omega
  have hp3 : n < 6 * (p + 1) ^ 2 := by
    have h6 : n < 6 * (n / 6) + 6 := by omega
    have : n / 6 + 1 ≤ (p + 1) ^ 2 := hsq2
    nlinarith
  set f := 2 * p + 4 * Fintype.card (Pair p)
  have hf : f ≤ n := by
    have := card_Pair_le p
    have : p ≤ p ^ 2 := by nlinarith
    simp only [f]
    nlinarith
  obtain ⟨H, F, hF, hext⟩ := stab_face_fin p (n - f) hp1 (m := n) (by rw [card_SV]; omega)
  refine ⟨H, ?_⟩
  have hxc := xc_stab_ge_cor H F hF hext
  calc (2 : ℝ) ^ (Real.logb 2 (3 / 2) / 5 * Real.sqrt n)
      ≤ (2 : ℝ) ^ (Real.logb 2 (3 / 2) * p) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hC := logb_pos'
        have hsq : Real.sqrt n ≤ 5 * p := by
          rw [Real.sqrt_le_left (by positivity)]
          have : (n : ℝ) < 6 * (p + 1) ^ 2 := by exact_mod_cast hp3
          have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
          nlinarith
        nlinarith
    _ = (3 / 2 : ℝ) ^ p := two_rpow_logb p
    _ ≤ extensionComplexity (corPolytope p) := xc_cor_ge hp1
    _ ≤ _ := by exact_mod_cast hxc

end XCT

open Matrix ExtensionComplexity.TSP

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n),
      (2 : ℝ) ^ (C * Real.sqrt n) ≤
        (extensionComplexity (ChvatalPolytopes.Shared.stablePolytope G) : ℝ) :=
  XCT.xc_stab_lower_bound
