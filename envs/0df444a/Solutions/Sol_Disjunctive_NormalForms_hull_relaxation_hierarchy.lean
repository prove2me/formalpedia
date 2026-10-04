-- Prove2me | solution 1 for Disjunctive.NormalForms.hull_relaxation_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:30:41.621449+00:00
-- url     : https://prove2.me/submissions/aca10fd4-8ce0-43ad-80ad-6ed2cb48021f

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

open Disjunctive.NormalForms

lemma poly_convex_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (Poly A b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]

lemma poly_closed_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed (Poly A b) := by
  have : Poly A b = ⋂ i, {x : Fin n → ℝ | b i ≤ (A.mulVec x) i} := by
    ext x; simp [Disjunctive.NormalForms.Poly]
  rw [this]
  refine isClosed_iInter fun i => isClosed_le continuous_const ?_
  have : Continuous fun x : Fin n → ℝ => A.mulVec x := Continuous.matrix_mulVec continuous_const
    continuous_id
  exact (continuous_apply i).comp this

lemma pos_parallel_core {n : ℕ} (a b : Fin n → ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v, 0 < dotProduct a v → 0 ≤ dotProduct b v) :
    ∃ c : ℝ, 0 < c ∧ b = c • a := by
  have haa : 0 < dotProduct a a := by
    rcases (dotProduct_self_star_nonneg a).lt_or_eq with h' | h'
    · simpa using h'
    · exact absurd (dotProduct_self_eq_zero.mp (by simpa using h'.symm)) ha
  -- auxiliary: `0 ≤ X + t Y` for all `t > 0` implies `0 ≤ X`
  have aux : ∀ X Y : ℝ, (∀ t : ℝ, 0 < t → 0 ≤ X + t * Y) → 0 ≤ X := by
    intro X Y hXY
    by_contra hX
    push Not at hX
    rcases le_or_gt Y 0 with hY | hY
    · have := hXY 1 one_pos; linarith
    · have := hXY (-X / (2 * Y)) (div_pos (by linarith) (by linarith))
      have e : -X / (2 * Y) * Y = -X / 2 := by field_simp
      linarith
  have key : ∀ u, dotProduct a a * dotProduct b u = dotProduct a u * dotProduct b a := by
    intro u
    have hge : ∀ u, 0 ≤ dotProduct a a * dotProduct b u - dotProduct a u * dotProduct b a := by
      intro u
      apply aux _ (dotProduct b a)
      intro t ht
      have hv := h ((dotProduct a a) • u - (dotProduct a u) • a + t • a) (by
        simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        nlinarith [dotProduct_comm a u])
      simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hv
      linarith
    have h1 := hge u
    have h2 := hge (-u)
    simp only [dotProduct_neg] at h2
    linarith
  refine ⟨dotProduct b a / dotProduct a a, ?_, ?_⟩
  · have hba : 0 ≤ dotProduct b a := h a haa
    rcases hba.lt_or_eq with hlt | heq
    · exact div_pos hlt haa
    · exfalso
      apply hb
      ext i
      have := key (Pi.single i 1)
      rw [← heq] at this
      simp [dotProduct_single] at this
      rcases this with h0 | h0
      · exact absurd h0 ha
      · simpa using h0
  · ext i
    have := key (Pi.single i 1)
    simp only [dotProduct_single, mul_one] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith

lemma elementary_dichotomy_core {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsElementaryDisjunction S) :
    (∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), S = Poly A b) ∨
      convexHull ℝ S = Set.univ := by
  classical
  obtain ⟨Q, _, d, d0, rfl⟩ := hS
  by_cases ha : ∃ i, d i = 0 ∧ d0 i ≤ 0
  · left
    obtain ⟨i, hi, hi0⟩ := ha
    refine ⟨0, 0, 0, ?_⟩
    ext x
    simp only [Set.mem_iUnion, Disjunctive.NormalForms.Poly, Set.mem_setOf_eq]
    constructor
    · intro _ r; exact r.elim0
    · intro _; exact ⟨i, by simp [HalfspaceGE, hi, hi0]⟩
  by_cases hb : ∃ i k v, 0 < dotProduct (d i) v ∧ dotProduct (d k) v < 0
  · right
    obtain ⟨i, k, v, hi, hk⟩ := hb
    apply Set.eq_univ_of_forall
    intro z
    set t : ℝ := max 0 (max ((d0 i - dotProduct (d i) z) / dotProduct (d i) v)
      ((d0 k - dotProduct (d k) z) / (-dotProduct (d k) v))) with ht
    have ht1 : (d0 i - dotProduct (d i) z) / dotProduct (d i) v ≤ t :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have ht2 : (d0 k - dotProduct (d k) z) / (-dotProduct (d k) v) ≤ t :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rw [div_le_iff₀ hi] at ht1
    rw [div_le_iff₀ (by linarith)] at ht2
    have hp : z + t • v ∈ ⋃ i, HalfspaceGE (d i) (d0 i) := by
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [HalfspaceGE, Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    have hq : z - t • v ∈ ⋃ i, HalfspaceGE (d i) (d0 i) := by
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      simp only [HalfspaceGE, Set.mem_setOf_eq, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
    apply segment_subset_convexHull hp hq
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · left
    push Not at ha hb
    by_cases hN : ∃ i0, d i0 ≠ 0
    · obtain ⟨i0, hi0⟩ := hN
      have hpar : ∀ i, d i ≠ 0 → ∃ c : ℝ, 0 < c ∧ d i = c • d i0 := by
        intro i hi
        exact pos_parallel_core (d i0) (d i) hi0 hi (fun v hv => hb i0 i v hv)
      choose! c hc0 hc using hpar
      set N : Finset Q := Finset.univ.filter (fun i => d i ≠ 0) with hNdef
      have hNne : N.Nonempty := ⟨i0, by simp [hNdef, hi0]⟩
      set μ : ℝ := N.inf' hNne (fun i => d0 i / c i) with hμ
      refine ⟨1, Matrix.of fun _ j => d i0 j, fun _ => μ, ?_⟩
      ext x
      simp only [Set.mem_iUnion, HalfspaceGE, Set.mem_setOf_eq, Disjunctive.NormalForms.Poly]
      have hmv : ∀ r : Fin 1, ((Matrix.of fun (_ : Fin 1) j => d i0 j).mulVec x) r =
          dotProduct (d i0) x := by
        intro r; simp [Matrix.mulVec, dotProduct]
      simp only [hmv]
      constructor
      · rintro ⟨i, hi⟩ _
        have hdi : d i ≠ 0 := by
          intro h0
          rw [h0, zero_dotProduct] at hi
          linarith [ha i h0]
        have hiN : i ∈ N := by simp [hNdef, hdi]
        refine le_trans (Finset.inf'_le _ hiN) ?_
        rw [hc i hdi, smul_dotProduct, smul_eq_mul] at hi
        rw [div_le_iff₀ (hc0 i hdi)]
        linarith
      · intro hx
        obtain ⟨i, hiN, hieq⟩ := Finset.exists_mem_eq_inf' hNne (fun i => d0 i / c i)
        have hdi : d i ≠ 0 := by simpa [hNdef] using hiN
        refine ⟨i, ?_⟩
        have := hx 0
        rw [hμ, hieq, div_le_iff₀ (hc0 i hdi)] at this
        rw [hc i hdi, smul_dotProduct, smul_eq_mul]
        linarith
    · push Not at hN
      refine ⟨1, 0, fun _ => 1, ?_⟩
      ext x
      simp only [Set.mem_iUnion, HalfspaceGE, Set.mem_setOf_eq, Disjunctive.NormalForms.Poly]
      constructor
      · rintro ⟨i, hi⟩
        rw [hN i, zero_dotProduct] at hi
        linarith [ha i (hN i)]
      · intro h
        have := h 0
        simp at this
        linarith

theorem cnf_core {n : ℕ} {T : Type*} [Fintype T] (D : T → Set (Fin n → ℝ))
    (hCNF : ∀ j, IsElementaryDisjunction (D j)) :
    HRel D = P0Set D := by
  have hpoly : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      closure (convexHull ℝ (Poly A b)) = Poly A b := by
    intro m A b
    rw [(poly_convex_core A b).convexHull_eq, (poly_closed_core A b).closure_eq]
  ext x
  simp only [HRel, P0Set, Set.mem_iInter]
  constructor
  · intro h j hj
    obtain ⟨m, A, b, hD⟩ := hj
    have := h j
    rw [hD, hpoly] at this
    rw [hD]
    exact this
  · intro h j
    by_cases hj : j ∈ ImproperIndices D
    · obtain ⟨m, A, b, hD⟩ := hj
      have := h j ⟨m, A, b, hD⟩
      rw [hD, hpoly]
      rw [hD] at this
      exact this
    · rcases elementary_dichotomy_core (D j) (hCNF j) with hp | hu
      · exact absurd hp hj
      · rw [hu, closure_univ]
        exact Set.mem_univ x


theorem solution {n t : ℕ} (T : Fin (t + 1) → Type*) [∀ i, Fintype (T i)]
    (S : (i : Fin (t + 1)) → T i → Set (Fin n → ℝ)) (hCNF : ∀ j, IsElementaryDisjunction (S 0 j))
    (hDNF : Fintype.card (T (Fin.last t)) = 1)
    (hSteps : ∀ i : Fin t, IsBasicStepOf (S i.castSucc) (S i.succ)) :
    P0Set (S 0) = HRel (S 0) ∧
      (∀ i : Fin t, HRel (S i.succ) ⊆ HRel (S i.castSucc)) ∧
      HRel (S (Fin.last t)) = closure (convexHull ℝ (⋂ j, S (Fin.last t) j)) := by
  refine ⟨(cnf_core (S 0) hCNF).symm, ?_, ?_⟩
  · intro i x hx
    obtain ⟨k, l, hkl, e, hother, hmerge⟩ := hSteps i
    simp only [HRel, Set.mem_iInter] at hx ⊢
    intro j
    by_cases hjk : j = k
    · subst hjk
      have := hx (e.symm (Sum.inr ()))
      rw [hmerge] at this
      exact closure_mono (convexHull_mono Set.inter_subset_left) this
    by_cases hjl : j = l
    · subst hjl
      have := hx (e.symm (Sum.inr ()))
      rw [hmerge] at this
      exact closure_mono (convexHull_mono Set.inter_subset_right) this
    · have := hx (e.symm (Sum.inl ⟨j, hjk, hjl⟩))
      rwa [hother] at this
  · obtain ⟨j0, hj0⟩ := Fintype.card_eq_one_iff.mp hDNF
    have h1 : (⋂ j, S (Fin.last t) j) = S (Fin.last t) j0 := by
      ext x; simp only [Set.mem_iInter]
      exact ⟨fun h => h j0, fun h j => by rw [hj0 j]; exact h⟩
    rw [h1]
    ext x; simp only [HRel, Set.mem_iInter]
    exact ⟨fun h => h j0, fun h j => by rw [hj0 j]; exact h⟩

#print axioms solution
