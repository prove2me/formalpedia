-- Prove2me | solution 1 for AxialPathObstruction.bounded_forward_fixed_covariance_unbounded_mixed
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:23:12.083513+00:00
-- url     : https://prove2.me/submissions/ae5a0ddb-995d-4d80-a42c-b919c9ef8f37

import Definitions.Def_DerivativeChainAxialPath_20261028


set_option autoImplicit false

/-! An exact geometric countermodel, not a derivative-root tower. -/
namespace AxialPathObstruction






























theorem differences_zig (h a : ℝ) (k : ℕ) :
    differences ((h : ℂ) :: zigVertices h a k) = zigEdges a k := by
  induction k with
  | zero => simp [zigVertices, zigEdges, differences]
  | succ k ih =>
    simp only [zigVertices, differences, zigEdges]
    rw [ih]
    congr 1
    · ring
    · congr 1
      ring

theorem differences_vertices (h a : ℝ) (k : ℕ) :
    differences (vertices h a k) = edges h a k := by
  simp only [vertices, differences, sub_zero, differences_zig, edges]

theorem sum_zig (a : ℝ) (k : ℕ) : (zigEdges a k).sum = 0 := by
  induction k with
  | zero => simp [zigEdges]
  | succ k ih => simp [zigEdges, ih]

theorem sum_edges (h a : ℝ) (k : ℕ) : (edges h a k).sum = (h : ℂ) := by
  simp [edges, sum_zig]



theorem map_sum_zig (a : ℝ) (k : ℕ) (f : ℂ → ℝ) :
    ((zigEdges a k).map f).sum = (k : ℝ)*(f ((a : ℂ)*Complex.I)+f (-((a : ℂ)*Complex.I))) := by
  induction k with
  | zero => simp [zigEdges]
  | succ k ih =>
    simp only [zigEdges, List.map_cons, List.sum_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem zig_re_zero (a : ℝ) (k : ℕ) (v : ℂ) (hv : v ∈ zigEdges a k) : v.re=0 := by
  induction k with
  | zero => simp [zigEdges] at hv
  | succ k ih =>
    simp only [zigEdges, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · simp
    · simp
    · exact ih hv

theorem zig_norm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (v : ℂ)
    (hv : v ∈ zigEdges a k) : ‖v‖=a := by
  induction k with
  | zero => simp [zigEdges] at hv
  | succ k ih =>
    simp only [zigEdges, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · simp [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    · simp [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    · exact ih hv

theorem edges_forward (h a : ℝ) (k : ℕ) (hh : 0 ≤ h) :
    ∀ v ∈ edges h a k, 0 ≤ v.re := by
  intro v hv
  simp only [edges, List.mem_cons] at hv
  rcases hv with rfl | hv
  · simpa using hh
  · rw [zig_re_zero a k v hv]

theorem vertex_types (h a : ℝ) (k : ℕ) (z : ℂ) (hz : z ∈ vertices h a k) :
    z=0 ∨ z=(h : ℂ) ∨ z=(h : ℂ)+(a : ℂ)*Complex.I := by
  have hi : ∀ k : ℕ, z ∈ zigVertices h a k →
      z=(h : ℂ) ∨ z=(h : ℂ)+(a : ℂ)*Complex.I := by
    intro k
    induction k with
    | zero => simp [zigVertices]
    | succ k ih =>
      intro hz
      simp only [zigVertices, List.mem_cons] at hz
      rcases hz with hz | hz | hz
      · exact Or.inr hz
      · exact Or.inl hz
      · exact ih hz
  simp only [vertices, List.mem_cons] at hz
  rcases hz with hz | hz | hz
  · exact Or.inl hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (hi k hz)

theorem vertex_normSq (h a : ℝ) (k : ℕ) (z : ℂ) (hz : z ∈ vertices h a k) :
    Complex.normSq z ≤ h^2+a^2 := by
  rcases vertex_types h a k z hz with rfl | rfl | rfl
  · simp only [map_zero]
    positivity
  · simp only [Complex.normSq_ofReal]
    nlinarith [sq_nonneg a]
  · rw [Complex.normSq_add_mul_I]

theorem moments (h a : ℝ) (k : ℕ) :
    sxx (edges h a k)=h^2 ∧ sxy (edges h a k)=0 ∧
      syy (edges h a k)=2*(k : ℝ)*a^2 := by
  simp [sxx, sxy, syy, edges, map_sum_zig]
  ring



theorem angular_vertical (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    angularCharge (h : ℂ) ((a : ℂ)*Complex.I)=h*a ∧
      angularCharge (h : ℂ) (-((a : ℂ)*Complex.I))=h*a := by
  simp only [angularCharge, wedge, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, mul_zero, sub_zero,
    mul_one, add_zero, neg_zero, norm_neg]
  simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_pos hh, abs_of_pos ha]
  constructor <;> field_simp

theorem mixed_formula (h a : ℝ) (k : ℕ) (hh : 0 < h) (ha : 0 < a) :
    mixedCharge h a k=2*(k : ℝ)*h*a := by
  rw [mixedCharge, map_sum_zig, (angular_vertical h a hh ha).1,
    (angular_vertical h a hh ha).2]
  ring








theorem amplitude_bounds (M : ℕ) (hM : 1 ≤ M) :
    0 < amplitude M ∧ amplitude M ≤ 1/4 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold amplitude
  constructor
  · positivity
  · apply (div_le_iff₀ (show (0 : ℝ)<4*M by linarith)).2
    linarith

theorem fixed_covariance (M : ℕ) (hM : 1 ≤ M) :
    sxx (edges (1/2) (amplitude M) (cycles M))=1/4 ∧
    sxy (edges (1/2) (amplitude M) (cycles M))=0 ∧
    syy (edges (1/2) (amplitude M) (cycles M))=1/4 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rcases moments (1/2) (amplitude M) (cycles M) with ⟨hx, hxy, hy⟩
  refine ⟨?_, hxy, ?_⟩
  · norm_num at hx ⊢
    exact hx
  · rw [hy]
    simp only [cycles, amplitude, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring

theorem fixed_determinant (M : ℕ) (hM : 1 ≤ M) :
    covarianceDet (edges (1/2) (amplitude M) (cycles M))=1/16 := by
  rcases fixed_covariance M hM with ⟨hx,hxy,hy⟩
  norm_num [covarianceDet, hx, hxy, hy]



theorem mixed_charge_value (M : ℕ) (hM : 1 ≤ M) :
    mixedCharge (1/2) (amplitude M) (cycles M)=(M : ℝ)/2 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [mixed_formula _ _ _ (by norm_num) (amplitude_bounds M hM).1]
  simp only [cycles, amplitude, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring





theorem vertices_small_disk (M : ℕ) (hM : 1 ≤ M) :
    ∀ z ∈ vertices (1/2) (amplitude M) (cycles M), Complex.normSq z ≤ 5/16 := by
  intro z hz
  have hb := vertex_normSq (1/2) (amplitude M) (cycles M) z hz
  have ha := amplitude_bounds M hM
  nlinarith



theorem mixed_unbounded (C : ℝ) :
    ∃ M : ℕ, 1 ≤ M ∧ C < mixedCharge (1/2) (amplitude M) (cycles M) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2*C) 0)
  have hmpos : (0 : ℝ) < M := lt_of_le_of_lt (le_max_right _ _) hM
  have hmnat : 1 ≤ M := by exact_mod_cast hmpos
  refine ⟨M, hmnat, ?_⟩
  rw [mixed_charge_value M hmnat]
  have h2 := lt_of_le_of_lt (le_max_left (2*C) 0) hM
  linarith
















end AxialPathObstruction

open AxialPathObstruction in
/-- A complete finite geometric witness, with all constraints on its actual vertices and edges. -/
theorem solution (C : ℝ) :
    ∃ V : List ℂ,
      V.head?=some 0 ∧
      (differences V).head?=some (1/2 : ℂ) ∧
      (∀ z ∈ V, Complex.normSq z ≤ 5/16) ∧
      (∀ v ∈ differences V, 0 ≤ v.re) ∧
      (differences V).sum=(1/2 : ℂ) ∧
      sxx (differences V)=1/4 ∧ sxy (differences V)=0 ∧ syy (differences V)=1/4 ∧
      covarianceDet (differences V)=1/16 ∧
      (∀ v ∈ (differences V).tail, v≠0 ∧ dot (1/2 : ℂ) v=0) ∧
      C < firstAngularCharge (differences V) := by
  obtain ⟨M, hM, hC⟩ := mixed_unbounded C
  refine ⟨vertices (1/2) (amplitude M) (cycles M), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rw [differences_vertices]
    norm_num [edges]
  · exact vertices_small_disk M hM
  · rw [differences_vertices]
    exact edges_forward _ _ _ (by norm_num)
  · rw [differences_vertices, sum_edges]
    norm_num
  · rw [differences_vertices]
    exact (fixed_covariance M hM).1
  · rw [differences_vertices]
    exact (fixed_covariance M hM).2.1
  · rw [differences_vertices]
    exact (fixed_covariance M hM).2.2
  · rw [differences_vertices]
    exact fixed_determinant M hM
  · intro v hv
    rw [differences_vertices] at hv
    change v ∈ zigEdges (amplitude M) (cycles M) at hv
    constructor
    · intro hz
      have hn := zig_norm (amplitude M) (le_of_lt (amplitude_bounds M hM).1)
        (cycles M) v hv
      rw [hz, norm_zero] at hn
      linarith [(amplitude_bounds M hM).1]
    · have hr := zig_re_zero (amplitude M) (cycles M) v hv
      norm_num [dot, hr]
  · rw [differences_vertices]
    exact hC
