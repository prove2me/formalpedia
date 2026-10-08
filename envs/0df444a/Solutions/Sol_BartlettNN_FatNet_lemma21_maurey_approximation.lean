-- Prove2me | solution 1 for BartlettNN.FatNet.lemma21_maurey_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:11:15.050983+00:00
-- url     : https://prove2.me/submissions/8fb39054-0a5c-4f82-ab7c-c64e25c08d43

import Mathlib

set_option autoImplicit false

theorem m04a_exists_ge_inner {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (F : Set G) (u h' : G) (hh' : h' ∈ convexHull ℝ F) :
    ∃ g ∈ F, inner ℝ u h' ≤ inner ℝ u g := by
  have hc : ConvexOn ℝ Set.univ (fun x : G => inner ℝ u x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp [inner_add_right, inner_smul_right]
  exact hc.exists_ge_of_mem_convexHull (Set.subset_univ _) hh'

theorem m04a_step {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (b : ℝ) (v h' g : G) (hg : ‖g‖ ^ 2 ≤ b ^ 2)
    (hi : inner ℝ (v + h') h' ≤ inner ℝ (v + h') g) :
    ‖v + (h' - g)‖ ^ 2 ≤ ‖v‖ ^ 2 + (b ^ 2 - ‖h'‖ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq] at hg ⊢
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right] at hi ⊢
  rw [real_inner_comm h' v, real_inner_comm g v, real_inner_comm g h'] at *
  linarith

theorem m04a_hull_approx {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (F : Set G) (b : ℝ) (hb : ∀ f ∈ F, ‖f‖ ≤ b) (h' : G) (hh' : h' ∈ convexHull ℝ F) :
    ∀ k : ℕ, ∃ f : Fin k → G, (∀ i, f i ∈ F) ∧
      ‖(k : ℝ) • h' - ∑ i, f i‖ ^ 2 ≤ k * (b ^ 2 - ‖h'‖ ^ 2) := by
  intro k
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  | succ k ih =>
    obtain ⟨f, hfF, hf⟩ := ih
    set v : G := (k : ℝ) • h' - ∑ i, f i with hv
    obtain ⟨g, hgF, hgi⟩ := m04a_exists_ge_inner F (v + h') h' hh'
    have hg2 : ‖g‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb g hgF) 2
    refine ⟨Fin.snoc f g, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hgF
      · simpa using hfF j
    · have hsum : ∑ i, (Fin.snoc f g : Fin (k + 1) → G) i = ∑ i, f i + g := by
        rw [Fin.sum_univ_castSucc]
        simp
      have heq : ((k + 1 : ℕ) : ℝ) • h' - ∑ i, (Fin.snoc f g : Fin (k + 1) → G) i
          = v + (h' - g) := by
        rw [hsum, hv]
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [heq]
      have := m04a_step b v h' g hg2 hgi
      push_cast
      nlinarith

theorem solution {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (F : Set G) (b : ℝ) (hb : ∀ f ∈ F, ‖f‖ ≤ b)
    (h : G) (hh : h ∈ closure (convexHull ℝ F)) :
    ∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, b ^ 2 - ‖h‖ ^ 2 < c →
      ∃ f : Fin k → G, (∀ i, f i ∈ F) ∧ ‖h - (k : ℝ)⁻¹ • ∑ i, f i‖ ^ 2 ≤ c / k := by
  intro k hk c hc
  -- F nonempty, b ≥ 0, ‖h‖ ≤ b
  have hFne : F.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne] at hh
  obtain ⟨f0, hf0⟩ := hFne
  have hb0 : 0 ≤ b := le_trans (norm_nonneg _) (hb f0 hf0)
  have hball : closure (convexHull ℝ F) ⊆ Metric.closedBall (0 : G) b := by
    apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall _ _)
    intro f hf
    simpa using hb f hf
  have hhb : ‖h‖ ≤ b := by simpa using hball hh
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hnn : 0 ≤ (b ^ 2 - ‖h‖ ^ 2) / k := by
    apply div_nonneg _ hkpos.le
    nlinarith [norm_nonneg h]
  set φ : G → ℝ := fun x => (‖h - x‖ + Real.sqrt ((b ^ 2 - ‖x‖ ^ 2) / k)) ^ 2 with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hφh : φ h < c / k := by
    simp only [hφ, sub_self, norm_zero, zero_add]
    rw [Real.sq_sqrt hnn]
    exact div_lt_div_of_pos_right hc hkpos
  have hopen : IsOpen (φ ⁻¹' Set.Iio (c / k)) := isOpen_Iio.preimage hφc
  obtain ⟨h', hh'U, hh'H⟩ := mem_closure_iff.mp hh _ hopen hφh
  obtain ⟨f, hfF, hf⟩ := m04a_hull_approx F b hb h' hh'H k
  refine ⟨f, hfF, ?_⟩
  have hU : φ h' < c / k := hh'U
  -- ‖h' - k⁻¹ S‖^2 ≤ (b^2 - ‖h'‖^2)/k
  have h1 : h' - (k : ℝ)⁻¹ • ∑ i, f i = (k : ℝ)⁻¹ • ((k : ℝ) • h' - ∑ i, f i) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hkpos.ne', one_smul]
  have h2 : ‖h' - (k : ℝ)⁻¹ • ∑ i, f i‖ ^ 2 ≤ (b ^ 2 - ‖h'‖ ^ 2) / k := by
    rw [h1, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hkpos]
    rw [div_eq_inv_mul]
    have : ((k : ℝ)⁻¹) ^ 2 * ((k : ℝ) * (b ^ 2 - ‖h'‖ ^ 2)) = (k : ℝ)⁻¹ * (b ^ 2 - ‖h'‖ ^ 2) := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 : ‖h' - (k : ℝ)⁻¹ • ∑ i, f i‖ ≤ Real.sqrt ((b ^ 2 - ‖h'‖ ^ 2) / k) := by
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have h4 : ‖h - (k : ℝ)⁻¹ • ∑ i, f i‖ ≤ ‖h - h'‖ + Real.sqrt ((b ^ 2 - ‖h'‖ ^ 2) / k) := by
    calc ‖h - (k : ℝ)⁻¹ • ∑ i, f i‖
        = ‖(h - h') + (h' - (k : ℝ)⁻¹ • ∑ i, f i)‖ := by congr 1; abel
      _ ≤ ‖h - h'‖ + ‖h' - (k : ℝ)⁻¹ • ∑ i, f i‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h5 : ‖h - (k : ℝ)⁻¹ • ∑ i, f i‖ ^ 2 ≤ φ h' := by
    simp only [hφ]
    exact pow_le_pow_left₀ (norm_nonneg _) h4 2
  linarith
