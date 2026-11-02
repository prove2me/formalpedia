-- Prove2me | solution 1 for BilevelSOC.SecondOrder.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:30:36.881662+00:00
-- url     : https://prove2.me/submissions/c1ce0a11-11da-408c-8f3d-d46a7a6ffb3f

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology
open BilevelSOC.SecondOrder Filter Set

/-- Limit of a finite maximum: indices in `S` converge, the others diverge to `-∞`. -/
theorem bsoc_lmax {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℝ → ℝ) (l : Filter ℝ)
    (S : Finset ι) (hS : S.Nonempty) (a : ι → ℝ)
    (h1 : ∀ i ∈ S, Tendsto (q i) l (𝓝 (a i))) (h2 : ∀ i ∉ S, Tendsto (q i) l atBot) :
    Tendsto (fun t => Finset.univ.sup' Finset.univ_nonempty (fun i => q i t)) l
      (𝓝 (S.sup' hS a)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨i, hi, hia⟩ := Finset.exists_mem_eq_sup' hS a
    rw [hia] at hb
    filter_upwards [(tendsto_order.1 (h1 i hi)).1 b hb] with t ht
    exact lt_of_lt_of_le ht (Finset.le_sup' (fun i => q i t) (Finset.mem_univ i))
  · intro b hb
    have : ∀ i, ∀ᶠ t in l, q i t < b := by
      intro i
      by_cases hi : i ∈ S
      · exact (tendsto_order.1 (h1 i hi)).2 b
          (lt_of_le_of_lt (Finset.le_sup' a hi) hb)
      · exact (tendsto_atBot.1 (h2 i hi) (b - 1)).mono fun t ht => by linarith
    filter_upwards [Filter.eventually_all.2 this] with t ht
    exact (Finset.sup'_lt_iff _).2 fun i _ => ht i

theorem bsoc_sup'_sub_div {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (c s : ℝ)
    (hs : 0 < s) :
    (Finset.univ.sup' Finset.univ_nonempty f - c) / s =
      Finset.univ.sup' Finset.univ_nonempty (fun i => (f i - c) / s) := by
  apply le_antisymm
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    rw [hi]
    exact Finset.le_sup' (fun i => (f i - c) / s) (Finset.mem_univ i)
  · refine Finset.sup'_le _ _ fun i _ => ?_
    apply div_le_div_of_nonneg_right _ hs.le
    linarith [Finset.le_sup' f (Finset.mem_univ i)]

theorem bsoc_atBot_of_num {N : ℝ → ℝ} {c : ℝ} (hc : c < 0)
    (hN : Tendsto N (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun t => N t / t) (𝓝[>] (0 : ℝ)) atBot := by
  have := hN.neg_mul_atTop hc tendsto_inv_nhdsGT_zero
  simpa [div_eq_mul_inv] using this

theorem bsoc_atBot_of_num2 {N : ℝ → ℝ} {c : ℝ} (hc : c < 0)
    (hN : Tendsto N (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun t => N t / (t ^ 2 / 2)) (𝓝[>] (0 : ℝ)) atBot := by
  have h1 : Tendsto (fun t : ℝ => 2 * (t⁻¹) ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero).const_mul_atTop two_pos
  have := hN.neg_mul_atTop hc h1
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  field_simp

/-- Continuity along the curve from second-order directional differentiability. -/
theorem bsoc_cont_of_dir {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x d : V) (v : ℝ) (h : HasDirDerivAt θ x d v) :
    Tendsto (fun t : ℝ => θ (x + t • d)) (𝓝[>] (0 : ℝ)) (𝓝 (θ x)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have := (ht.mul h).add_const (θ x)
  rw [zero_mul, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
  field_simp
  ring

theorem bsoc_cont_of_dir2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x d w : V) (v v2 : ℝ)
    (h : Tendsto (fun t : ℝ => (θ (x + t • d + (t ^ 2 / 2) • w) - θ x - t * v) /
        (t ^ 2 / 2)) (𝓝[>] (0 : ℝ)) (𝓝 v2)) :
    Tendsto (fun t : ℝ => θ (x + t • d + (t ^ 2 / 2) • w)) (𝓝[>] (0 : ℝ)) (𝓝 (θ x)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun t : ℝ => t ^ 2 / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (ht.pow 2).div_const 2
    simpa using this
  have := ((ht2.mul h).add (ht.mul_const v)).add_const (θ x)
  rw [zero_mul, zero_mul, zero_add, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
  field_simp
  ring

theorem solution {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [Nonempty ι]
    (θ : ι → V → ℝ) (θ' : ι → V → ℝ) (θ'' : ι → V → V → ℝ)
    (x : V) (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : ∀ i, LipschitzOnWith L (θ i) U)
    (hDiff : ∀ i, SecondOrderDirDiff (θ i) x (θ' i) (θ'' i)) :
    ∃ (Θ' : V → ℝ) (Θ'' : V → V → ℝ),
      SecondOrderDirDiff (maxFn θ) x Θ' Θ'' ∧
      (∀ d, IsGreatest {v : ℝ | ∃ i, θ i x = maxFn θ x ∧ v = θ' i d} (Θ' d)) ∧
      (∀ d w, IsGreatest
        {v : ℝ | ∃ i, θ i x = maxFn θ x ∧ θ' i d = Θ' d ∧ v = θ'' i d w}
        (Θ'' d w)) := by
  classical
  set M := maxFn θ x with hM
  set A : Finset ι := Finset.univ.filter (fun i => θ i x = M) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => θ i x)
    exact ⟨i, by simp [A, M, maxFn, hi]⟩
  have hle : ∀ i, θ i x ≤ M := fun i =>
    Finset.le_sup' (fun i => θ i x) (Finset.mem_univ i)
  let Θ' : V → ℝ := fun d => A.sup' hAne (fun i => θ' i d)
  let Ad : V → Finset ι := fun d => A.filter (fun i => θ' i d = Θ' d)
  have hAdne : ∀ d, (Ad d).Nonempty := by
    intro d
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup' hAne (fun i => θ' i d)
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hie.symm⟩⟩
  let Θ'' : V → V → ℝ := fun d w => (Ad d).sup' (hAdne d) (fun i => θ'' i d w)
  have hmaxeq : ∀ y, maxFn θ y = Finset.univ.sup' Finset.univ_nonempty (fun i => θ i y) :=
    fun y => rfl
  refine ⟨Θ', Θ'', fun d => ⟨?_, fun w => ?_⟩, fun d => ⟨?_, ?_⟩, fun d w => ⟨?_, ?_⟩⟩
  · -- first-order
    unfold HasDirDerivAt
    have key := bsoc_lmax (fun i t => (θ i (x + t • d) - M) / t) (𝓝[>] (0 : ℝ)) A hAne
      (fun i => θ' i d) ?_ ?_
    · refine key.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [hmaxeq (x + t • d), bsoc_sup'_sub_div _ _ _ ht]
    · intro i hi
      have hiA : θ i x = M := (Finset.mem_filter.1 hi).2
      have := ((hDiff i) d).1
      unfold HasDirDerivAt at this
      rw [← hiA]; exact this
    · intro i hi
      have hlt : θ i x - M < 0 := by
        have : θ i x ≠ M := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        exact sub_neg.2 (lt_of_le_of_ne (hle i) this)
      exact bsoc_atBot_of_num hlt ((bsoc_cont_of_dir _ _ _ _ ((hDiff i) d).1).sub_const M)
  · -- second-order
    have key := bsoc_lmax
      (fun i t => (θ i (x + t • d + (t ^ 2 / 2) • w) - M - t * Θ' d) / (t ^ 2 / 2))
      (𝓝[>] (0 : ℝ)) (Ad d) (hAdne d) (fun i => θ'' i d w) ?_ ?_
    · refine key.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have ht2 : 0 < t ^ 2 / 2 := by positivity
      rw [hmaxeq (x + t • d + (t ^ 2 / 2) • w), sub_sub,
        bsoc_sup'_sub_div _ _ _ ht2]
      congr 1; funext i; rw [sub_sub]
    · intro i hi
      have hiA : θ i x = M := (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
      have hid : θ' i d = Θ' d := (Finset.mem_filter.1 hi).2
      have := ((hDiff i) d).2 w
      rw [← hiA, ← hid]; exact this
    · intro i hi
      have hconv := ((hDiff i) d).2 w
      by_cases hiA : i ∈ A
      · -- active at x but not at (x,d)
        have hiM : θ i x = M := (Finset.mem_filter.1 hiA).2
        have hlt : θ' i d - Θ' d < 0 := by
          have h1 : θ' i d ≤ Θ' d := Finset.le_sup' (fun i => θ' i d) hiA
          have h2 : θ' i d ≠ Θ' d := fun h => hi (Finset.mem_filter.2 ⟨hiA, h⟩)
          exact sub_neg.2 (lt_of_le_of_ne h1 h2)
        have h2t : Tendsto (fun t : ℝ => (θ' i d - Θ' d) * (2 * t⁻¹)) (𝓝[>] (0 : ℝ))
            atBot :=
          (tendsto_inv_nhdsGT_zero.const_mul_atTop two_pos).const_mul_atTop_of_neg hlt
        have := hconv.add_atBot h2t
        refine this.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        rw [← hiM]
        field_simp
        ring
      · have hlt : θ i x - M < 0 := by
          have : θ i x ≠ M := fun h => hiA (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          exact sub_neg.2 (lt_of_le_of_ne (hle i) this)
        have hc := bsoc_cont_of_dir2 _ _ _ _ _ _ hconv
        have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have hN := (hc.sub_const M).sub (ht.mul_const (Θ' d))
        rw [zero_mul, sub_zero] at hN
        exact bsoc_atBot_of_num2 hlt hN
  · -- membership for Θ'
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup' hAne (fun i => θ' i d)
    exact ⟨i, (Finset.mem_filter.1 hi).2, hie⟩
  · rintro v ⟨i, hi, rfl⟩
    exact Finset.le_sup' (fun i => θ' i d) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  · obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup' (hAdne d) (fun i => θ'' i d w)
    have h1 := Finset.mem_filter.1 hi
    exact ⟨i, (Finset.mem_filter.1 h1.1).2, h1.2, hie⟩
  · rintro v ⟨i, hi, hid, rfl⟩
    exact Finset.le_sup' (fun i => θ'' i d w)
      (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, hid⟩)
