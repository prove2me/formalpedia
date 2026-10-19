-- Prove2me | solution 1 for ClassNumberFormula.quarter_circle_lattice_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:40:36.316733+00:00
-- url     : https://prove2.me/submissions/4fe7c2d8-0fdd-4c65-98e9-ca4da24f4516

import Mathlib

open Filter Topology Real MeasureTheory

namespace CNQC

lemma int_unit : ∫ u in (0 : ℝ)..1, √(1 - u ^ 2) = π / 4 := by
  have h := integral_sqrt_one_sub_sq
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)] at h
  · have hneg : ∫ u in (-1 : ℝ)..0, √(1 - u ^ 2) = ∫ u in (0 : ℝ)..1, √(1 - u ^ 2) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun u => √(1 - u ^ 2))
      simp only [neg_sq, neg_zero] at this
      exact this.symm
    rw [hneg] at h; linarith
  · exact (continuous_sqrt.comp (by fun_prop)).intervalIntegrable _ _
  · exact (continuous_sqrt.comp (by fun_prop)).intervalIntegrable _ _

lemma int_sqrtN (N : ℝ) (hN : 0 ≤ N) : ∫ t in (0 : ℝ)..√N, √(N - t ^ 2) = π / 4 * N := by
  rcases hN.lt_or_eq with hN | rfl
  · have hs : 0 < √N := Real.sqrt_pos.mpr hN
    have e : ∀ u : ℝ, √(N - (√N * u) ^ 2) = √N * √(1 - u ^ 2) := by
      intro u
      rw [mul_pow, Real.sq_sqrt hN.le, ← Real.sqrt_mul hN.le]; ring_nf
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun t => √(N - t ^ 2)) hs.ne'
    simp only [mul_zero, mul_one] at this
    have h1 : ∫ x in (0 : ℝ)..1, √(N - (√N * x) ^ 2) = √N * (π / 4) := by
      rw [intervalIntegral.integral_congr (g := fun u => √N * √(1 - u ^ 2)) (fun u _ => e u),
        intervalIntegral.integral_const_mul, int_unit]
    rw [this, smul_eq_mul] at h1
    have h2 : √N * √N = N := Real.mul_self_sqrt hN.le
    have h3 := congrArg (fun z => √N * z) h1
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h3
    rw [h3, ← mul_assoc, h2]; ring
  · simp

noncomputable def f (N : ℝ) (t : ℝ) : ℝ := √(N - t ^ 2)

lemma f_cont (N : ℝ) : Continuous (f N) :=
  Real.continuous_sqrt.comp (by fun_prop : Continuous fun t : ℝ => N - t ^ 2)

lemma f_anti (N : ℝ) : AntitoneOn (f N) (Set.Ici 0) := by
  intro a ha b hb hab
  apply Real.sqrt_le_sqrt
  have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  linarith

lemma f_zero (N t : ℝ) (h : N ≤ t ^ 2) : f N t = 0 := Real.sqrt_eq_zero'.mpr (by linarith)

lemma int_f (N b : ℝ) (hN : 0 ≤ N) (hb : √N ≤ b) : ∫ t in (0 : ℝ)..b, f N t = π / 4 * N := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := √N)]
  · rw [show (∫ t in (0 : ℝ)..√N, f N t) = π / 4 * N from int_sqrtN N hN]
    have : ∫ t in √N..b, f N t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le hb] at ht
        apply f_zero
        have h1 : √N ≤ t := ht.1
        have h2 : (√N) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
        rwa [Real.sq_sqrt hN] at h2
    rw [this, add_zero]
  · exact (continuous_sqrt.comp (by fun_prop)).intervalIntegrable _ _
  · exact (continuous_sqrt.comp (by fun_prop)).intervalIntegrable _ _

/-- sum bounds for natural `N ≥ 1` -/
lemma sum_upper (N : ℕ) : ∑ i ∈ Finset.range N, f N ((i + 1 : ℕ) : ℝ) ≤ π / 4 * N := by
  have h := AntitoneOn.sum_le_integral (x₀ := 0) (a := N) (f := f N)
    ((f_anti N).mono (by intro x hx; exact hx.1))
  simp only [zero_add] at h
  calc _ ≤ ∫ x in (0 : ℝ)..N, f N x := by simpa using h
    _ = π / 4 * N := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        · apply int_f N N (Nat.cast_nonneg _)
          rw [Real.sqrt_le_left (by positivity)]
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith

lemma sum_lower (N : ℕ) (hN : 1 ≤ N) :
    π / 4 * N - √N ≤ ∑ i ∈ Finset.range N, f N ((i + 1 : ℕ) : ℝ) := by
  have h := AntitoneOn.integral_le_sum (x₀ := 1) (a := N) (f := f N)
    ((f_anti N).mono (by intro x hx; exact le_trans zero_le_one hx.1))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hint : ∫ x in (1 : ℝ)..1 + N, f N x = π / 4 * N - ∫ x in (0 : ℝ)..1, f N x := by
    have := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 1) (c := 1 + (N : ℝ))
      (μ := volume) (f := f N) ((f_cont _).intervalIntegrable _ _) ((f_cont _).intervalIntegrable _ _)
    rw [int_f N (1 + N) (Nat.cast_nonneg _) (by rw [Real.sqrt_le_left (by positivity)]; nlinarith)]
      at this
    linarith
  have hsmall : ∫ x in (0 : ℝ)..1, f N x ≤ √N := by
    have := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 1) (f := f N) zero_le_one
      ((f_cont _).intervalIntegrable _ _) (intervalIntegrable_const)
      (g := fun _ => √(N : ℝ)) (fun x hx => by unfold f; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x]))
    simpa using this
  have e : ∀ i : ℕ, f N (1 + i) = f N ((i + 1 : ℕ) : ℝ) := by intro i; push_cast; ring_nf
  simp only [e] at h
  linarith

/-- inner count -/
def c (N x : ℕ) : ℕ := ((Finset.range (N + 1)).filter (fun y => x ^ 2 + y ^ 2 ≤ N)).card

lemma c_bounds (N x : ℕ) :
    f N x ≤ c N x ∧ (c N x : ℝ) ≤ f N x + (if x ^ 2 ≤ N then 1 else 0) := by
  by_cases hx : x ^ 2 ≤ N
  · rw [if_pos hx]
    set s := √((N : ℝ) - (x : ℝ) ^ 2) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hNx : (0 : ℝ) ≤ N - (x : ℝ) ^ 2 := by
      have : ((x ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hx
      push_cast at this; linarith
    have hset : (Finset.range (N + 1)).filter (fun y => x ^ 2 + y ^ 2 ≤ N) =
        Finset.range (⌊s⌋₊ + 1) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      rw [Nat.le_floor_iff hs0, hs, Real.le_sqrt (Nat.cast_nonneg _) hNx]
      constructor
      · rintro ⟨_, h⟩
        have : ((x ^ 2 + y ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast h
        push_cast at this; linarith
      · intro h
        have h2 : ((x ^ 2 + y ^ 2 : ℕ) : ℝ) ≤ N := by push_cast; linarith
        have h3 : x ^ 2 + y ^ 2 ≤ N := by exact_mod_cast h2
        refine ⟨?_, h3⟩
        nlinarith
    have hc : (c N x : ℝ) = ⌊s⌋₊ + 1 := by
      unfold c; rw [hset, Finset.card_range]; push_cast; ring
    have hf : f N x = s := rfl
    rw [hc, hf]
    exact ⟨(Nat.lt_floor_add_one s).le, by linarith [Nat.floor_le hs0]⟩
  · rw [if_neg hx]
    have hempty : (Finset.range (N + 1)).filter (fun y => x ^ 2 + y ^ 2 ≤ N) = ∅ := by
      ext y; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ h; exact hx (le_trans (Nat.le_add_right _ _) h)
    have hc : c N x = 0 := by unfold c; rw [hempty, Finset.card_empty]
    have hf : f N x = 0 := by
      apply f_zero
      have : N < x ^ 2 := not_le.mp hx
      exact_mod_cast this.le
    rw [hc, hf]; simp

lemma count_eq (N : ℕ) :
    Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} =
      ∑ i ∈ Finset.range N, c N (i + 1) := by
  have e1 : {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} ≃
      {q : ℕ × ℕ // q ∈ ((Finset.Icc 1 N) ×ˢ (Finset.range (N + 1))).filter
        (fun q => q.1 ^ 2 + q.2 ^ 2 ≤ N)} := {
    toFun := fun p => ⟨(p.1.1.toNat, p.1.2.toNat), by
      obtain ⟨⟨a, b⟩, ha, hb, hab⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
      have hb' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb
      have key : a.toNat ^ 2 + b.toNat ^ 2 ≤ N := by
        have : ((a.toNat ^ 2 + b.toNat ^ 2 : ℕ) : ℤ) ≤ N := by push_cast; rw [ha', hb']; exact hab
        exact_mod_cast this
      have h1 : 1 ≤ a.toNat := by omega
      refine ⟨⟨⟨h1, ?_⟩, ?_⟩, key⟩ <;> nlinarith⟩
    invFun := fun q => ⟨((q.1.1 : ℤ), (q.1.2 : ℤ)), by
      have hq := q.2
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hq
      dsimp only
      refine ⟨by exact_mod_cast hq.1.1.1, by positivity, by exact_mod_cast hq.2⟩⟩
    left_inv := fun p => by
      obtain ⟨⟨a, b⟩, ha, hb, hab⟩ := p
      ext <;> simp [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hb]
    right_inv := fun q => by ext <;> simp }
  rw [Nat.card_congr e1, Nat.card_eq_finsetCard, Finset.card_filter, Finset.sum_product]
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) from rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  unfold c
  rw [Finset.card_filter, add_comm 1 i]

lemma sum_ind (N : ℕ) :
    (∑ i ∈ Finset.range N, (if (i + 1) ^ 2 ≤ N then (1 : ℝ) else 0)) ≤ √N := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.range N).filter (fun i => (i + 1) ^ 2 ≤ N) ⊆ Finset.range (Nat.sqrt N) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    have := Nat.le_sqrt'.mpr hi.2
    omega
  calc (((Finset.range N).filter (fun i => (i + 1) ^ 2 ≤ N)).card : ℝ)
      ≤ (Finset.range (Nat.sqrt N)).card := by exact_mod_cast Finset.card_le_card hsub
    _ = Nat.sqrt N := by rw [Finset.card_range]
    _ ≤ √N := Real.nat_sqrt_le_real_sqrt

theorem main :
    Tendsto (fun N : ℕ =>
        (Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} : ℝ) / N)
      atTop (𝓝 (π / 4)) := by
  have hlow : ∀ N : ℕ, 1 ≤ N → π / 4 - (√N)⁻¹ ≤
      (Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} : ℝ) / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [count_eq, Nat.cast_sum, le_div_iff₀ hN']
    have h1 := sum_lower N hN
    have h2 : ∑ i ∈ Finset.range N, f N ((i + 1 : ℕ) : ℝ) ≤ ∑ i ∈ Finset.range N, (c N (i + 1) : ℝ) :=
      Finset.sum_le_sum fun i _ => (c_bounds N (i + 1)).1
    have h3 : (√(N : ℝ))⁻¹ * N = √N := by
      have hsN : √(N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN').ne'
      calc (√(N : ℝ))⁻¹ * N = (√(N : ℝ))⁻¹ * (√N * √N) := by rw [Real.mul_self_sqrt hN'.le]
        _ = √N := by field_simp
    nlinarith
  have hup : ∀ N : ℕ, 1 ≤ N →
      (Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} : ℝ) / N ≤
        π / 4 + (√N)⁻¹ := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [count_eq, Nat.cast_sum, div_le_iff₀ hN']
    have h1 := sum_upper N
    have h2 : ∑ i ∈ Finset.range N, (c N (i + 1) : ℝ) ≤
        ∑ i ∈ Finset.range N, (f N ((i + 1 : ℕ) : ℝ) + (if (i + 1) ^ 2 ≤ N then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => (c_bounds N (i + 1)).2
    rw [Finset.sum_add_distrib] at h2
    have h4 := sum_ind N
    have h3 : (√(N : ℝ))⁻¹ * N = √N := by
      have hsN : √(N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN').ne'
      calc (√(N : ℝ))⁻¹ * N = (√(N : ℝ))⁻¹ * (√N * √N) := by rw [Real.mul_self_sqrt hN'.le]
        _ = √N := by field_simp
    nlinarith
  have hinv : Tendsto (fun N : ℕ => (√(N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ => π / 4 - (√(N : ℝ))⁻¹) atTop (𝓝 (π / 4)) := by
    simpa using (tendsto_const_nhds (x := π / 4)).sub hinv
  have hu : Tendsto (fun N : ℕ => π / 4 + (√(N : ℝ))⁻¹) atTop (𝓝 (π / 4)) := by
    simpa using (tendsto_const_nhds (x := π / 4)).add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using hlow N hN
  · filter_upwards [eventually_ge_atTop 1] with N hN using hup N hN

end CNQC

theorem solution :
    Tendsto (fun N : ℕ =>
        (Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ N} : ℝ) / N)
      atTop (𝓝 (π / 4)) :=
  CNQC.main
