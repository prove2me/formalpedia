-- Prove2me | solution 1 for ChvatalPolytopes.Perfect.convexHull_iff_minmax
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:46:13.376497+00:00
-- url     : https://prove2.me/submissions/af73b92d-b4e1-444a-9bd4-12966a57810b

import Mathlib



namespace ChvatalPolytopes.Perfect

open Finset

/-- Conic Carathéodory: a nonnegative combination can be rewritten as a nonnegative combination
with linearly independent support. -/
theorem caratheodory_cone_P {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E]
    [Module ℝ E] (v : ι → E) :
    ∀ (n : ℕ) (t : ι → ℝ), (univ.filter fun i => t i ≠ 0).card = n → (∀ i, 0 ≤ t i) →
    ∃ t' : ι → ℝ, (∀ i, 0 ≤ t' i) ∧ ∑ i, t' i • v i = ∑ i, t i • v i ∧
      LinearIndepOn ℝ v (↑(univ.filter fun i => t' i ≠ 0) : Set ι) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t hn ht
  by_cases hli : LinearIndepOn ℝ v (↑(univ.filter fun i => t i ≠ 0) : Set ι)
  · exact ⟨t, ht, rfl, hli⟩
  · rw [linearIndepOn_finset_iff] at hli
    push_neg at hli
    obtain ⟨g, hg0, i₁, hi₁, hgi₁⟩ := hli
    have hi₁' : t i₁ ≠ 0 := (Finset.mem_filter.1 hi₁).2
    -- a relation with some positive coefficient, supported in the support of t
    have key : ∃ g'' : ι → ℝ, ∑ i, g'' i • v i = 0 ∧ (∀ i, t i = 0 → g'' i = 0) ∧
        ∃ i, 0 < g'' i := by
      set g1 : ι → ℝ := fun i => if t i ≠ 0 then g i else 0 with hg1
      have hsum1 : ∑ i, g1 i • v i = 0 := by
        rw [← hg0, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hg1]
        split_ifs <;> simp
      have hsupp1 : ∀ i, t i = 0 → g1 i = 0 := by
        intro i hi; simp [hg1, hi]
      have hg1i₁ : g1 i₁ = g i₁ := by simp [hg1, hi₁']
      rcases lt_or_gt_of_ne hgi₁ with hneg | hpos
      · refine ⟨fun i => -g1 i, ?_, ?_, ⟨i₁, ?_⟩⟩
        · simp [neg_smul, Finset.sum_neg_distrib, hsum1]
        · intro i hi; simp [hsupp1 i hi]
        · simp only [hg1i₁]; linarith
      · exact ⟨g1, hsum1, hsupp1, ⟨i₁, by rw [hg1i₁]; exact hpos⟩⟩
    obtain ⟨g'', hsum, hsupp, hpos⟩ := key
    have hne : (univ.filter fun i => 0 < g'' i).Nonempty := by
      obtain ⟨i, hi⟩ := hpos
      exact ⟨i, by simp [hi]⟩
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ (fun i => t i / g'' i) hne
    have hgi₀ : 0 < g'' i₀ := (Finset.mem_filter.1 hi₀).2
    set θ : ℝ := t i₀ / g'' i₀ with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (ht i₀) hgi₀.le
    set t'' : ι → ℝ := fun i => t i - θ * g'' i with ht''
    have ht''0 : ∀ i, 0 ≤ t'' i := by
      intro i
      simp only [ht'']
      by_cases hgi : 0 < g'' i
      · have := hmin i (by simp [hgi])
        rw [hθ] at this ⊢
        rw [le_div_iff₀ hgi] at this
        linarith
      · push_neg at hgi
        have := ht i
        nlinarith
    have ht''i₀ : t'' i₀ = 0 := by
      simp only [ht'', hθ]
      rw [div_mul_cancel₀ _ hgi₀.ne', sub_self]
    have hti₀ : t i₀ ≠ 0 := by
      intro h
      have := hsupp i₀ h
      linarith
    have hsub : (univ.filter fun i => t'' i ≠ 0) ⊆ (univ.filter fun i => t i ≠ 0).erase i₀ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact hi ht''i₀
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        apply hi
        simp [ht'', hsupp i h, h]
    have hcard : (univ.filter fun i => t'' i ≠ 0).card < n := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simp [hti₀]), hn] at h1
      have : 1 ≤ n := by
        rw [← hn]
        exact Finset.card_pos.2 ⟨i₀, by simp [hti₀]⟩
      omega
    have hsum'' : ∑ i, t'' i • v i = ∑ i, t i • v i := by
      simp only [ht'', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hsum,
        smul_zero, sub_zero]
    obtain ⟨t', ht', hs', hli'⟩ := ih _ hcard t'' rfl ht''0
    exact ⟨t', ht', hs'.trans hsum'', hli'⟩

/-- A finitely generated cone in a finite-dimensional real normed space is closed. -/
theorem cone_isClosed_P {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : ι → E) :
    IsClosed {x : E | ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • v i} := by
  classical
  have hrepr : {x : E | ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • v i} =
      ⋃ s : {s : Finset ι // LinearIndepOn ℝ v (↑s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s.1 : Set ι) => v i)) ''
          {t : (s.1 : Set ι) → ℝ | ∀ i, 0 ≤ t i} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨t', ht', hsum, hli⟩ := caratheodory_cone_P v _ t rfl ht
      refine Set.mem_iUnion.2 ⟨⟨_, hli⟩, ?_⟩
      refine ⟨fun i => t' i, fun i => ht' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hsum]
      change ∑ i : (univ.filter fun i => t' i ≠ 0), t' i • v i = _
      rw [Finset.sum_coe_sort (univ.filter fun i => t' i ≠ 0) (fun i => t' i • v i)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hi]
    · intro hx
      obtain ⟨s, hx⟩ := Set.mem_iUnion.1 hx
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨fun i => if h : i ∈ s.1 then t ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs with h
        · exact ht ⟨i, h⟩
        · exact le_rfl
      · rw [Fintype.linearCombination_apply]
        dsimp only
        have h1 : ∑ i : s.1, t i • v i =
            ∑ i : s.1, (if h : (i : ι) ∈ s.1 then t ⟨i, h⟩ else 0) • v i := by
          apply Finset.sum_congr rfl; intro i _; simp [i.2]
        change ∑ i : s.1, t i • v i = _
        rw [h1, Finset.sum_coe_sort s.1 (fun i => (if h : i ∈ s.1 then t ⟨i, h⟩ else 0) • v i)]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp [hi]
  rw [hrepr]
  apply isClosed_iUnion_of_finite
  intro s
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s.1 : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    rw [Fintype.linearCombination_apply] at hg
    have := Fintype.linearIndependent_iff.1 s.2 g hg
    funext i
    exact this i
  have hemb := LinearMap.isClosedEmbedding_of_injective hinj
  apply hemb.isClosedMap
  have : {t : (s.1 : Set ι) → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t : (s.1 : Set ι) → ℝ | 0 ≤ t i} := by
    ext t; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

/-- Representation of a continuous linear functional on `W → ℝ` in the standard basis. -/
theorem dual_repr_P {W : Type*} [Fintype W] [DecidableEq W] (f : StrongDual ℝ (W → ℝ))
    (z : W → ℝ) : f z = ∑ w, z w * f (fun j => if w = j then 1 else 0) := by
  have := LinearMap.pi_apply_eq_sum_univ (f : (W → ℝ) →ₗ[ℝ] ℝ) z
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  exact this

/-- Generators of the homogenized cone of the system `x ≥ 0`, `A x ≤ b`. -/
def farkasGen {V J : Type*} [DecidableEq V] (a : J → V → ℝ) (b : J → ℝ) :
    J ⊕ V ⊕ Unit → (Option V → ℝ)
  | Sum.inl i => fun w => w.elim (b i) (a i)
  | Sum.inr (Sum.inl u) => fun w => w.elim 0 (fun u' => if u = u' then -1 else 0)
  | Sum.inr (Sum.inr _) => fun w => w.elim 1 (fun _ => 0)

theorem farkas_eval_some_P {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (t : J ⊕ V ⊕ Unit → ℝ) (u : V) :
    (∑ k, t k • farkasGen a b k) (some u) =
      ∑ i, t (Sum.inl i) * a i u - t (Sum.inr (Sum.inl u)) := by
  simp [Finset.sum_apply, Fintype.sum_sum_type, farkasGen, mul_ite]
  ring

theorem farkas_eval_none_P {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (t : J ⊕ V ⊕ Unit → ℝ) :
    (∑ k, t k • farkasGen a b k) none =
      ∑ i, t (Sum.inl i) * b i + t (Sum.inr (Sum.inr ())) := by
  simp [Finset.sum_apply, Fintype.sum_sum_type, farkasGen]

/-- Farkas-type lemma / LP duality for a bounded-above objective over `x ≥ 0`, `A x ≤ b`. -/
theorem farkas_P {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (x₀ : V → ℝ)
    (hx₀ : (∀ u, 0 ≤ x₀ u) ∧ ∀ i, ∑ u, a i u * x₀ u ≤ b i) (c : V → ℝ) (β : ℝ)
    (hbound : ∀ x : V → ℝ, (∀ u, 0 ≤ x u) → (∀ i, ∑ u, a i u * x u ≤ b i) →
      ∑ u, c u * x u ≤ β) :
    ∃ lam : J → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ u, c u ≤ ∑ i, lam i * a i u) ∧
      ∑ i, lam i * b i ≤ β := by
  classical
  set K : Set (Option V → ℝ) :=
    {z | ∃ t : J ⊕ V ⊕ Unit → ℝ, (∀ k, 0 ≤ t k) ∧ z = ∑ k, t k • farkasGen a b k} with hK
  set z₀ : Option V → ℝ := fun w => w.elim β c with hz₀def
  by_cases hz₀ : z₀ ∈ K
  · obtain ⟨t, ht, hz⟩ := hz₀
    refine ⟨fun i => t (Sum.inl i), fun i => ht _, ?_, ?_⟩
    · intro u
      have h1 := congrFun hz (some u)
      rw [farkas_eval_some_P] at h1
      have h2 : z₀ (some u) = c u := rfl
      have := ht (Sum.inr (Sum.inl u))
      linarith
    · have h1 := congrFun hz none
      rw [farkas_eval_none_P] at h1
      have h2 : z₀ none = β := rfl
      have := ht (Sum.inr (Sum.inr ()))
      linarith
  · exfalso
    have hKconv : Convex ℝ K := by
      rintro z1 ⟨t1, ht1, rfl⟩ z2 ⟨t2, ht2, rfl⟩ p q hp hq hpq
      refine ⟨fun k => p * t1 k + q * t2 k, fun k => add_nonneg (mul_nonneg hp (ht1 k))
        (mul_nonneg hq (ht2 k)), ?_⟩
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    have hKclosed : IsClosed K := cone_isClosed_P (farkasGen a b)
    obtain ⟨f, u₀, hfK, hfz₀⟩ := geometric_hahn_banach_closed_point hKconv hKclosed hz₀
    have h0K : (0 : Option V → ℝ) ∈ K := ⟨0, fun _ => le_rfl, by simp⟩
    have hu₀ : 0 < u₀ := by have := hfK 0 h0K; simpa using this
    have hscale : ∀ z ∈ K, ∀ r : ℝ, 0 ≤ r → r • z ∈ K := by
      rintro z ⟨t, ht, rfl⟩ r hr
      refine ⟨fun k => r * t k, fun k => mul_nonneg hr (ht k), ?_⟩
      simp only [Finset.smul_sum, mul_smul]
    have hfK' : ∀ z ∈ K, f z ≤ 0 := by
      intro z hz
      by_contra hpos
      push Not at hpos
      have hr : 0 ≤ u₀ / f z + 1 := by positivity
      have := hfK _ (hscale z hz _ hr)
      rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    have hgen : ∀ k, farkasGen a b k ∈ K := by
      intro k
      refine ⟨Pi.single k 1, fun k' => ?_, ?_⟩
      · by_cases h : k' = k
        · subst h; simp
        · simp [h]
      · simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq']
    set e : Option V → (Option V → ℝ) := fun w => fun j => if w = j then 1 else 0 with he
    set xv : V → ℝ := fun u => f (e (some u)) with hxv
    set τ : ℝ := f (e none) with hτ
    have hrep : ∀ z : Option V → ℝ, f z = z none * τ + ∑ u, z (some u) * xv u := by
      intro z
      rw [dual_repr_P f z, Fintype.sum_option]
    have hx_nonneg : ∀ u, 0 ≤ xv u := by
      intro u
      have := hfK' _ (hgen (Sum.inr (Sum.inl u)))
      rw [hrep] at this
      simp [farkasGen, Finset.sum_ite_eq] at this
      linarith
    have hτ0 : τ ≤ 0 := by
      have := hfK' _ (hgen (Sum.inr (Sum.inr ())))
      rw [hrep] at this
      simpa [farkasGen] using this
    have hrow : ∀ i, b i * τ + ∑ u, a i u * xv u ≤ 0 := by
      intro i
      have := hfK' _ (hgen (Sum.inl i))
      rw [hrep] at this
      simpa [farkasGen] using this
    have hobj : 0 < β * τ + ∑ u, c u * xv u := by
      have := hfz₀
      rw [hrep] at this
      have h2 : z₀ none = β := rfl
      have h3 : ∀ u, z₀ (some u) = c u := fun u => rfl
      have h4 : ∑ u, z₀ (some u) * xv u = ∑ u, c u * xv u :=
        Finset.sum_congr rfl (fun u _ => by rw [h3 u])
      rw [h2, h4] at this
      linarith
    rcases lt_or_eq_of_le hτ0 with hneg | hzero
    · -- τ < 0: scale to a feasible point
      have hpos : 0 < -τ := by linarith
      set y : V → ℝ := fun u => xv u / (-τ) with hy
      have hy0 : ∀ u, 0 ≤ y u := fun u => div_nonneg (hx_nonneg u) hpos.le
      have hyb : ∀ i, ∑ u, a i u * y u ≤ b i := by
        intro i
        have : ∑ u, a i u * y u = (∑ u, a i u * xv u) / (-τ) := by
          rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro u _; simp [hy, mul_div_assoc]
        rw [this, div_le_iff₀ hpos]
        have := hrow i
        linarith
      have := hbound y hy0 hyb
      have h2 : ∑ u, c u * y u = (∑ u, c u * xv u) / (-τ) := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro u _; simp [hy, mul_div_assoc]
      rw [h2, div_le_iff₀ hpos] at this
      linarith
    · -- τ = 0: unbounded direction
      rw [hzero] at hrow hobj
      simp only [mul_zero, zero_add] at hrow hobj
      set σ := ∑ u, c u * xv u with hσ
      have hx₀b := hbound x₀ hx₀.1 hx₀.2
      set r : ℝ := (β - ∑ u, c u * x₀ u) / σ + 1 with hr
      have hr0 : 0 ≤ r := by
        have : 0 ≤ (β - ∑ u, c u * x₀ u) / σ := div_nonneg (by linarith) hobj.le
        linarith
      set y : V → ℝ := fun u => x₀ u + r * xv u with hy
      have hy0 : ∀ u, 0 ≤ y u := fun u => add_nonneg (hx₀.1 u) (mul_nonneg hr0 (hx_nonneg u))
      have hyb : ∀ i, ∑ u, a i u * y u ≤ b i := by
        intro i
        have : ∑ u, a i u * y u = ∑ u, a i u * x₀ u + r * ∑ u, a i u * xv u := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro u _; simp only [hy]; ring
        rw [this]
        have h1 := hx₀.2 i
        have h2 : r * ∑ u, a i u * xv u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 (hrow i)
        linarith
      have := hbound y hy0 hyb
      have h2 : ∑ u, c u * y u = ∑ u, c u * x₀ u + r * σ := by
        rw [hσ, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro u _; simp only [hy]; ring
      rw [h2, hr, add_mul, div_mul_cancel₀ _ hobj.ne'] at this
      linarith

/-- Weak LP duality. -/
theorem weak_dual_lp_P {V J : Type*} [Fintype V] [Fintype J] (a : J → V → ℝ) (b : J → ℝ)
    (x : V → ℝ) (hx0 : ∀ u, 0 ≤ x u) (hxb : ∀ i, ∑ u, a i u * x u ≤ b i)
    (c : V → ℝ) (lam : J → ℝ) (hl : ∀ i, 0 ≤ lam i) (hc : ∀ u, c u ≤ ∑ i, lam i * a i u) :
    ∑ u, c u * x u ≤ ∑ i, lam i * b i := by
  calc ∑ u, c u * x u ≤ ∑ u, (∑ i, lam i * a i u) * x u :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (hc u) (hx0 u)
    _ = ∑ i, lam i * ∑ u, a i u * x u := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro u _; ring
    _ ≤ ∑ i, lam i * b i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxb i) (hl i)

theorem convex_P_P {V J : Type*} [Fintype V] [Fintype J] (a : J → V → ℝ) (b : J → ℝ) :
    Convex ℝ {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} := by
  intro x hx y hy p q hp hq hpq
  refine ⟨fun u => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hp (hx.1 u)) (mul_nonneg hq (hy.1 u))
  · have h1 := hx.2 i
    have h2 := hy.2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show ∑ u, a i u * (p * x u + q * y u) = p * ∑ u, a i u * x u + q * ∑ u, a i u * y u by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro u _; ring]
    calc _ ≤ p * b i + q * b i :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hp) (mul_le_mul_of_nonneg_left h2 hq)
      _ = b i := by rw [← add_mul, hpq, one_mul]

theorem convex_lin_le_P {V : Type*} [Fintype V] (c : V → ℝ) (β : ℝ) :
    Convex ℝ {x : V → ℝ | ∑ u, c u * x u ≤ β} :=
  convex_halfSpace_le
    ⟨fun x y => by simp [mul_add, Finset.sum_add_distrib],
     fun r x => by simp [Finset.mul_sum, mul_left_comm, smul_eq_mul]⟩ β

theorem floor_mul_bounds_P (r s : ℝ) :
    r * s - |s| ≤ (⌊r⌋ : ℝ) * s ∧ (⌊r⌋ : ℝ) * s ≤ r * s + |s| := by
  have h1 := Int.floor_le r
  have h2 := Int.lt_floor_add_one r
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]; constructor <;> nlinarith
  · rw [abs_of_neg hs]; constructor <;> nlinarith

theorem convexHull_iff_minmax_core {V : Type*} [Fintype V] {J : Type*} [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (S : Finset (V → ℝ)) (hS : S.Nonempty)
    (hSsol : ∀ x ∈ S, (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} = convexHull ℝ (S : Set (V → ℝ)) ↔
      ∀ c : V → ℤ,
        (∀ lam : J → ℝ, (∀ i, 0 ≤ lam i) → (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) →
          S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u) ≤ ∑ i, lam i * b i) ∧
        (∃ lam : J → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) ∧
          ∑ i, lam i * b i = S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u)) := by
  classical
  have hwa : ∀ c : V → ℤ, ∀ lam : J → ℝ, (∀ i, 0 ≤ lam i) →
      (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) →
      S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u) ≤ ∑ i, lam i * b i := by
    intro c lam hl hc
    exact Finset.sup'_le _ _ (fun x hx =>
      weak_dual_lp_P a b x (hSsol x hx).1 (hSsol x hx).2 _ lam hl hc)
  obtain ⟨x₀, hx₀S⟩ := hS
  have hx₀ := hSsol x₀ hx₀S
  constructor
  · intro hPS c
    refine ⟨hwa c, ?_⟩
    set β := S.sup' ⟨x₀, hx₀S⟩ (fun x => ∑ u, (c u : ℝ) * x u) with hβ
    have hbound : ∀ x : V → ℝ, (∀ u, 0 ≤ x u) → (∀ i, ∑ u, a i u * x u ≤ b i) →
        ∑ u, (c u : ℝ) * x u ≤ β := by
      intro x hx1 hx2
      have hxP : x ∈ convexHull ℝ (S : Set (V → ℝ)) := by
        rw [← hPS]; exact ⟨hx1, hx2⟩
      have hsub : convexHull ℝ (S : Set (V → ℝ)) ⊆ {x | ∑ u, (c u : ℝ) * x u ≤ β} := by
        apply convexHull_min
        · intro x hx
          exact Finset.le_sup' (fun x => ∑ u, (c u : ℝ) * x u) (Finset.mem_coe.1 hx)
        · exact convex_lin_le_P _ β
      exact hsub hxP
    obtain ⟨lam, hl, hc, hle⟩ := farkas_P a b x₀ hx₀ (fun u => (c u : ℝ)) β hbound
    exact ⟨lam, hl, hc, le_antisymm hle (hwa c lam hl hc)⟩
  · intro h
    apply Set.Subset.antisymm
    · intro y hy
      by_contra hny
      obtain ⟨f, u₀, hfS, hfy⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
        (S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed hny
      set w : V → ℝ := fun u => f (fun j => if u = j then 1 else 0) with hw
      have hrep : ∀ z, f z = ∑ u, z u * w u := fun z => dual_repr_P f z
      set g := f y - u₀ with hg
      have hg0 : 0 < g := by linarith
      set B := ∑ u, |y u| + ∑ z ∈ S, ∑ u, |z u| with hB
      have hB0 : 0 ≤ B := add_nonneg (Finset.sum_nonneg fun u _ => abs_nonneg _)
        (Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun u _ => abs_nonneg _)
      obtain ⟨N, hN⟩ := exists_nat_gt (B / g)
      have hNg : B < N * g := by rwa [div_lt_iff₀ hg0] at hN
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      set c : V → ℤ := fun u => ⌊(N : ℝ) * w u⌋ with hc
      have hlow : (N : ℝ) * f y - ∑ u, |y u| ≤ ∑ u, (c u : ℝ) * y u := by
        rw [hrep, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro u _
        have := (floor_mul_bounds_P ((N : ℝ) * w u) (y u)).1
        simp only [hc]
        linarith
      have hup : ∀ z ∈ S, ∑ u, (c u : ℝ) * z u ≤ (N : ℝ) * f z + ∑ u, |z u| := by
        intro z hz
        rw [hrep, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro u _
        have := (floor_mul_bounds_P ((N : ℝ) * w u) (z u)).2
        simp only [hc]
        linarith
      obtain ⟨lam, hl, hcl, hsum⟩ := (h c).2
      have hyle : ∑ u, (c u : ℝ) * y u ≤ ∑ i, lam i * b i :=
        weak_dual_lp_P a b y hy.1 hy.2 _ lam hl hcl
      obtain ⟨z, hzS, hz⟩ := Finset.exists_mem_eq_sup' ⟨x₀, hx₀S⟩
        (fun x => ∑ u, (c u : ℝ) * x u)
      rw [hsum, hz] at hyle
      have hfz : f z < u₀ := hfS z (subset_convexHull ℝ _ (Finset.mem_coe.2 hzS))
      have hzB : ∑ u, |z u| ≤ ∑ z ∈ S, ∑ u, |z u| :=
        Finset.single_le_sum (f := fun z => ∑ u, |z u|)
          (fun z _ => Finset.sum_nonneg fun u _ => abs_nonneg _) hzS
      have := hup z hzS
      have h1 : (N : ℝ) * f z ≤ N * (f y - g) := by
        apply mul_le_mul_of_nonneg_left _ hN0; linarith
      nlinarith
    · apply convexHull_min
      · intro x hx; exact hSsol x (Finset.mem_coe.1 hx)
      · exact convex_P_P a b

end ChvatalPolytopes.Perfect

open ChvatalPolytopes.Perfect


theorem solution {V : Type*} [Fintype V] {J : Type*} [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (S : Finset (V → ℝ)) (hS : S.Nonempty)
    (hSsol : ∀ x ∈ S, (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} = convexHull ℝ (S : Set (V → ℝ)) ↔
      ∀ c : V → ℤ,
        (∀ lam : J → ℝ, (∀ i, 0 ≤ lam i) → (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) →
          S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u) ≤ ∑ i, lam i * b i) ∧
        (∃ lam : J → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) ∧
          ∑ i, lam i * b i = S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u)) := by
  exact convexHull_iff_minmax_core a b S hS hSsol
