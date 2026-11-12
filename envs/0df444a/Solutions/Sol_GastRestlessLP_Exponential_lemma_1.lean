-- Prove2me | solution 1 for GastRestlessLP.Exponential.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T22:14:20.372173+00:00
-- url     : https://prove2.me/submissions/73abc9d6-21b7-4e91-b211-8b916d38bae8

import Definitions.Def_GastRestlessLP_Exponential_Population

open scoped BigOperators

namespace _M5Lemma1Helper

open GastRestlessLP.Exponential

lemma sum_prod_fin {S : Type} [Fintype S] :
    ∀ (N : ℕ) (f : Fin N → S → ℝ),
      (∑ x' : Fin N → S, ∏ i : Fin N, f i (x' i)) = ∏ i : Fin N, ∑ s' : S, f i s'
  | 0, _ => by
      simp
  | N + 1, f => by
      let e : (S × (Fin N → S)) ≃ (Fin (N + 1) → S) := Fin.consEquiv (fun _ => S)
      rw [← Equiv.sum_comp e]
      simp only [e, Fin.consEquiv_apply]
      rw [Fintype.sum_prod_type]
      have hstep : ∀ s₀ : S,
          (∑ y : Fin N → S, ∏ i : Fin (N + 1), f i (@Fin.cons N (fun _ => S) s₀ y i)) =
            f 0 s₀ * ∑ y : Fin N → S, ∏ i : Fin N, f i.succ (y i) := by
        intro s₀
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y _
        exact Fin.prod_univ_succ (fun i => f i (@Fin.cons N (fun _ => S) s₀ y i))
      simp_rw [hstep, ← Finset.sum_mul]
      rw [sum_prod_fin N (fun i s' => f i.succ s'), Fin.prod_univ_succ]

lemma transitionLaw_sum_weight {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2) :
    (∑ x' : Fin N → S, (transitionLaw M x a).weight x') = 1 := by
  change (∑ x' : Fin N → S, ∏ i : Fin N, M.arm.P (a i) (x i) (x' i)) = 1
  rw [sum_prod_fin]
  have h1 : ∀ i : Fin N, (∑ s' : S, M.arm.P (a i) (x i) s') = 1 :=
    fun i => M.stochastic.2.1 (a i) (x i)
  simp [h1]

lemma transitionLaw_weight_nonneg {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2) (x' : Fin N → S) :
    0 ≤ (transitionLaw M x a).weight x' := by
  change 0 ≤ ∏ i : Fin N, M.arm.P (a i) (x i) (x' i)
  exact Finset.prod_nonneg (fun i _ => M.stochastic.1 (a i) (x i) (x' i))

lemma transitionLaw_expect_prod {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2)
    (h : Fin N → S → ℝ) :
    (transitionLaw M x a).expect (fun x' => ∏ i : Fin N, h i (x' i)) =
      ∏ i : Fin N, ∑ s' : S, M.arm.P (a i) (x i) s' * h i s' := by
  change (∑ x' : Fin N → S, (∏ i : Fin N, M.arm.P (a i) (x i) (x' i)) * ∏ i : Fin N, h i (x' i)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact sum_prod_fin N (fun i s' => M.arm.P (a i) (x i) s' * h i s')

lemma transitionLaw_expect_coord {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2)
    (i : Fin N) (g : S → ℝ) :
    (transitionLaw M x a).expect (fun x' => g (x' i)) =
      ∑ s' : S, M.arm.P (a i) (x i) s' * g s' := by
  have hrewrite : (fun x' : Fin N → S => g (x' i)) =
      (fun x' : Fin N → S => ∏ j : Fin N, (if j = i then g (x' j) else 1)) := by
    funext x'
    symm
    simp
  rw [hrewrite, transitionLaw_expect_prod M x a (fun j s' => if j = i then g s' else 1)]
  have hfactor : ∀ j : Fin N,
      (∑ s' : S, M.arm.P (a j) (x j) s' * (if j = i then g s' else 1)) =
        if j = i then ∑ s' : S, M.arm.P (a i) (x i) s' * g s' else 1 := by
    intro j
    split_ifs with hj
    · subst hj
      rfl
    · simp [M.stochastic.2.1 (a j) (x j)]
  simp_rw [hfactor]
  simp

lemma transitionLaw_expect_pair_of_ne {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2)
    {i j : Fin N} (hij : i ≠ j) (g₁ g₂ : S → ℝ) :
    (transitionLaw M x a).expect (fun x' => g₁ (x' i) * g₂ (x' j)) =
      (∑ s' : S, M.arm.P (a i) (x i) s' * g₁ s') *
        (∑ s' : S, M.arm.P (a j) (x j) s' * g₂ s') := by
  have hrewrite : (fun x' : Fin N → S => g₁ (x' i) * g₂ (x' j)) =
      (fun x' : Fin N → S =>
        ∏ k : Fin N, ((if k = i then g₁ (x' k) else 1) * (if k = j then g₂ (x' k) else 1))) := by
    funext x'
    rw [Finset.prod_mul_distrib]
    simp
  rw [hrewrite, transitionLaw_expect_prod M x a
    (fun k s' => (if k = i then g₁ s' else 1) * (if k = j then g₂ s' else 1))]
  have hfactor : ∀ k : Fin N,
      (∑ s' : S, M.arm.P (a k) (x k) s' *
          ((if k = i then g₁ s' else 1) * (if k = j then g₂ s' else 1))) =
        (if k = i then ∑ s' : S, M.arm.P (a i) (x i) s' * g₁ s' else 1) *
          (if k = j then ∑ s' : S, M.arm.P (a j) (x j) s' * g₂ s' else 1) := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hij.symm]
      · simp [hki, hkj, M.stochastic.2.1 (a k) (x k)]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

lemma expect_sum {α ι : Type*} [Fintype ι] (μ : RawBlending.UB.FinLaw α)
    (f : ι → α → ℝ) :
    μ.expect (fun x => ∑ i : ι, f i x) = ∑ i : ι, μ.expect (f i) := by
  unfold RawBlending.UB.FinLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma expect_div_const {α : Type*} (μ : RawBlending.UB.FinLaw α)
    (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x / c) = μ.expect f / c := by
  unfold RawBlending.UB.FinLaw.expect
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

lemma expect_mul_const_left {α : Type*} (μ : RawBlending.UB.FinLaw α)
    (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  unfold RawBlending.UB.FinLaw.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

lemma transitionError_eq_sum {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2)
    (x' : Fin N → S) (s : S) :
    transitionError M x a x' s =
      (∑ i : Fin N, ((if x' i = s then (1 : ℝ) else 0) - M.arm.P (a i) (x i) s)) / (N : ℝ) := by
  unfold transitionError empirical phi empiricalAllocation count
  have hemp : ((Finset.univ.filter (fun i : Fin N => x' i = s)).card : ℝ) =
      ∑ i : Fin N, (if x' i = s then (1 : ℝ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    split_ifs <;> simp
  have hphi : (∑ r : S, ∑ b : Fin 2,
      (((Finset.univ.filter (fun i : Fin N => x i = r ∧ a i = b)).card : ℝ) / (N : ℝ)) *
        M.arm.P b r s) =
      (∑ i : Fin N, M.arm.P (a i) (x i) s) / (N : ℝ) := by
    have hcard : ∀ (r : S) (b : Fin 2),
        ((Finset.univ.filter (fun i : Fin N => x i = r ∧ a i = b)).card : ℝ) =
          ∑ i : Fin N, (if x i = r ∧ a i = b then (1 : ℝ) else 0) := by
      intro r b
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs <;> simp
    simp_rw [hcard]
    have hpull : (∑ r : S, ∑ b : Fin 2,
        ((∑ i : Fin N, if x i = r ∧ a i = b then (1 : ℝ) else 0) / (N : ℝ)) * M.arm.P b r s) =
        (∑ r : S, ∑ b : Fin 2, ∑ i : Fin N,
          (if x i = r ∧ a i = b then M.arm.P b r s else 0)) / (N : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro r _
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [div_mul_eq_mul_div, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs <;> ring
    rw [hpull]
    congr 1
    have hswap1 :
        (∑ r : S, ∑ b : Fin 2, ∑ i : Fin N,
          (if x i = r ∧ a i = b then M.arm.P b r s else 0)) =
        ∑ i : Fin N, ∑ r : S, ∑ b : Fin 2,
          (if x i = r ∧ a i = b then M.arm.P b r s else 0) := by
      trans (∑ r : S, ∑ i : Fin N, ∑ b : Fin 2,
        (if x i = r ∧ a i = b then M.arm.P b r s else 0))
      · refine Finset.sum_congr rfl (fun r _ => Finset.sum_comm)
      · exact Finset.sum_comm
    rw [hswap1]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hinner : ∀ r : S,
        (∑ b : Fin 2, if x i = r ∧ a i = b then M.arm.P b r s else 0) =
          if x i = r then M.arm.P (a i) (x i) s else 0 := by
      intro r
      by_cases hxr : x i = r
      · subst hxr
        simp
      · simp [hxr]
    simp_rw [hinner]
    simp
  rw [hemp, hphi, ← sub_div, ← Finset.sum_sub_distrib]

lemma finite_cauchy_schwarz {ι : Type*} (u : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ u, f i * g i) ^ 2 ≤ (∑ i ∈ u, f i ^ 2) * (∑ i ∈ u, g i ^ 2) := by
  have hnonneg : 0 ≤ ∑ i ∈ u, ∑ j ∈ u, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hid : (∑ i ∈ u, ∑ j ∈ u, (f i * g j - f j * g i) ^ 2) =
      2 * ((∑ i ∈ u, f i ^ 2) * (∑ j ∈ u, g j ^ 2) - (∑ i ∈ u, f i * g i) ^ 2) := by
    have hexp : ∀ i j,
        (f i * g j - f j * g i) ^ 2 =
          f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2 - 2 * ((f i * g i) * (f j * g j)) := by
      intro i j
      ring
    simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : (∑ i ∈ u, ∑ j ∈ u, f i ^ 2 * g j ^ 2) =
        (∑ i ∈ u, f i ^ 2) * (∑ j ∈ u, g j ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.mul_sum]
    have h2 : (∑ i ∈ u, ∑ j ∈ u, f j ^ 2 * g i ^ 2) =
        (∑ j ∈ u, f j ^ 2) * (∑ i ∈ u, g i ^ 2) := by
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.mul_sum]
    have h3 : (∑ i ∈ u, ∑ j ∈ u, 2 * ((f i * g i) * (f j * g j))) =
        2 * (∑ i ∈ u, f i * g i) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [sq, Finset.sum_mul]
    rw [h1, h2, h3]
    ring
  linarith

lemma hoeffding_bernoulli {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) ≤ Real.exp (t ^ 2 / 8) := by
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · simp only [sub_zero, one_mul, mul_zero, Real.exp_zero, zero_mul, add_zero]
    exact Real.one_le_exp (by positivity)
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt1
  · simp only [sub_self, zero_mul, one_mul, mul_zero, Real.exp_zero, zero_add]
    exact Real.one_le_exp (by positivity)
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp
  let u : ℝ → ℝ := fun x => 1 - p + p * Real.exp x
  have hu_pos : ∀ x : ℝ, 0 < u x := by
    intro x
    dsimp [u]
    have hexp : 0 < p * Real.exp x := mul_pos hp_pos (Real.exp_pos x)
    linarith
  have hu_deriv : ∀ x : ℝ, HasDerivAt u (p * Real.exp x) x := by
    intro x
    have h := ((Real.hasDerivAt_exp x).const_mul p).const_add (1 - p)
    exact h
  let φ : ℝ → ℝ := fun x => x * p + x ^ 2 / 8 - Real.log (u x)
  let φ' : ℝ → ℝ := fun x => p + x / 4 - p * Real.exp x / u x
  let φ'' : ℝ → ℝ := fun x =>
    1 / 4 - (p * Real.exp x * u x - p * Real.exp x * (p * Real.exp x)) / (u x) ^ 2
  have hφ_deriv : ∀ x : ℝ, HasDerivAt φ (φ' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y * p) p x := by
      have h := (hasDerivAt_id x).mul_const p
      simpa only [id_eq, one_mul] using h
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 8) (x / 4) x := by
      have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        have hp2 := hasDerivAt_pow 2 x
        exact hp2.congr_deriv (by ring)
      exact (hpow.div_const 8).congr_deriv (by ring)
    have h3 : HasDerivAt (fun y : ℝ => Real.log (u y)) (p * Real.exp x / u x) x :=
      (hu_deriv x).log (hu_pos x).ne'
    exact (h1.add h2).sub h3
  have hφ'_deriv : ∀ x : ℝ, HasDerivAt φ' (φ'' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => p + y / 4) (1 / 4) x := by
      have hlin : HasDerivAt (fun y : ℝ => y / 4) (1 / 4) x := by
        have hd := (hasDerivAt_id x).div_const 4
        exact hd.congr_deriv (by ring)
      exact hlin.const_add p
    have hnum : HasDerivAt (fun y : ℝ => p * Real.exp y) (p * Real.exp x) x :=
      (Real.hasDerivAt_exp x).const_mul p
    have hquot : HasDerivAt (fun y : ℝ => p * Real.exp y / u y)
        ((p * Real.exp x * u x - p * Real.exp x * (p * Real.exp x)) / (u x) ^ 2) x :=
      hnum.div (hu_deriv x) (hu_pos x).ne'
    exact h1.sub hquot
  have hφ''_nonneg : ∀ x : ℝ, 0 ≤ φ'' x := by
    intro x
    have hsq : φ'' x = ((1 - p) - p * Real.exp x) ^ 2 / (4 * (u x) ^ 2) := by
      dsimp [φ'', u]
      have hne : (1 - p + p * Real.exp x) ≠ 0 := (hu_pos x).ne'
      field_simp [hne]
      ring
    rw [hsq]
    positivity
  have hφ'_nonneg : ∀ c : ℝ, 0 < c → 0 ≤ φ' c := by
    intro c hc
    have hcont : ContinuousOn φ' (Set.Icc 0 c) :=
      fun x _ => (hφ'_deriv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ' (Set.Ioo 0 c) :=
      fun x _ => (hφ'_deriv x).differentiableAt.differentiableWithinAt
    obtain ⟨ξ, _, hslope⟩ := exists_deriv_eq_slope φ' hc hcont hdiff
    rw [(hφ'_deriv ξ).deriv] at hslope
    have h0 : φ' 0 = 0 := by
      dsimp [φ', u]
      simp [sub_add_cancel]
    have hnn := hφ''_nonneg ξ
    rw [hslope, h0, sub_zero, sub_zero, div_nonneg_iff] at hnn
    rcases hnn with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  have hφ_nonneg : 0 ≤ φ t := by
    have hcont : ContinuousOn φ (Set.Icc 0 t) :=
      fun x _ => (hφ_deriv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ (Set.Ioo 0 t) :=
      fun x _ => (hφ_deriv x).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope φ ht_pos hcont hdiff
    rw [(hφ_deriv c).deriv] at hslope
    have h0 : φ 0 = 0 := by
      dsimp [φ, u]
      simp [sub_add_cancel]
    have hnn := hφ'_nonneg c hc.1
    rw [hslope, h0, sub_zero, sub_zero, div_nonneg_iff] at hnn
    rcases hnn with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  have hlog : Real.log (u t) ≤ t * p + t ^ 2 / 8 := by
    dsimp [φ] at hφ_nonneg
    linarith
  have hexp_le : u t ≤ Real.exp (t * p + t ^ 2 / 8) := by
    rw [← Real.exp_log (hu_pos t)]
    exact Real.exp_le_exp.mpr hlog
  have hprod : Real.exp (-t * p) * u t ≤ Real.exp (-t * p) * Real.exp (t * p + t ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left hexp_le (Real.exp_pos _).le
  have hlhs : Real.exp (-t * p) * u t =
      (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) := by
    dsimp [u]
    have hsum : -t * p + t = t * (1 - p) := by ring
    calc
      Real.exp (-t * p) * (1 - p + p * Real.exp t)
          = (1 - p) * Real.exp (-t * p) + p * (Real.exp (-t * p) * Real.exp t) := by ring
      _ = (1 - p) * Real.exp (-t * p) + p * Real.exp (-t * p + t) := by rw [← Real.exp_add]
      _ = (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) := by rw [hsum]
  have hrhs : Real.exp (-t * p) * Real.exp (t * p + t ^ 2 / 8) = Real.exp (t ^ 2 / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linarith

lemma one_sided_bernoulli_tail {S : Type} [Fintype S] [DecidableEq S]
    (M : Model S) {N : ℕ} (hN : 0 < N) (x : Fin N → S) (a : Fin N → Fin 2)
    (Y : Fin N → S → ℝ) (hY : ∀ i s', Y i s' = 0 ∨ Y i s' = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    let p : Fin N → ℝ := fun i => ∑ s' : S, M.arm.P (a i) (x i) s' * Y i s'
    probability (transitionLaw M x a)
        (fun x' => δ ≤ (∑ i : Fin N, (Y i (x' i) - p i)) / (N : ℝ)) ≤
      Real.exp (-2 * (N : ℝ) * δ ^ 2) := by
  classical
  intro p
  let t : ℝ := 4 * δ
  have ht_nonneg : 0 ≤ t := by positivity
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hpointwise : ∀ x' : Fin N → S,
      (if δ ≤ (∑ i : Fin N, (Y i (x' i) - p i)) / (N : ℝ) then (1 : ℝ) else 0) ≤
        Real.exp (-t * (N : ℝ) * δ) * ∏ i : Fin N, Real.exp (t * (Y i (x' i) - p i)) := by
    intro x'
    split_ifs with hge
    · rw [← Real.exp_sum, ← Real.exp_add]
      rw [le_div_iff₀ hN_pos] at hge
      have hmul : t * (δ * (N : ℝ)) ≤ t * ∑ i : Fin N, (Y i (x' i) - p i) :=
        mul_le_mul_of_nonneg_left hge ht_nonneg
      rw [Finset.mul_sum] at hmul
      exact Real.one_le_exp (by linarith)
    · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))
  have hexp_le :
      probability (transitionLaw M x a)
          (fun x' => δ ≤ (∑ i : Fin N, (Y i (x' i) - p i)) / (N : ℝ)) ≤
        (transitionLaw M x a).expect (fun x' =>
          Real.exp (-t * (N : ℝ) * δ) * ∏ i : Fin N, Real.exp (t * (Y i (x' i) - p i))) := by
    unfold probability RawBlending.UB.FinLaw.expect
    refine Finset.sum_le_sum ?_
    intro x' _
    exact mul_le_mul_of_nonneg_left (hpointwise x') (transitionLaw_weight_nonneg M x a x')
  rw [expect_mul_const_left,
    transitionLaw_expect_prod M x a (fun i s' => Real.exp (t * (Y i s' - p i)))] at hexp_le
  have hcoord : ∀ i : Fin N,
      (∑ s' : S, M.arm.P (a i) (x i) s' * Real.exp (t * (Y i s' - p i))) ≤
        Real.exp (t ^ 2 / 8) := by
    intro i
    have hp0 : 0 ≤ p i := by
      refine Finset.sum_nonneg ?_
      intro s' _
      rcases hY i s' with h0 | h1
      · simp [h0]
      · simp [h1, M.stochastic.1 (a i) (x i) s']
    have hp1 : p i ≤ 1 := by
      calc
        p i = ∑ s' : S, M.arm.P (a i) (x i) s' * Y i s' := rfl
        _ ≤ ∑ s' : S, M.arm.P (a i) (x i) s' * 1 := by
          refine Finset.sum_le_sum ?_
          intro s' _
          apply mul_le_mul_of_nonneg_left _ (M.stochastic.1 (a i) (x i) s')
          rcases hY i s' with h0 | h1 <;> linarith
        _ = 1 := by simp [M.stochastic.2.1 (a i) (x i)]
    have hsplit : ∀ s' : S,
        Real.exp (t * (Y i s' - p i)) =
          (1 - Y i s') * Real.exp (-t * p i) + Y i s' * Real.exp (t * (1 - p i)) := by
      intro s'
      rcases hY i s' with h0 | h1
      · simp [h0]
      · simp [h1]
    have hsum_eq :
        (∑ s' : S, M.arm.P (a i) (x i) s' * Real.exp (t * (Y i s' - p i))) =
          (1 - p i) * Real.exp (-t * p i) + p i * Real.exp (t * (1 - p i)) := by
      simp_rw [hsplit]
      have hlin : ∀ s' : S,
          M.arm.P (a i) (x i) s' *
              ((1 - Y i s') * Real.exp (-t * p i) + Y i s' * Real.exp (t * (1 - p i))) =
            (M.arm.P (a i) (x i) s' - M.arm.P (a i) (x i) s' * Y i s') * Real.exp (-t * p i) +
              (M.arm.P (a i) (x i) s' * Y i s') * Real.exp (t * (1 - p i)) := by
        intro s'
        ring
      simp_rw [hlin, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      have hrow : (∑ s' : S, M.arm.P (a i) (x i) s') = 1 := M.stochastic.2.1 (a i) (x i)
      rw [hrow]
    rw [hsum_eq]
    exact hoeffding_bernoulli hp0 hp1 ht_nonneg
  have hprod_le :
      (∏ i : Fin N, ∑ s' : S, M.arm.P (a i) (x i) s' * Real.exp (t * (Y i s' - p i))) ≤
        ∏ _i : Fin N, Real.exp (t ^ 2 / 8) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i _
      exact Finset.sum_nonneg (fun s' _ =>
        mul_nonneg (M.stochastic.1 (a i) (x i) s') (Real.exp_pos _).le)
    · intro i _
      exact hcoord i
  have hconst_prod : (∏ _i : Fin N, Real.exp (t ^ 2 / 8)) = Real.exp ((N : ℝ) * (t ^ 2 / 8)) := by
    rw [← Real.exp_sum]
    simp
  have hfinal :
      Real.exp (-t * (N : ℝ) * δ) * Real.exp ((N : ℝ) * (t ^ 2 / 8)) =
        Real.exp (-2 * (N : ℝ) * δ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  calc
    probability (transitionLaw M x a)
        (fun x' => δ ≤ (∑ i : Fin N, (Y i (x' i) - p i)) / (N : ℝ))
        ≤ Real.exp (-t * (N : ℝ) * δ) *
            ∏ i : Fin N, ∑ s' : S, M.arm.P (a i) (x i) s' * Real.exp (t * (Y i s' - p i)) :=
          hexp_le
    _ ≤ Real.exp (-t * (N : ℝ) * δ) * ∏ _i : Fin N, Real.exp (t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hprod_le (Real.exp_pos _).le
    _ = Real.exp (-2 * (N : ℝ) * δ ^ 2) := by rw [hconst_prod, hfinal]

end _M5Lemma1Helper

open GastRestlessLP.Exponential
open _M5Lemma1Helper

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : Model S) (N : ℕ) (hN : 0 < N) (x : Fin N → S) (a : Fin N → Fin 2) :
    (∀ s, (transitionLaw M x a).expect (fun x' => transitionError M x a x' s) = 0) ∧
    (transitionLaw M x a).expect (fun x' => l1 (transitionError M x a x')) ≤
      Real.sqrt (Fintype.card S : ℝ) / Real.sqrt (N : ℝ) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      probability (transitionLaw M x a) (fun x' => ε ≤ l1 (transitionError M x a x')) ≤
        2 * (Fintype.card S : ℝ) *
          Real.exp (-2 * (N : ℝ) * ε ^ 2 / (Fintype.card S : ℝ) ^ 2)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hd_pos_nat : 0 < Fintype.card S := Fintype.card_pos
  have hd_pos : (0 : ℝ) < (Fintype.card S : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  let Z : Fin N → S → S → ℝ := fun i s s' =>
    (if s' = s then (1 : ℝ) else 0) - M.arm.P (a i) (x i) s
  have hZ_mean : ∀ (i : Fin N) (s : S),
      (∑ s' : S, M.arm.P (a i) (x i) s' * Z i s s') = 0 := by
    intro i s
    dsimp [Z]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hrow : (∑ s' : S, M.arm.P (a i) (x i) s') = 1 := M.stochastic.2.1 (a i) (x i)
    have hind : (∑ s' : S, M.arm.P (a i) (x i) s' * (if s' = s then (1 : ℝ) else 0)) =
        M.arm.P (a i) (x i) s := by
      simp
    rw [hind, hrow, one_mul, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    simp_rw [transitionError_eq_sum]
    rw [expect_div_const, expect_sum]
    have hzero : ∀ i : Fin N,
        (transitionLaw M x a).expect (fun x' => Z i s (x' i)) = 0 := by
      intro i
      rw [transitionLaw_expect_coord, hZ_mean]
    simp_rw [show ∀ (i : Fin N) (x' : Fin N → S),
        (if x' i = s then (1 : ℝ) else 0) - M.arm.P (a i) (x i) s = Z i s (x' i) from
      fun _ _ => rfl, hzero]
    simp
  · have hE2_coord : ∀ s : S,
        (transitionLaw M x a).expect (fun x' => (transitionError M x a x' s) ^ 2) ≤
          (∑ i : Fin N, M.arm.P (a i) (x i) s) / (N : ℝ) ^ 2 := by
      intro s
      have hsq_eq : ∀ x' : Fin N → S,
          (transitionError M x a x' s) ^ 2 =
            (∑ i : Fin N, ∑ j : Fin N, Z i s (x' i) * Z j s (x' j)) / (N : ℝ) ^ 2 := by
        intro x'
        rw [transitionError_eq_sum, div_pow]
        congr 1
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
      simp_rw [hsq_eq]
      rw [expect_div_const, expect_sum]
      simp_rw [expect_sum]
      have hpair : ∀ i j : Fin N,
          (transitionLaw M x a).expect (fun x' => Z i s (x' i) * Z j s (x' j)) ≤
            if i = j then M.arm.P (a i) (x i) s else 0 := by
        intro i j
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte]
          have hdiag : (transitionLaw M x a).expect (fun x' => Z i s (x' i) * Z i s (x' i)) =
              ∑ s' : S, M.arm.P (a i) (x i) s' * (Z i s s' * Z i s s') :=
            transitionLaw_expect_coord M x a i (fun s' => Z i s s' * Z i s s')
          rw [hdiag]
          let p := M.arm.P (a i) (x i) s
          have hsimp : ∀ s' : S,
              M.arm.P (a i) (x i) s' * (Z i s s' * Z i s s') =
                M.arm.P (a i) (x i) s' * (if s' = s then (1 : ℝ) else 0) -
                  2 * p * (M.arm.P (a i) (x i) s' * (if s' = s then (1 : ℝ) else 0)) +
                  p ^ 2 * M.arm.P (a i) (x i) s' := by
            intro s'
            dsimp [Z, p]
            split_ifs <;> ring
          simp_rw [hsimp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          have hrow : (∑ s' : S, M.arm.P (a i) (x i) s') = 1 := M.stochastic.2.1 (a i) (x i)
          have hind : (∑ s' : S, M.arm.P (a i) (x i) s' * (if s' = s then (1 : ℝ) else 0)) = p := by
            dsimp [p]
            simp
          rw [hind, hrow]
          dsimp [p]
          nlinarith [sq_nonneg (M.arm.P (a i) (x i) s)]
        · simp only [hij, ↓reduceIte]
          rw [transitionLaw_expect_pair_of_ne M x a hij, hZ_mean, zero_mul]
      have hsum_le :
          (∑ i : Fin N, ∑ j : Fin N,
              (transitionLaw M x a).expect (fun x' => Z i s (x' i) * Z j s (x' j))) ≤
            ∑ i : Fin N, M.arm.P (a i) (x i) s := by
        calc
          (∑ i : Fin N, ∑ j : Fin N,
              (transitionLaw M x a).expect (fun x' => Z i s (x' i) * Z j s (x' j)))
              ≤ ∑ i : Fin N, ∑ j : Fin N, (if i = j then M.arm.P (a i) (x i) s else 0) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
          _ = ∑ i : Fin N, M.arm.P (a i) (x i) s := by simp
      exact div_le_div_of_nonneg_right hsum_le (sq_nonneg _)
    have hE_l1_sq :
        (transitionLaw M x a).expect (fun x' => (l1 (transitionError M x a x')) ^ 2) ≤
          (Fintype.card S : ℝ) / (N : ℝ) := by
      have hpw : ∀ x' : Fin N → S,
          (l1 (transitionError M x a x')) ^ 2 ≤
            (Fintype.card S : ℝ) * ∑ s : S, (transitionError M x a x' s) ^ 2 := by
        intro x'
        unfold l1
        have hcs := finite_cauchy_schwarz (Finset.univ : Finset S)
          (fun _ => (1 : ℝ)) (fun s => |transitionError M x a x' s|)
        simpa [sq_abs] using hcs
      have hexp1 :
          (transitionLaw M x a).expect (fun x' => (l1 (transitionError M x a x')) ^ 2) ≤
            (transitionLaw M x a).expect (fun x' =>
              (Fintype.card S : ℝ) * ∑ s : S, (transitionError M x a x' s) ^ 2) := by
        unfold RawBlending.UB.FinLaw.expect
        refine Finset.sum_le_sum ?_
        intro x' _
        exact mul_le_mul_of_nonneg_left (hpw x') (transitionLaw_weight_nonneg M x a x')
      rw [expect_mul_const_left, expect_sum] at hexp1
      have hsum_s :
          (∑ s : S, (transitionLaw M x a).expect (fun x' => (transitionError M x a x' s) ^ 2)) ≤
            1 / (N : ℝ) := by
        calc
          (∑ s : S, (transitionLaw M x a).expect (fun x' => (transitionError M x a x' s) ^ 2))
              ≤ ∑ s : S, (∑ i : Fin N, M.arm.P (a i) (x i) s) / (N : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun s _ => hE2_coord s)
          _ = (∑ i : Fin N, ∑ s : S, M.arm.P (a i) (x i) s) / (N : ℝ) ^ 2 := by
            rw [← Finset.sum_div, Finset.sum_comm]
          _ = (N : ℝ) / (N : ℝ) ^ 2 := by
            have h1 : ∀ i : Fin N, (∑ s : S, M.arm.P (a i) (x i) s) = 1 :=
              fun i => M.stochastic.2.1 (a i) (x i)
            simp [h1]
          _ = 1 / (N : ℝ) := by
            field_simp [hN_pos.ne']
      calc
        (transitionLaw M x a).expect (fun x' => (l1 (transitionError M x a x')) ^ 2)
            ≤ (Fintype.card S : ℝ) *
                ∑ s : S, (transitionLaw M x a).expect (fun x' => (transitionError M x a x' s) ^ 2) :=
          hexp1
        _ ≤ (Fintype.card S : ℝ) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_s hd_pos.le
        _ = (Fintype.card S : ℝ) / (N : ℝ) := by ring
    let μ := transitionLaw M x a
    have hcs_exp :
        (μ.expect (fun x' => l1 (transitionError M x a x'))) ^ 2 ≤
          (Fintype.card S : ℝ) / (N : ℝ) := by
      have hcs := finite_cauchy_schwarz (Finset.univ : Finset (Fin N → S))
        (fun x' => Real.sqrt (μ.weight x'))
        (fun x' => Real.sqrt (μ.weight x') * l1 (transitionError M x a x'))
      have hlhs : (∑ x' : Fin N → S,
          Real.sqrt (μ.weight x') * (Real.sqrt (μ.weight x') * l1 (transitionError M x a x'))) =
          μ.expect (fun x' => l1 (transitionError M x a x')) := by
        unfold RawBlending.UB.FinLaw.expect
        change (∑ x' : Fin N → S, _) = ∑ x' : Fin N → S, μ.weight x' * l1 (transitionError M x a x')
        refine Finset.sum_congr rfl ?_
        intro x' _
        rw [← mul_assoc, Real.mul_self_sqrt (transitionLaw_weight_nonneg M x a x')]
      have hrhs1 : (∑ x' : Fin N → S, (Real.sqrt (μ.weight x')) ^ 2) = 1 := by
        have hsq : ∀ x' : Fin N → S, (Real.sqrt (μ.weight x')) ^ 2 = μ.weight x' :=
          fun x' => Real.sq_sqrt (transitionLaw_weight_nonneg M x a x')
        simp_rw [hsq]
        exact transitionLaw_sum_weight M x a
      have hrhs2 : (∑ x' : Fin N → S,
          (Real.sqrt (μ.weight x') * l1 (transitionError M x a x')) ^ 2) =
          μ.expect (fun x' => (l1 (transitionError M x a x')) ^ 2) := by
        unfold RawBlending.UB.FinLaw.expect
        change (∑ x' : Fin N → S, _) =
          ∑ x' : Fin N → S, μ.weight x' * (l1 (transitionError M x a x')) ^ 2
        refine Finset.sum_congr rfl ?_
        intro x' _
        rw [mul_pow, Real.sq_sqrt (transitionLaw_weight_nonneg M x a x')]
      rw [hlhs, hrhs1, hrhs2, one_mul] at hcs
      exact hcs.trans hE_l1_sq
    have hexp_nonneg : 0 ≤ μ.expect (fun x' => l1 (transitionError M x a x')) := by
      unfold RawBlending.UB.FinLaw.expect l1
      exact Finset.sum_nonneg (fun x' _ => mul_nonneg (transitionLaw_weight_nonneg M x a x')
        (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    rw [← Real.sqrt_div (Nat.cast_nonneg _), ← Real.sqrt_sq hexp_nonneg]
    exact Real.sqrt_le_sqrt hcs_exp
  · intro ε hε
    classical
    rcases eq_or_lt_of_le hε with rfl | hε_pos
    · have hprob_le_one :
          probability (transitionLaw M x a) (fun x' => 0 ≤ l1 (transitionError M x a x')) ≤ 1 := by
        unfold probability RawBlending.UB.FinLaw.expect
        calc
          (∑ x' ∈ (transitionLaw M x a).supp,
              (transitionLaw M x a).weight x' *
                (if 0 ≤ l1 (transitionError M x a x') then (1 : ℝ) else 0))
              ≤ ∑ x' : Fin N → S, (transitionLaw M x a).weight x' * 1 := by
            refine Finset.sum_le_sum ?_
            intro x' _
            apply mul_le_mul_of_nonneg_left _ (transitionLaw_weight_nonneg M x a x')
            split_ifs <;> norm_num
          _ = 1 := by simp [transitionLaw_sum_weight]
      have hd_ge_one : (1 : ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast hd_pos_nat
      have hrhs_eq :
          2 * (Fintype.card S : ℝ) *
              Real.exp (-2 * (N : ℝ) * (0 : ℝ) ^ 2 / (Fintype.card S : ℝ) ^ 2) =
            2 * (Fintype.card S : ℝ) := by
        simp
      linarith
    · obtain ⟨d, hd_def⟩ : ∃ x_d : ℝ, x_d = (Fintype.card S : ℝ) := ⟨_, rfl⟩
      have hd_pos' : 0 < d := hd_def ▸ hd_pos
      obtain ⟨δ, hδ_def⟩ : ∃ x_δ : ℝ, x_δ = ε / d := ⟨_, rfl⟩
      have hδ_pos : 0 < δ := hδ_def ▸ div_pos hε_pos hd_pos'
      have hunion : ∀ x' : Fin N → S,
          (if ε ≤ l1 (transitionError M x a x') then (1 : ℝ) else 0) ≤
            ∑ s : S,
              ((if δ ≤ transitionError M x a x' s then (1 : ℝ) else 0) +
                (if δ ≤ -transitionError M x a x' s then (1 : ℝ) else 0)) := by
        intro x'
        have hsum_nonneg : ∀ s : S,
            0 ≤ (if δ ≤ transitionError M x a x' s then (1 : ℝ) else 0) +
              (if δ ≤ -transitionError M x a x' s then (1 : ℝ) else 0) := by
          intro s
          split_ifs <;> norm_num
        split_ifs with hge
        · by_contra hlt
          rw [not_le] at hlt
          have hall_lt : ∀ s : S, |transitionError M x a x' s| < δ := by
            intro s
            by_contra habs
            rw [not_lt] at habs
            have hterm_ge : (1 : ℝ) ≤
                (if δ ≤ transitionError M x a x' s then (1 : ℝ) else 0) +
                  (if δ ≤ -transitionError M x a x' s then (1 : ℝ) else 0) := by
              rcases le_abs.mp habs with hpos | hneg
              · simp only [hpos, ↓reduceIte]
                split_ifs <;> norm_num
              · simp only [hneg, ↓reduceIte]
                split_ifs <;> norm_num
            have hle := Finset.single_le_sum
              (f := fun r => (if δ ≤ transitionError M x a x' r then (1 : ℝ) else 0) +
                (if δ ≤ -transitionError M x a x' r then (1 : ℝ) else 0))
              (fun r _ => hsum_nonneg r) (Finset.mem_univ s)
            linarith
          have hsum_lt :
              (∑ s : S, |transitionError M x a x' s|) < ∑ _s : S, δ :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s _ => hall_lt s)
          have hdδ : (∑ _s : S, δ) = ε := by
            simp [hδ_def, hd_def, mul_div_cancel₀ _ hd_pos.ne']
          unfold l1 at hge
          linarith
        · exact Finset.sum_nonneg (fun s _ => hsum_nonneg s)
      have hprob_union :
          probability (transitionLaw M x a) (fun x' => ε ≤ l1 (transitionError M x a x')) ≤
            ∑ s : S,
              (probability (transitionLaw M x a) (fun x' => δ ≤ transitionError M x a x' s) +
                probability (transitionLaw M x a) (fun x' => δ ≤ -transitionError M x a x' s)) := by
        have h1 :
            probability (transitionLaw M x a) (fun x' => ε ≤ l1 (transitionError M x a x')) ≤
              (transitionLaw M x a).expect (fun x' =>
                ∑ s : S,
                  ((if δ ≤ transitionError M x a x' s then (1 : ℝ) else 0) +
                    (if δ ≤ -transitionError M x a x' s then (1 : ℝ) else 0))) := by
          unfold probability RawBlending.UB.FinLaw.expect
          refine Finset.sum_le_sum ?_
          intro x' _
          exact mul_le_mul_of_nonneg_left (hunion x') (transitionLaw_weight_nonneg M x a x')
        rw [expect_sum] at h1
        refine h1.trans (le_of_eq ?_)
        refine Finset.sum_congr rfl ?_
        intro s _
        unfold probability RawBlending.UB.FinLaw.expect
        simp_rw [mul_add, Finset.sum_add_distrib]
      have hcoord_tail : ∀ s : S,
          probability (transitionLaw M x a) (fun x' => δ ≤ transitionError M x a x' s) +
              probability (transitionLaw M x a) (fun x' => δ ≤ -transitionError M x a x' s) ≤
            2 * Real.exp (-2 * (N : ℝ) * δ ^ 2) := by
        intro s
        let Ypos : Fin N → S → ℝ := fun _ s' => if s' = s then 1 else 0
        have hYpos : ∀ i s', Ypos i s' = 0 ∨ Ypos i s' = 1 := by
          intro i s'
          dsimp [Ypos]
          split_ifs <;> simp
        have hp_pos : ∀ i : Fin N,
            (∑ s' : S, M.arm.P (a i) (x i) s' * Ypos i s') = M.arm.P (a i) (x i) s := by
          intro i
          dsimp [Ypos]
          simp
        have herr_pos : ∀ x' : Fin N → S,
            transitionError M x a x' s =
              (∑ i : Fin N,
                (Ypos i (x' i) - ∑ s' : S, M.arm.P (a i) (x i) s' * Ypos i s')) / (N : ℝ) := by
          intro x'
          rw [transitionError_eq_sum]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hp_pos]
        have hpos_eq :
            probability (transitionLaw M x a) (fun x' => δ ≤ transitionError M x a x' s) =
              probability (transitionLaw M x a)
                (fun x' => δ ≤ (∑ i : Fin N,
                  (Ypos i (x' i) - ∑ s' : S, M.arm.P (a i) (x i) s' * Ypos i s')) / (N : ℝ)) := by
          simp_rw [herr_pos]
        have hpos_bound :
            probability (transitionLaw M x a) (fun x' => δ ≤ transitionError M x a x' s) ≤
              Real.exp (-2 * (N : ℝ) * δ ^ 2) := by
          rw [hpos_eq]
          exact one_sided_bernoulli_tail M hN x a Ypos hYpos hδ_pos
        let Yneg : Fin N → S → ℝ := fun _ s' => if s' = s then 0 else 1
        have hYneg : ∀ i s', Yneg i s' = 0 ∨ Yneg i s' = 1 := by
          intro i s'
          dsimp [Yneg]
          split_ifs <;> simp
        have hp_neg : ∀ i : Fin N,
            (∑ s' : S, M.arm.P (a i) (x i) s' * Yneg i s') = 1 - M.arm.P (a i) (x i) s := by
          intro i
          have hrel : ∀ s' : S, Yneg i s' = 1 - Ypos i s' := by
            intro s'
            dsimp [Yneg, Ypos]
            split_ifs <;> ring
          simp_rw [hrel, mul_sub, mul_one, Finset.sum_sub_distrib, hp_pos,
            M.stochastic.2.1 (a i) (x i)]
        have herr_neg : ∀ x' : Fin N → S,
            -transitionError M x a x' s =
              (∑ i : Fin N,
                (Yneg i (x' i) - ∑ s' : S, M.arm.P (a i) (x i) s' * Yneg i s')) / (N : ℝ) := by
          intro x'
          rw [transitionError_eq_sum, ← neg_div, ← Finset.sum_neg_distrib]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hp_neg]
          dsimp [Yneg]
          split_ifs <;> ring
        have hneg_eq :
            probability (transitionLaw M x a) (fun x' => δ ≤ -transitionError M x a x' s) =
              probability (transitionLaw M x a)
                (fun x' => δ ≤ (∑ i : Fin N,
                  (Yneg i (x' i) - ∑ s' : S, M.arm.P (a i) (x i) s' * Yneg i s')) / (N : ℝ)) := by
          simp_rw [herr_neg]
        have hneg_bound :
            probability (transitionLaw M x a) (fun x' => δ ≤ -transitionError M x a x' s) ≤
              Real.exp (-2 * (N : ℝ) * δ ^ 2) := by
          rw [hneg_eq]
          exact one_sided_bernoulli_tail M hN x a Yneg hYneg hδ_pos
        linarith
      calc
        probability (transitionLaw M x a) (fun x' => ε ≤ l1 (transitionError M x a x'))
            ≤ ∑ s : S,
                (probability (transitionLaw M x a) (fun x' => δ ≤ transitionError M x a x' s) +
                  probability (transitionLaw M x a) (fun x' => δ ≤ -transitionError M x a x' s)) :=
          hprob_union
        _ ≤ ∑ _s : S, 2 * Real.exp (-2 * (N : ℝ) * δ ^ 2) :=
          Finset.sum_le_sum (fun s _ => hcoord_tail s)
        _ = 2 * (Fintype.card S : ℝ) *
              Real.exp (-2 * (N : ℝ) * ε ^ 2 / (Fintype.card S : ℝ) ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hδ_def, hd_def]
          have hexp_eq : -2 * (N : ℝ) * (ε / (Fintype.card S : ℝ)) ^ 2 =
              -2 * (N : ℝ) * ε ^ 2 / (Fintype.card S : ℝ) ^ 2 := by
            ring
          rw [hexp_eq]
          ring
