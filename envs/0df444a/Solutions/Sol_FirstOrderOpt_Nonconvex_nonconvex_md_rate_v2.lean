-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.nonconvex_md_rate_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:57:15.901652+00:00
-- url     : https://prove2.me/submissions/be6e029f-18ea-4d93-9e8d-84ea16219663

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

open scoped RealInnerProductSpace in
/-- Descent lemma along a convex set with an `L`-Lipschitz gradient. -/
theorem md5b41_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (L : ℝ) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (a b : E) (ha : a ∈ X) (hb : b ∈ X) :
    f b ≤ f a + ⟪fGrad a, b - a⟫ + L / 2 * ‖b - a‖ ^ 2 := by
  set d := b - a with hd
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, a + s • d ∈ X := by
    intro s hs
    have := hXconv ha hb (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
    convert this using 1
    simp only [hd]
    module
  let ψ : ℝ → ℝ := fun s => f (a + s • d) - s * ⟪fGrad a, d⟫ - L / 2 * s ^ 2 * ‖d‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt ψ
      (⟪fGrad (a + s • d), d⟫ - ⟪fGrad a, d⟫ - L * s * ‖d‖ ^ 2) (Set.Icc 0 1) s := by
    intro s hs
    have hline : HasDerivWithinAt (fun t : ℝ => a + t • d) d (Set.Icc 0 1) s := by
      simpa using (((hasDerivAt_id s).smul_const d).const_add a).hasDerivWithinAt
    have hf' : HasFDerivWithinAt f (InnerProductSpace.toDual ℝ E (fGrad (a + s • d))) X
        (a + s • d) := hGrad _ (hmem s hs)
    have hcomp := hf'.comp_hasDerivWithinAt s hline (fun t ht => hmem t ht)
    rw [InnerProductSpace.toDual_apply_apply] at hcomp
    have h2 : HasDerivWithinAt (fun t : ℝ => t * ⟪fGrad a, d⟫) ⟪fGrad a, d⟫ (Set.Icc 0 1) s := by
      simpa using (hasDerivAt_mul_const (⟪fGrad a, d⟫) (x := s)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2) (L * s * ‖d‖ ^ 2)
        (Set.Icc 0 1) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact this.hasDerivWithinAt.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    exact (hcomp.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun s hs => (hderiv s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).mono
        (by rw [interior_Icc]; exact Set.Ioo_subset_Icc_self)
    · intro s hs
      rw [interior_Icc] at hs
      have hL := hSmooth _ (hmem s (Set.Ioo_subset_Icc_self hs)) a ha
      have hc : ⟪fGrad (a + s • d) - fGrad a, d⟫ ≤ L * s * ‖d‖ ^ 2 := by
        calc ⟪fGrad (a + s • d) - fGrad a, d⟫ ≤ ‖fGrad (a + s • d) - fGrad a‖ * ‖d‖ :=
              real_inner_le_norm _ _
          _ ≤ L * ‖a + s • d - a‖ * ‖d‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = L * s * ‖d‖ ^ 2 := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]; ring
      rw [inner_sub_left] at hc
      linarith
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [ψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at h01
  have hab : a + d = b := by simp [hd]
  rw [hab] at h01
  norm_num at h01
  linarith

/-- Elementary limit: `c + K (1 - t) ≤ 0` for all `t ∈ (0,1]` gives `c + K ≤ 0`. -/
theorem md5b41_limit (c K : ℝ) (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → c + K * (1 - t) ≤ 0) : c + K ≤ 0 := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  set t := min 1 (ε / (K + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t ≤ ε / (K + 1) := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : K * t ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left htε hK
  have h3 : K * (ε / (K + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  nlinarith

open scoped RealInnerProductSpace in
open FirstOrderOpt.Prox in
/-- One prox step of mirror descent with stepsize `1/L` decreases the linearised model. -/
theorem md5b41_prox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 < L) (g a b : E)
    (ha : a ∈ X) (hb : b ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, b⟫ + L * ν.V a b + h b ≤ ⟪g, u⟫ + L * ν.V a u + h u) :
    ⟪g, b - a⟫ + h b - h a + L * ‖b - a‖ ^ 2 ≤ 0 := by
  have hV : (1 / 2) * ‖b - a‖ ^ 2 ≤ ν.V a b := by
    have := ν.strongConvex a ha b hb
    unfold DistanceGeneratingFunction.V
    linarith
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (⟪g, b - a⟫ + h b - h a + L * ν.V a b) + L / 2 * ‖b - a‖ ^ 2 * (1 - t) ≤ 0 := by
    intro t ht0 ht1
    set u := (1 - t) • b + t • a with hu
    have huX : u ∈ X := hXconv hb ha (by linarith) ht0.le (by ring)
    have hmu := hmin u huX
    have hhu : h u ≤ (1 - t) * h b + t * h a := by
      have := hhconv.2 hb ha (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      simpa [smul_eq_mul] using this
    have S1 := ν.strongConvex u huX b hb
    have S2 := ν.strongConvex u huX a ha
    have e1 : b - u = (-t) • (a - b) := by rw [hu]; module
    have e2 : a - u = (1 - t) • (a - b) := by rw [hu]; module
    have e3 : u - a = (1 - t) • (b - a) := by rw [hu]; module
    rw [e1, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos ht0] at S1
    rw [e2, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)] at S2
    have hab : ‖a - b‖ = ‖b - a‖ := norm_sub_rev a b
    rw [hab] at S1 S2
    have hωu : ν.ω u ≤ (1 - t) * ν.ω b + t * ν.ω a - 1 / 2 * t * (1 - t) * ‖b - a‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left S1 (by linarith : (0:ℝ) ≤ 1 - t),
        mul_le_mul_of_nonneg_left S2 ht0.le]
    have hgu : ⟪g, u⟫ = (1 - t) * ⟪g, b⟫ + t * ⟪g, a⟫ := by
      rw [hu, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    unfold DistanceGeneratingFunction.V at hmu ⊢
    rw [e3, map_smul, smul_eq_mul, hgu] at hmu
    rw [inner_sub_right]
    have hLω := mul_le_mul_of_nonneg_left hωu hL.le
    have hmain : t * ((⟪g, b⟫ - ⟪g, a⟫ + h b - h a +
        L * (ν.ω b - ν.ω a - (ν.dω a) (b - a))) + L / 2 * ‖b - a‖ ^ 2 * (1 - t)) ≤ 0 := by
      nlinarith
    by_contra hc
    push Not at hc
    have := mul_pos ht0 hc
    linarith
  have hlim := md5b41_limit _ _ (by positivity) key
  nlinarith

open scoped RealInnerProductSpace in open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + L * ν.V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + L * ν.V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = L • (x k - x (k + 1)))
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (2 * L ^ 2 * DΨ ^ 2) / (N : ℝ) := by
  have hstep : ∀ k, 1 ≤ k → k ≤ N →
      f (x (k + 1)) + h (x (k + 1)) + L / 2 * ‖x (k + 1) - x k‖ ^ 2 ≤ f (x k) + h (x k) := by
    intro k hk1 hkN
    have A := md5b41_prox X hXconv h hhconv ν L hL (fGrad (x k)) (x k) (x (k + 1))
      (hx k) (hx (k + 1)) (hxDef k hk1 hkN)
    have B := md5b41_descent X hXconv f L fGrad hGrad hSmooth (x k) (x (k + 1))
      (hx k) (hx (k + 1))
    linarith
  have htele : ∀ n, n ≤ N → f (x (n + 1)) + h (x (n + 1)) +
      L / 2 * ∑ i ∈ Finset.range n, ‖x (i + 1 + 1) - x (i + 1)‖ ^ 2 ≤ f (x 1) + h (x 1) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, mul_add]
      have h1 := hstep (n + 1) (by omega) hn
      have h2 := ih (by omega)
      linarith
  have hT := htele N le_rfl
  have hlow1 : ΨStar ≤ f (x (N + 1)) + h (x (N + 1)) := hΨStar.1 ⟨x (N + 1), hx _, rfl⟩
  have hlow0 : ΨStar ≤ f (x 1) + h (x 1) := hΨStar.1 ⟨x 1, hx _, rfl⟩
  set S := ∑ i ∈ Finset.range N, ‖x (i + 1 + 1) - x (i + 1)‖ ^ 2 with hS
  have hsumg : (N : ℝ) * ‖gX R‖ ^ 2 ≤ ∑ i ∈ Finset.range N, ‖gX (i + 1)‖ ^ 2 := by
    have : ∑ _i ∈ Finset.range N, ‖gX R‖ ^ 2 ≤ ∑ i ∈ Finset.range N, ‖gX (i + 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact pow_le_pow_left₀ (norm_nonneg _) (hRmin (i + 1) (by omega) (by omega)) 2
    simpa using this
  have hgS : ∑ i ∈ Finset.range N, ‖gX (i + 1)‖ ^ 2 = L ^ 2 * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hgX (i + 1) (by omega) (by omega), norm_smul, Real.norm_of_nonneg hL.le,
      norm_sub_rev]
    ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hD2 : DΨ ^ 2 = (f (x 1) + h (x 1) - ΨStar) / L := by
    rw [hDΨ, Real.sq_sqrt (div_nonneg (by linarith) hL.le)]
  rw [hD2, le_div_iff₀ hNpos]
  have hfin : 2 * L ^ 2 * ((f (x 1) + h (x 1) - ΨStar) / L) =
      2 * L * (f (x 1) + h (x 1) - ΨStar) := by
    field_simp
  rw [hfin]
  have hSb : L / 2 * S ≤ f (x 1) + h (x 1) - ΨStar := by linarith
  have := mul_le_mul_of_nonneg_left hSb (by positivity : (0:ℝ) ≤ 2 * L)
  nlinarith
