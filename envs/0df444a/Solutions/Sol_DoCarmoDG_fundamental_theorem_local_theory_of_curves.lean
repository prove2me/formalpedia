-- Prove2me | solution 1 for DoCarmoDG.fundamental_theorem_local_theory_of_curves
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T14:09:58.661991+00:00
-- url     : https://prove2.me/submissions/0af3ba11-77be-40db-9e38-d8f88c698e13

import Mathlib
import Definitions.Def_DoCarmo_local_theory_curves

/-! 4cd095fa DoCarmoDG.fundamental_theorem_local_theory_of_curves (do Carmo 1-5, fundamental theorem of the local theory of curves).
Existence: the Frenet system t'=kn, n'=-kt-tau b, b'=tau n on frames x : Fin 3 -> R^3 is skew, so
|t|^2+|n|^2+|b|^2 is conserved.  On a compact [c,d] inside (a,b) a ContDiffBump cutoff makes the field
bounded and globally Lipschitz, IsPicardLindelof gives a solution on all of [c,d], and conservation keeps
the cutoff inactive.  Solutions on nested intervals agree (energy uniqueness) and patch to (a,b); the
frame is C^inf by bootstrapping, orthonormal by a Gram-energy argument, positively oriented by the IVT
(<b, t x n> is continuous with square 1), and alpha = integral of t.
Uniqueness: for an arc-length curve with curvature k > 0 the Frenet formulas are re-derived
(derivatives of the constant inner products + expansion in the orthonormal basis (t,n,b)).  rho maps
frame(alpha)(s0) to frame(beta)(s0) (OrthonormalBasis.equiv, det 1 via Basis.det_comp and the triple
product), the energy <rho t1,t2>+<rho n1,n2>+<rho b1,b2> is constant = 3, so rho t1 = t2 and
beta - rho alpha is constant.
No `Theorems.*` module is imported: every DoCarmoDG fact used is re-proved here. -/

set_option autoImplicit false

namespace FrenetBuild


open Set Filter Topology DoCarmoDG
open scoped NNReal

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem norm_one_of_inner (v : E3) (h : inner ℝ v v = 1) : ‖v‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).1 (by rw [← real_inner_self_eq_norm_sq]; exact h)

theorem contDiff_cross : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => cross p.1 p.2) := by
  unfold cross
  refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- The Frenet vector field on frames `x = (t, n, b)`. -/
noncomputable def frF (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) : Fin 3 → E3 :=
  ![k s • x 1, -(k s • x 0) - τ s • x 2, τ s • x 1]

theorem frF_apply0 (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) : frF k τ s x 0 = k s • x 1 := rfl

theorem frF_apply1 (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) :
    frF k τ s x 1 = -(k s • x 0) - τ s • x 2 := rfl

theorem frF_apply2 (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) : frF k τ s x 2 = τ s • x 1 := rfl

/-- Energy of a frame. -/
noncomputable def frQ (x : Fin 3 → E3) : ℝ :=
  inner ℝ (x 0) (x 0) + inner ℝ (x 1) (x 1) + inner ℝ (x 2) (x 2)

theorem frF_sub (k τ : ℝ → ℝ) (s : ℝ) (x y : Fin 3 → E3) :
    frF k τ s x - frF k τ s y = frF k τ s (x - y) := by
  funext i
  fin_cases i <;> simp [frF, smul_sub] <;> abel

theorem frF_smul (k τ : ℝ → ℝ) (s c : ℝ) (x : Fin 3 → E3) :
    frF k τ s (c • x) = c • frF k τ s x := by
  funext i
  fin_cases i <;> simp [frF, smul_sub, smul_smul, mul_comm]

theorem frF_skew (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) :
    inner ℝ (x 0) (frF k τ s x 0) + inner ℝ (x 1) (frF k τ s x 1)
      + inner ℝ (x 2) (frF k τ s x 2) = 0 := by
  simp only [frF_apply0, frF_apply1, frF_apply2, inner_sub_right, inner_neg_right,
    real_inner_smul_right, real_inner_comm (x 0) (x 1), real_inner_comm (x 1) (x 2)]
  ring

theorem norm_frF_le (k τ : ℝ → ℝ) (s : ℝ) (x : Fin 3 → E3) :
    ‖frF k τ s x‖ ≤ (|k s| + |τ s|) * ‖x‖ := by
  have h0 := norm_le_pi_norm x 0
  have h1 := norm_le_pi_norm x 1
  have h2 := norm_le_pi_norm x 2
  have hk := abs_nonneg (k s)
  have hτ := abs_nonneg (τ s)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, frF_apply0, norm_smul, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_nonneg hτ (norm_nonneg x)]
  · simp only [Fin.mk_one, frF_apply1]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_neg, norm_smul, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left h0 hk, mul_le_mul_of_nonneg_left h2 hτ]
  · simp only [Fin.reduceFinMk, frF_apply2, norm_smul, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left h1 hτ, mul_nonneg hk (norm_nonneg x)]

theorem hasDerivWithinAt_frQ {y : ℝ → Fin 3 → E3} {y' : Fin 3 → E3} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt y y' s t) :
    HasDerivWithinAt (fun u => frQ (y u))
      (2 * (inner ℝ (y t 0) (y' 0) + inner ℝ (y t 1) (y' 1) + inner ℝ (y t 2) (y' 2))) s t := by
  have hi := fun i => hasDerivWithinAt_pi.1 h i
  have h0 := (hi 0).inner ℝ (hi 0)
  have h1 := (hi 1).inner ℝ (hi 1)
  have h2 := (hi 2).inner ℝ (hi 2)
  refine ((h0.add h1).add h2).congr_deriv ?_
  rw [real_inner_comm (y' 0), real_inner_comm (y' 1), real_inner_comm (y' 2)]
  ring

/-- A smooth cutoff making the Frenet field globally bounded and Lipschitz. -/
noncomputable def bump3 : ContDiffBump (0 : Fin 3 → E3) := ⟨2, 3, by norm_num, by norm_num⟩

noncomputable def trunc3 (x : Fin 3 → E3) : Fin 3 → E3 := bump3 x • x

theorem trunc3_of_norm_le {x : Fin 3 → E3} (hx : ‖x‖ ≤ 2) : trunc3 x = x := by
  unfold trunc3
  rw [bump3.one_of_mem_closedBall (by simpa [bump3] using hx), one_smul]

theorem norm_trunc3_le (x : Fin 3 → E3) : ‖trunc3 x‖ ≤ 3 := by
  unfold trunc3
  by_cases hx : ‖x‖ < 3
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bump3.nonneg]
    have := bump3.le_one (x := x)
    nlinarith [norm_nonneg x]
  · have : bump3 x = 0 := by
      apply Function.notMem_support.1
      rw [bump3.support_eq]
      simpa [bump3] using hx
    simp [this]

theorem trunc3_lipschitz : ∃ C, LipschitzWith C trunc3 :=
  ContDiff.lipschitzWith_of_hasCompactSupport (n := 1) bump3.hasCompactSupport.smul_right
    (bump3.contDiff.smul contDiff_id) one_ne_zero

theorem exists_sol_Icc (k τ : ℝ → ℝ) (c d s0 : ℝ) (hk : ContinuousOn k (Icc c d))
    (hτ : ContinuousOn τ (Icc c d)) (hs0 : s0 ∈ Icc c d) (x0 : Fin 3 → E3) (hx0 : frQ x0 = 3) :
    ∃ y : ℝ → Fin 3 → E3, y s0 = x0 ∧
      ∀ t ∈ Icc c d, HasDerivWithinAt y (frF k τ t (y t)) (Icc c d) t := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.abs.add hτ.abs)
  obtain ⟨C, hC⟩ := trunc3_lipschitz
  set M' : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩ with hM'
  have hkτ : ∀ t ∈ Icc c d, |k t| + |τ t| ≤ max M 0 := fun t ht =>
    (le_abs_self _).trans ((hM t ht).trans (le_max_left _ _))
  have hlip : ∀ t ∈ Icc c d, LipschitzWith M' (frF k τ t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, frF_sub]
      exact (norm_frF_le k τ t _).trans
        (mul_le_mul_of_nonneg_right (hkτ t ht) (norm_nonneg _))
  let f : ℝ → (Fin 3 → E3) → (Fin 3 → E3) := fun t x => frF k τ t (trunc3 x)
  have hL : (0 : ℝ) ≤ 3 * max M 0 := by positivity
  have ha : (0 : ℝ) ≤ 3 * max M 0 * (d - c) := mul_nonneg hL (by linarith [hs0.1, hs0.2])
  have hPL : IsPicardLindelof f (⟨s0, hs0⟩ : Icc c d) x0 ⟨3 * max M 0 * (d - c), ha⟩ 0
      ⟨3 * max M 0, hL⟩ (M' * C) :=
    { lipschitzOnWith := fun t ht => ((hlip t ht).comp hC).lipschitzOnWith
      continuousOn := fun x _ => by
        refine continuousOn_pi.2 fun i => ?_
        fin_cases i
        · exact hk.smul continuousOn_const
        · exact (hk.smul continuousOn_const).neg.sub (hτ.smul continuousOn_const)
        · exact hτ.smul continuousOn_const
      norm_le := fun t ht x _ => by
        refine (norm_frF_le k τ t _).trans ?_
        have := norm_trunc3_le x
        have h2 := hkτ t ht
        have h3 : 0 ≤ |k t| + |τ t| := by positivity
        show (|k t| + |τ t|) * ‖trunc3 x‖ ≤ 3 * max M 0
        nlinarith
      mul_max_le := by
        simp only [NNReal.coe_zero, sub_zero]
        exact mul_le_mul_of_nonneg_left (max_le (by linarith [hs0.1]) (by linarith [hs0.2])) hL }
  obtain ⟨y, hy0, hy⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hd : ∀ t ∈ Icc c d, HasDerivWithinAt (fun u => frQ (y u)) 0 (Icc c d) t := by
    intro t ht
    convert hasDerivWithinAt_frQ (hy t ht) using 1
    simp only [f, trunc3, frF_smul, Pi.smul_apply, real_inner_smul_right]
    have := frF_skew k τ t (y t)
    linear_combination (-2 * bump3 (y t)) * this
  have hcont : ContinuousOn (fun u => frQ (y u)) (Icc c d) := fun t ht =>
    (hd t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun t ht =>
    (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hQ : ∀ t ∈ Icc c d, frQ (y t) = 3 := fun t ht => by
    rw [hconst t ht, ← hconst s0 hs0]
    simp only [hy0, hx0]
  refine ⟨y, hy0, fun t ht => ?_⟩
  have hn : ‖y t‖ ≤ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    have hq := hQ t ht
    unfold frQ at hq
    have e0 := real_inner_self_nonneg (x := y t 0)
    have e1 := real_inner_self_nonneg (x := y t 1)
    have e2 := real_inner_self_nonneg (x := y t 2)
    have hi : inner ℝ (y t i) (y t i) ≤ 3 := by
      fin_cases i
      · simp only [Fin.zero_eta]; linarith
      · simp only [Fin.mk_one]; linarith
      · simp only [Fin.reduceFinMk]; linarith
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (y t i)]
  have := hy t ht
  simp only [f, trunc3_of_norm_le hn] at this
  exact this

theorem const_of_hasDerivAt_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G} {p q : ℝ} (h : ∀ t ∈ Ioo p q, HasDerivAt g 0 t) {x y : ℝ}
    (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) : g x = g y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (h t ht).differentiableAt.differentiableWithinAt) (fun t ht => (h t ht).deriv) hx hy

theorem sol_unique_Ioo (k τ : ℝ → ℝ) (p q s0 : ℝ) (y z : ℝ → Fin 3 → E3) (hs0 : s0 ∈ Ioo p q)
    (hy : ∀ t ∈ Ioo p q, HasDerivAt y (frF k τ t (y t)) t)
    (hz : ∀ t ∈ Ioo p q, HasDerivAt z (frF k τ t (z t)) t) (h0 : y s0 = z s0) :
    ∀ t ∈ Ioo p q, y t = z t := by
  have hd : ∀ t ∈ Ioo p q, HasDerivAt (fun u => frQ ((y - z) u)) 0 t := by
    intro t ht
    have h1 : HasDerivAt (y - z) (frF k τ t ((y - z) t)) t := by
      rw [Pi.sub_apply, ← frF_sub]; exact (hy t ht).sub (hz t ht)
    have h2 := (hasDerivWithinAt_frQ h1.hasDerivWithinAt (s := univ)).hasDerivAt univ_mem
    rw [frF_skew, mul_zero] at h2
    exact h2
  intro t ht
  have hc := const_of_hasDerivAt_zero hd ht hs0
  simp only [Pi.sub_apply, h0, sub_self] at hc
  have hq : frQ (y t - z t) = 0 := by rw [hc]; simp [frQ]
  unfold frQ at hq
  have e0 := real_inner_self_nonneg (x := (y t - z t) 0)
  have e1 := real_inner_self_nonneg (x := (y t - z t) 1)
  have e2 := real_inner_self_nonneg (x := (y t - z t) 2)
  have v0 : inner ℝ ((y t - z t) 0) ((y t - z t) 0) = 0 := by linarith
  have v1 : inner ℝ ((y t - z t) 1) ((y t - z t) 1) = 0 := by linarith
  have v2 : inner ℝ ((y t - z t) 2) ((y t - z t) 2) = 0 := by linarith
  have w0 : (y t - z t) 0 = 0 := inner_self_eq_zero.1 v0
  have w1 : (y t - z t) 1 = 0 := inner_self_eq_zero.1 v1
  have w2 : (y t - z t) 2 = 0 := inner_self_eq_zero.1 v2
  have hw : y t - z t = 0 := by
    funext i
    fin_cases i
    exacts [w0, w1, w2]
  exact sub_eq_zero.1 hw

theorem exists_sol_Ioo (k τ : ℝ → ℝ) (a b s0 : ℝ) (hk : ContinuousOn k (Ioo a b))
    (hτ : ContinuousOn τ (Ioo a b)) (hs0 : s0 ∈ Ioo a b) (x0 : Fin 3 → E3) (hx0 : frQ x0 = 3) :
    ∃ y : ℝ → Fin 3 → E3, y s0 = x0 ∧ ∀ t ∈ Ioo a b, HasDerivAt y (frF k τ t (y t)) t := by
  have hex : ∀ c d : ℝ, ∃ y : ℝ → Fin 3 → E3, a < c → c < s0 → s0 < d → d < b →
      y s0 = x0 ∧ ∀ t ∈ Icc c d, HasDerivWithinAt y (frF k τ t (y t)) (Icc c d) t := by
    intro c d
    by_cases h : a < c ∧ c < s0 ∧ s0 < d ∧ d < b
    · have hsub : Icc c d ⊆ Ioo a b := Icc_subset_Ioo h.1 h.2.2.2
      obtain ⟨y, hy⟩ := exists_sol_Icc k τ c d s0 (hk.mono hsub) (hτ.mono hsub)
        ⟨h.2.1.le, h.2.2.1.le⟩ x0 hx0
      exact ⟨y, fun _ _ _ _ => hy⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose Y hY using hex
  set cL : ℝ → ℝ := fun s => (a + min s0 s) / 2 with hcL
  set dR : ℝ → ℝ := fun s => (b + max s0 s) / 2 with hdR
  have hc : ∀ s ∈ Ioo a b, a < cL s ∧ cL s < s0 ∧ s0 < dR s ∧ dR s < b ∧ cL s < s ∧ s < dR s := by
    intro s hs
    have h1 := min_le_left s0 s
    have h2 := min_le_right s0 s
    have h3 := le_max_left s0 s
    have h4 := le_max_right s0 s
    have h5 : a < min s0 s := lt_min hs0.1 hs.1
    have h6 : max s0 s < b := max_lt hs0.2 hs.2
    simp only [hcL, hdR]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hYd : ∀ s ∈ Ioo a b, ∀ u ∈ Ioo (cL s) (dR s),
      HasDerivAt (Y (cL s) (dR s)) (frF k τ u (Y (cL s) (dR s) u)) u := by
    intro s hs u hu
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hc s hs
    exact ((hY _ _ h1 h2 h3 h4).2 u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  refine ⟨fun s => Y (cL s) (dR s) s, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := hc s0 hs0
    exact (hY _ _ h1 h2 h3 h4).1
  intro t ht
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc t ht
  have heq : (fun s => Y (cL s) (dR s) s) =ᶠ[𝓝 t] Y (cL t) (dR t) := by
    filter_upwards [Ioo_mem_nhds h5 h6, Ioo_mem_nhds ht.1 ht.2] with s hs1 hs2
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc s hs2
    have hmem : ∀ u ∈ Ioo (max (cL s) (cL t)) (min (dR s) (dR t)),
        u ∈ Ioo (cL s) (dR s) ∧ u ∈ Ioo (cL t) (dR t) := fun u hu =>
      ⟨⟨(le_max_left _ _).trans_lt hu.1, hu.2.trans_le (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans_lt hu.1, hu.2.trans_le (min_le_right _ _)⟩⟩
    exact sol_unique_Ioo k τ _ _ s0 _ _ ⟨max_lt g2 h2, lt_min g3 h3⟩
      (fun u hu => hYd s hs2 u (hmem u hu).1) (fun u hu => hYd t ht u (hmem u hu).2)
      ((hY _ _ g1 g2 g3 g4).1.trans (hY _ _ h1 h2 h3 h4).1.symm) s
      ⟨max_lt g5 hs1.1, lt_min g6 hs1.2⟩
  exact (hYd t ht t ⟨h5, h6⟩).congr_of_eventuallyEq heq

theorem sol_contDiff (k τ : ℝ → ℝ) (a b : ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ (Ioo a b)) (y : ℝ → Fin 3 → E3)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (frF k τ t (y t)) t) :
    ContDiffOn ℝ (⊤ : ℕ∞) y (Ioo a b) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.2 fun t ht => (hy t ht).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun t ht => (hy t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have heq : EqOn (fun t => frF k τ t (y t)) (deriv y) (Ioo a b) := fun t ht =>
      (hy t ht).deriv.symm
    refine ContDiffOn.congr ?_ heq.symm
    have hk' : ContDiffOn ℝ n k (Ioo a b) := hk.of_le (by exact_mod_cast le_top)
    have hτ' : ContDiffOn ℝ n τ (Ioo a b) := hτ.of_le (by exact_mod_cast le_top)
    have hy' := contDiffOn_pi.1 ih
    refine contDiffOn_pi.2 fun i => ?_
    fin_cases i
    · exact hk'.smul (hy' 1)
    · exact (hk'.smul (hy' 0)).neg.sub (hτ'.smul (hy' 2))
    · exact hτ'.smul (hy' 1)

theorem gram_const (p q s0 : ℝ) (hs0 : s0 ∈ Ioo p q) (k τ A B C U V W : ℝ → ℝ)
    (hA : ∀ t ∈ Ioo p q, HasDerivAt A (2 * k t * U t) t)
    (hB : ∀ t ∈ Ioo p q, HasDerivAt B (-2 * k t * U t - 2 * τ t * W t) t)
    (hC : ∀ t ∈ Ioo p q, HasDerivAt C (2 * τ t * W t) t)
    (hU : ∀ t ∈ Ioo p q, HasDerivAt U (k t * B t - k t * A t - τ t * V t) t)
    (hV : ∀ t ∈ Ioo p q, HasDerivAt V (k t * W t + τ t * U t) t)
    (hW : ∀ t ∈ Ioo p q, HasDerivAt W (-k t * V t - τ t * C t + τ t * B t) t)
    (h0 : A s0 = 1 ∧ B s0 = 1 ∧ C s0 = 1 ∧ U s0 = 0 ∧ V s0 = 0 ∧ W s0 = 0) :
    ∀ t ∈ Ioo p q, A t = 1 ∧ B t = 1 ∧ C t = 1 ∧ U t = 0 ∧ V t = 0 ∧ W t = 0 := by
  let G : ℝ → ℝ := fun t => (A t - 1) ^ 2 + (B t - 1) ^ 2 + (C t - 1) ^ 2 + 2 * U t ^ 2
    + 2 * V t ^ 2 + 2 * W t ^ 2
  have hG : ∀ t ∈ Ioo p q, HasDerivAt G 0 t := by
    intro t ht
    have := ((((((hA t ht).sub_const 1).pow 2).add (((hB t ht).sub_const 1).pow 2)).add
      (((hC t ht).sub_const 1).pow 2)).add (((hU t ht).pow 2).const_mul 2)).add
      (((hV t ht).pow 2).const_mul 2) |>.add (((hW t ht).pow 2).const_mul 2)
    refine this.congr_deriv ?_
    push_cast
    ring
  intro t ht
  have hc := const_of_hasDerivAt_zero hG ht hs0
  obtain ⟨a0, b0, c0, u0, v0, w0⟩ := h0
  have hG0 : G s0 = 0 := by simp only [G, a0, b0, c0, u0, v0, w0]; norm_num
  rw [hG0] at hc
  simp only [G] at hc
  have s1 := sq_nonneg (A t - 1)
  have s2 := sq_nonneg (B t - 1)
  have s3 := sq_nonneg (C t - 1)
  have s4 := sq_nonneg (U t)
  have s5 := sq_nonneg (V t)
  have s6 := sq_nonneg (W t)
  have e1 : (A t - 1) ^ 2 = 0 := by linarith
  have e2 : (B t - 1) ^ 2 = 0 := by linarith
  have e3 : (C t - 1) ^ 2 = 0 := by linarith
  have e4 : U t ^ 2 = 0 := by linarith
  have e5 : V t ^ 2 = 0 := by linarith
  have e6 : W t ^ 2 = 0 := by linarith
  refine ⟨?_, ?_, ?_, pow_eq_zero_iff two_ne_zero |>.1 e4, pow_eq_zero_iff two_ne_zero |>.1 e5,
    pow_eq_zero_iff two_ne_zero |>.1 e6⟩
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e1)
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e2)
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e3)

theorem cross_apply (u v : E3) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross]

theorem inner_eq3 (u v : E3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_left (u v : E3) : inner ℝ u (cross u v) = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem inner_cross_right (u v : E3) : inner ℝ v (cross u v) = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem inner_cross_cross (u v : E3) :
    inner ℝ (cross u v) (cross u v) = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  rw [inner_eq3, inner_eq3 u u, inner_eq3 v v, inner_eq3 u v]
  obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

/-- Orthonormal basis from an orthonormal triple. -/
noncomputable def onb3 (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) : OrthonormalBasis (Fin 3) ℝ E3 :=
  (basisOfOrthonormalOfCardEqFinrank h (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact h)

theorem onb3_apply (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) : ⇑(onb3 T N B h) = ![T, N, B] := by
  unfold onb3
  rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

theorem orthonormal3 (T N B : E3) (h1 : inner ℝ T T = 1) (h2 : inner ℝ N N = 1)
    (h3 : inner ℝ B B = 1) (h4 : inner ℝ T N = 0) (h5 : inner ℝ T B = 0) (h6 : inner ℝ N B = 0) :
    Orthonormal ℝ ![T, N, B] := by
  have n1 := norm_one_of_inner T h1
  have n2 := norm_one_of_inner N h2
  have n3 := norm_one_of_inner B h3
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [n1, n2, n3, h4, h5, h6, real_inner_comm T N, real_inner_comm T B, real_inner_comm N B]

theorem expand3 (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) (v : E3) :
    v = inner ℝ T v • T + inner ℝ N v • N + inner ℝ B v • B := by
  have := (onb3 T N B h).sum_repr' v
  rw [onb3_apply, Fin.sum_univ_three] at this
  simpa using this.symm

theorem cross_eq_triple (T N B : E3) (h1 : inner ℝ T T = 1) (h2 : inner ℝ N N = 1)
    (h3 : inner ℝ B B = 1) (h4 : inner ℝ T N = 0) (h5 : inner ℝ T B = 0) (h6 : inner ℝ N B = 0) :
    cross T N = inner ℝ B (cross T N) • B ∧ inner ℝ B (cross T N) * inner ℝ B (cross T N) = 1 := by
  have he := expand3 T N B (orthonormal3 T N B h1 h2 h3 h4 h5 h6) (cross T N)
  rw [inner_cross_left, inner_cross_right, zero_smul, zero_smul, zero_add, zero_add] at he
  refine ⟨he, ?_⟩
  have hl := inner_cross_cross T N
  rw [h1, h2, h4] at hl
  rw [he, real_inner_smul_left, real_inner_smul_right, h3] at hl
  linarith

noncomputable def stdB : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem stdB_det (v : Fin 3 → E3) : stdB.det v = inner ℝ (cross (v 0) (v 1)) (v 2) := by
  rw [Module.Basis.det_apply, Matrix.det_fin_three, inner_eq3]
  obtain ⟨h0, h1, h2⟩ := cross_apply (v 0) (v 1)
  rw [h0, h1, h2]
  simp only [Module.Basis.toMatrix_apply, stdB, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  ring

theorem std_frame :
    inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : E3) (EuclideanSpace.single 0 1) = 1 ∧
    inner ℝ (EuclideanSpace.single 1 (1 : ℝ) : E3) (EuclideanSpace.single 1 1) = 1 ∧
    inner ℝ (EuclideanSpace.single 2 (1 : ℝ) : E3) (EuclideanSpace.single 2 1) = 1 ∧
    inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : E3) (EuclideanSpace.single 1 1) = 0 ∧
    inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : E3) (EuclideanSpace.single 2 1) = 0 ∧
    inner ℝ (EuclideanSpace.single 1 (1 : ℝ) : E3) (EuclideanSpace.single 2 1) = 0 ∧
    cross (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) =
      (EuclideanSpace.single 2 (1 : ℝ) : E3) := by
  refine ⟨by simp [EuclideanSpace.inner_single_left], by simp [EuclideanSpace.inner_single_left],
    by simp [EuclideanSpace.inner_single_left], by simp [EuclideanSpace.inner_single_left],
    by simp [EuclideanSpace.inner_single_left], by simp [EuclideanSpace.inner_single_left], ?_⟩
  ext i; fin_cases i <;> simp [cross]

noncomputable def stdFrame : Fin 3 → E3 :=
  ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, EuclideanSpace.single 2 1]

theorem frQ_stdFrame : frQ stdFrame = 3 := by
  obtain ⟨h1, h2, h3, -⟩ := std_frame
  simp only [frQ, stdFrame, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h1, h2, h3]; norm_num

theorem existence (a b : ℝ) (k τ : ℝ → ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ (Ioo a b)) (hkpos : ∀ s ∈ Ioo a b, 0 < k s) :
    ∃ α : ℝ → E3, IsArcLengthCurve (Ioo a b) α ∧ (∀ s ∈ Ioo a b, curvature α s = k s) ∧
      (∀ s ∈ Ioo a b, torsion α s = τ s) := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨s0, hs0⟩
  · refine ⟨0, ⟨by rw [he]; exact contDiffOn_empty, by simp [he]⟩, by simp [he], by simp [he]⟩
  obtain ⟨x, hx0, hx⟩ := exists_sol_Ioo k τ a b s0 hk.continuousOn hτ.continuousOn hs0 stdFrame
    frQ_stdFrame
  have hxs := sol_contDiff k τ a b hk hτ x hx
  set T : ℝ → E3 := fun s => x s 0 with hTdef
  set N : ℝ → E3 := fun s => x s 1 with hNdef
  set B : ℝ → E3 := fun s => x s 2 with hBdef
  have hT : ∀ s ∈ Ioo a b, HasDerivAt T (k s • N s) s := fun s hs => hasDerivAt_pi.1 (hx s hs) 0
  have hN : ∀ s ∈ Ioo a b, HasDerivAt N (-(k s • T s) - τ s • B s) s := fun s hs =>
    hasDerivAt_pi.1 (hx s hs) 1
  have hB : ∀ s ∈ Ioo a b, HasDerivAt B (τ s • N s) s := fun s hs => hasDerivAt_pi.1 (hx s hs) 2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := std_frame
  have hx0' : T s0 = EuclideanSpace.single 0 1 ∧ N s0 = EuclideanSpace.single 1 1 ∧
      B s0 = EuclideanSpace.single 2 1 := by
    simp only [hTdef, hNdef, hBdef, hx0, stdFrame]
    exact ⟨rfl, rfl, rfl⟩
  have hon := gram_const a b s0 hs0 k τ (fun s => inner ℝ (T s) (T s))
    (fun s => inner ℝ (N s) (N s)) (fun s => inner ℝ (B s) (B s)) (fun s => inner ℝ (T s) (N s))
    (fun s => inner ℝ (T s) (B s)) (fun s => inner ℝ (N s) (B s))
    (fun t ht => ((hT t ht).inner ℝ (hT t ht)).congr_deriv (by
      simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm (T t) (N t)]; ring))
    (fun t ht => ((hN t ht).inner ℝ (hN t ht)).congr_deriv (by
      simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_comm (T t) (N t),
        real_inner_comm (N t) (B t), real_inner_comm (T t) (B t)]; ring))
    (fun t ht => ((hB t ht).inner ℝ (hB t ht)).congr_deriv (by
      simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm (N t) (B t)]; ring))
    (fun t ht => ((hT t ht).inner ℝ (hN t ht)).congr_deriv (by
      simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
        real_inner_smul_left, real_inner_smul_right]; ring))
    (fun t ht => ((hT t ht).inner ℝ (hB t ht)).congr_deriv (by
      simp only [real_inner_smul_left, real_inner_smul_right]; ring))
    (fun t ht => ((hN t ht).inner ℝ (hB t ht)).congr_deriv (by
      simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
        real_inner_smul_left, real_inner_smul_right]; ring))
    (by simp only [hx0'.1, hx0'.2.1, hx0'.2.2]; exact ⟨f1, f2, f3, f4, f5, f6⟩)
  have hTc : ContinuousOn T (Ioo a b) := fun s hs => (hT s hs).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Ioo a b) := fun s hs => (hN s hs).continuousAt.continuousWithinAt
  have hBc : ContinuousOn B (Ioo a b) := fun s hs => (hB s hs).continuousAt.continuousWithinAt
  have hcs : ∀ s ∈ Ioo a b, cross (T s) (N s) = inner ℝ (B s) (cross (T s) (N s)) • B s ∧
      inner ℝ (B s) (cross (T s) (N s)) * inner ℝ (B s) (cross (T s) (N s)) = 1 := fun s hs => by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hon s hs
    exact cross_eq_triple _ _ _ o1 o2 o3 o4 o5 o6
  have hcont : ContinuousOn (fun s => inner ℝ (B s) (cross (T s) (N s))) (Ioo a b) :=
    hBc.inner (contDiff_cross.continuous.comp_continuousOn (hTc.prodMk hNc))
  have htr : ∀ s ∈ Ioo a b, inner ℝ (B s) (cross (T s) (N s)) = 1 := by
    intro s hs
    rcases mul_self_eq_one_iff.1 (hcs s hs).2 with h | h
    · exact h
    · exfalso
      have hsub : uIcc s0 s ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hs0 hs
      have h0 : (0 : ℝ) ∈ uIcc (inner ℝ (B s0) (cross (T s0) (N s0)))
          (inner ℝ (B s) (cross (T s) (N s))) := by
        rw [h, hx0'.1, hx0'.2.1, hx0'.2.2, f7, f3]
        rw [mem_uIcc]; right; norm_num
      obtain ⟨u, hu, hu0⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
      have := (hcs u (hsub hu)).2
      simp only at hu0
      rw [hu0] at this
      norm_num at this
  have hcross : ∀ s ∈ Ioo a b, cross (T s) (N s) = B s := fun s hs => by
    rw [(hcs s hs).1, htr s hs, one_smul]
  set α : ℝ → E3 := fun s => ∫ u in s0..s, T u with hαdef
  have hα : ∀ s ∈ Ioo a b, HasDerivAt α (T s) s := fun s hs =>
    intervalIntegral.integral_hasDerivAt_right
      ((hTc.mono (ordConnected_Ioo.uIcc_subset hs0 hs)).intervalIntegrable)
      (hTc.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hTc.continuousAt (Ioo_mem_nhds hs.1 hs.2))
  have hdα : ∀ s ∈ Ioo a b, deriv α s = T s := fun s hs => (hα s hs).deriv
  have hdd : ∀ s ∈ Ioo a b, deriv (deriv α) s = k s • N s := fun s hs =>
    (show deriv α =ᶠ[𝓝 s] T from
      Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hdα).deriv_eq.trans (hT s hs).deriv
  have hnN : ∀ s ∈ Ioo a b, ‖N s‖ = 1 := fun s hs => norm_one_of_inner _ (hon s hs).2.1
  have hcurv : ∀ s ∈ Ioo a b, curvature α s = k s := fun s hs => by
    rw [curvature, hdd s hs, norm_smul, hnN s hs, Real.norm_eq_abs, abs_of_pos (hkpos s hs),
      mul_one]
  have hnormal : ∀ s ∈ Ioo a b, normal α s = N s := fun s hs => by
    rw [normal, hcurv s hs, hdd s hs, smul_smul, inv_mul_cancel₀ (hkpos s hs).ne', one_smul]
  have hbin : ∀ s ∈ Ioo a b, binormal α s = B s := fun s hs => by
    rw [binormal, tangent, hdα s hs, hnormal s hs, hcross s hs]
  refine ⟨α, ⟨(contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).2
    ⟨fun s hs => (hα s hs).differentiableAt.differentiableWithinAt,
      (contDiffOn_pi.1 hxs 0).congr hdα⟩, fun s hs => ?_⟩, hcurv, fun s hs => ?_⟩
  · rw [hdα s hs]
    exact norm_one_of_inner _ (hon s hs).1
  · rw [torsion, (show binormal α =ᶠ[𝓝 s] B from
      Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hbin).deriv_eq,
      (hB s hs).deriv, hnormal s hs, real_inner_smul_left, (hon s hs).2.1, mul_one]

theorem deriv_zero_of_const {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : ℝ → G}
    {g' : G} {a b s : ℝ} {c : G} (hg : HasDerivAt g g' s) (hs : s ∈ Ioo a b)
    (hc : ∀ u ∈ Ioo a b, g u = c) : g' = 0 :=
  hg.unique ((hasDerivAt_const s c).congr_of_eventuallyEq
    (show g =ᶠ[𝓝 s] fun _ => c from Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hc))

theorem curve_frenet (a b : ℝ) (k τ : ℝ → ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hkpos : ∀ s ∈ Ioo a b, 0 < k s) (α : ℝ → E3) (hα : IsArcLengthCurve (Ioo a b) α)
    (hkt : ∀ s ∈ Ioo a b, curvature α s = k s ∧ torsion α s = τ s) (s : ℝ) (hs : s ∈ Ioo a b) :
    HasDerivAt α (deriv α s) s ∧ HasDerivAt (deriv α) (k s • normal α s) s ∧
    HasDerivAt (normal α) (-(k s • deriv α s) - τ s • binormal α s) s ∧
    HasDerivAt (binormal α) (τ s • normal α s) s ∧
    inner ℝ (deriv α s) (deriv α s) = 1 ∧ inner ℝ (normal α s) (normal α s) = 1 ∧
    inner ℝ (binormal α s) (binormal α s) = 1 ∧ inner ℝ (deriv α s) (normal α s) = 0 ∧
    inner ℝ (deriv α s) (binormal α s) = 0 ∧ inner ℝ (normal α s) (binormal α s) = 0 := by
  obtain ⟨hα1, hα2⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 hα.1
  obtain ⟨hα3, hα4⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 hα2
  have hα5 : DifferentiableOn ℝ (deriv (deriv α)) (Ioo a b) := hα4.differentiableOn (by simp)
  have hkd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ k u := fun u hu =>
    (hk.differentiableOn (by simp)).differentiableAt (Ioo_mem_nhds hu.1 hu.2)
  have hA2 : ∀ u ∈ Ioo a b, deriv (deriv α) u = k u • normal α u := by
    intro u hu
    rw [normal, (hkt u hu).1, smul_smul, mul_inv_cancel₀ (hkpos u hu).ne', one_smul]
  have hT : ∀ u ∈ Ioo a b, HasDerivAt (deriv α) (k u • normal α u) u := fun u hu => by
    rw [← hA2 u hu]
    exact (hα3.differentiableAt (Ioo_mem_nhds hu.1 hu.2)).hasDerivAt
  have hN : ∀ u ∈ Ioo a b, HasDerivAt (normal α) (deriv (normal α) u) u := by
    intro u hu
    have hev : normal α =ᶠ[𝓝 u] fun v => (k v)⁻¹ • deriv (deriv α) v :=
      Filter.eventually_of_mem (Ioo_mem_nhds hu.1 hu.2) fun v hv => by rw [normal, (hkt v hv).1]
    have hd : DifferentiableAt ℝ (fun v => (k v)⁻¹ • deriv (deriv α) v) u :=
      ((hkd u hu).inv (hkpos u hu).ne').smul (hα5.differentiableAt (Ioo_mem_nhds hu.1 hu.2))
    exact (hd.congr_of_eventuallyEq hev).hasDerivAt
  have hB : HasDerivAt (binormal α) (deriv (binormal α) s) s := by
    have h1 : DifferentiableAt ℝ (fun p : E3 × E3 => cross p.1 p.2) (deriv α s, normal α s) :=
      (contDiff_cross.differentiable (by simp)).differentiableAt
    exact (h1.comp s ((hα3.differentiableAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      (hN s hs).differentiableAt)).hasDerivAt
  have oTT : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (deriv α u) = 1 := fun u hu => by
    rw [real_inner_self_eq_norm_sq, hα.2 u hu]; norm_num
  have oNN : ∀ u ∈ Ioo a b, inner ℝ (normal α u) (normal α u) = 1 := by
    intro u hu
    have h1 : ‖deriv (deriv α) u‖ = k u := (hkt u hu).1
    have hk0 := (hkpos u hu).ne'
    rw [normal, (hkt u hu).1, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, h1]
    field_simp
  have oTN : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (normal α u) = 0 := by
    intro u hu
    have h := deriv_zero_of_const ((hT u hu).inner ℝ (hT u hu)) hu oTT
    rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (deriv α u) (normal α u)] at h
    have h2 : k u * (2 * inner ℝ (deriv α u) (normal α u)) = 0 := by linarith
    have := (mul_eq_zero.1 h2).resolve_left (hkpos u hu).ne'
    linarith
  have oBB : ∀ u ∈ Ioo a b, inner ℝ (binormal α u) (binormal α u) = 1 := fun u hu => by
    rw [binormal, tangent, inner_cross_cross, oTT u hu, oNN u hu, oTN u hu]; norm_num
  have oTB : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (binormal α u) = 0 := fun u _ => by
    rw [binormal, tangent, inner_cross_left]
  have oNB : ∀ u ∈ Ioo a b, inner ℝ (normal α u) (binormal α u) = 0 := fun u _ => by
    rw [binormal, tangent, inner_cross_right]
  have hon := orthonormal3 _ _ _ (oTT s hs) (oNN s hs) (oBB s hs) (oTN s hs) (oTB s hs) (oNB s hs)
  have d1 := deriv_zero_of_const ((hN s hs).inner ℝ (hN s hs)) hs oNN
  have d2 := deriv_zero_of_const ((hT s hs).inner ℝ (hN s hs)) hs oTN
  have d3 := deriv_zero_of_const ((hN s hs).inner ℝ hB) hs oNB
  have d4 := deriv_zero_of_const ((hT s hs).inner ℝ hB) hs oTB
  have d5 := deriv_zero_of_const (hB.inner ℝ hB) hs oBB
  have htor : inner ℝ (deriv (binormal α) s) (normal α s) = τ s := (hkt s hs).2
  rw [real_inner_comm (normal α s) (deriv (normal α) s)] at d1
  rw [real_inner_smul_left, oNN s hs] at d2
  rw [real_inner_comm (deriv (binormal α) s) (normal α s), htor] at d3
  rw [real_inner_smul_left, oNB s hs] at d4
  rw [real_inner_comm (binormal α s) (deriv (binormal α) s)] at d5
  have eN := expand3 _ _ _ hon (deriv (normal α) s)
  have eB := expand3 _ _ _ hon (deriv (binormal α) s)
  refine ⟨(hα1.differentiableAt (Ioo_mem_nhds hs.1 hs.2)).hasDerivAt, hT s hs, ?_, ?_, oTT s hs,
    oNN s hs, oBB s hs, oTN s hs, oTB s hs, oNB s hs⟩
  · have h1 : inner ℝ (deriv α s) (deriv (normal α) s) = -k s := by linarith
    have h2 : inner ℝ (normal α s) (deriv (normal α) s) = 0 := by linarith
    have h3 : inner ℝ (binormal α s) (deriv (normal α) s) = -τ s := by
      rw [real_inner_comm]; linarith
    rw [h1, h2, h3] at eN
    convert hN s hs using 1
    rw [eN]; simp only [neg_smul, zero_smul, add_zero]; abel
  · have h1 : inner ℝ (deriv α s) (deriv (binormal α) s) = 0 := by linarith
    have h2 : inner ℝ (normal α s) (deriv (binormal α) s) = τ s := by
      rw [real_inner_comm]; exact htor
    have h3 : inner ℝ (binormal α s) (deriv (binormal α) s) = 0 := by linarith
    rw [h1, h2, h3] at eB
    convert hB using 1
    rw [eB]; simp only [zero_smul, zero_add, add_zero]

theorem inner_le_one_eq (u v : E3) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1) :
    inner ℝ u v ≤ 1 ∧ (inner ℝ u v = 1 → u = v) := by
  have h := real_inner_self_nonneg (x := u - v)
  have e : inner ℝ (u - v) (u - v) = 2 - 2 * inner ℝ u v := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hu, hv, real_inner_comm u v]; ring
  refine ⟨by linarith, fun h1 => ?_⟩
  rw [h1] at e
  have e2 : inner ℝ (u - v) (u - v) = 0 := by linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 e2)

theorem uniqueness (a b : ℝ) (k τ : ℝ → ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hkpos : ∀ s ∈ Ioo a b, 0 < k s) (α β : ℝ → E3) (hα : IsArcLengthCurve (Ioo a b) α)
    (hβ : IsArcLengthCurve (Ioo a b) β)
    (hαk : ∀ s ∈ Ioo a b, curvature α s = k s ∧ torsion α s = τ s)
    (hβk : ∀ s ∈ Ioo a b, curvature β s = k s ∧ torsion β s = τ s) :
    ∃ M : E3 → E3, IsRigidMotion M ∧ ∀ s ∈ Ioo a b, β s = M (α s) := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨s0, hs0⟩
  · exact ⟨id, ⟨LinearIsometryEquiv.refl ℝ E3, 0, by simp, fun x => by simp⟩, by simp [he]⟩
  have F1 := curve_frenet a b k τ hk hkpos α hα hαk
  have F2 := curve_frenet a b k τ hk hkpos β hβ hβk
  obtain ⟨-, -, -, -, a1, a2, a3, a4, a5, a6⟩ := F1 s0 hs0
  obtain ⟨-, -, -, -, b1, b2, b3, b4, b5, b6⟩ := F2 s0 hs0
  have ho1 := orthonormal3 _ _ _ a1 a2 a3 a4 a5 a6
  have ho2 := orthonormal3 _ _ _ b1 b2 b3 b4 b5 b6
  let ρ := (onb3 _ _ _ ho1).equiv (onb3 _ _ _ ho2) (Equiv.refl (Fin 3))
  have hρ : ∀ i, ρ (![deriv α s0, normal α s0, binormal α s0] i) =
      ![deriv β s0, normal β s0, binormal β s0] i := fun i => by
    have := (onb3 _ _ _ ho1).equiv_apply_basis (onb3 _ _ _ ho2) (Equiv.refl (Fin 3)) i
    rw [onb3_apply, onb3_apply] at this
    exact this
  have hρT : ρ (deriv α s0) = deriv β s0 := hρ 0
  have hρN : ρ (normal α s0) = normal β s0 := hρ 1
  have hρB : ρ (binormal α s0) = binormal β s0 := hρ 2
  have hdet : LinearMap.det (ρ.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
    have h := Module.Basis.det_comp stdB (ρ.toLinearEquiv : E3 →ₗ[ℝ] E3)
      ![deriv α s0, normal α s0, binormal α s0]
    have hc : ((ρ.toLinearEquiv : E3 →ₗ[ℝ] E3) ∘ ![deriv α s0, normal α s0, binormal α s0]) =
        ![deriv β s0, normal β s0, binormal β s0] := funext hρ
    rw [hc, stdB_det, stdB_det] at h
    have e1 : inner ℝ (cross (![deriv α s0, normal α s0, binormal α s0] 0)
        (![deriv α s0, normal α s0, binormal α s0] 1))
        (![deriv α s0, normal α s0, binormal α s0] 2) = 1 := a3
    have e2 : inner ℝ (cross (![deriv β s0, normal β s0, binormal β s0] 0)
        (![deriv β s0, normal β s0, binormal β s0] 1))
        (![deriv β s0, normal β s0, binormal β s0] 2) = 1 := b3
    rw [e1, e2, mul_one] at h
    exact h.symm
  have hr : ∀ {f : ℝ → E3} {f' : E3} {s : ℝ}, HasDerivAt f f' s →
      HasDerivAt (fun u => ρ (f u)) (ρ f') s := fun h =>
    (ρ.toContinuousLinearEquiv.hasFDerivAt).comp_hasDerivAt _ h
  have hEg : ∀ s ∈ Ioo a b, HasDerivAt (fun u => inner ℝ (ρ (deriv α u)) (deriv β u) +
      inner ℝ (ρ (normal α u)) (normal β u) + inner ℝ (ρ (binormal α u)) (binormal β u)) 0 s := by
    intro s hs
    obtain ⟨-, t1, n1, c1, -⟩ := F1 s hs
    obtain ⟨-, t2, n2, c2, -⟩ := F2 s hs
    refine ((((hr t1).inner ℝ t2).add ((hr n1).inner ℝ n2)).add ((hr c1).inner ℝ c2)).congr_deriv ?_
    simp only [map_smul, map_sub, map_neg, inner_sub_left, inner_sub_right, inner_neg_left,
      inner_neg_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hTT : ∀ s ∈ Ioo a b, ρ (deriv α s) = deriv β s := by
    intro s hs
    obtain ⟨-, -, -, -, x1, x2, x3, -⟩ := F1 s hs
    obtain ⟨-, -, -, -, y1, y2, y3, -⟩ := F2 s hs
    have q1 := inner_le_one_eq (ρ (deriv α s)) (deriv β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x1) y1
    have q2 := inner_le_one_eq (ρ (normal α s)) (normal β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x2) y2
    have q3 := inner_le_one_eq (ρ (binormal α s)) (binormal β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x3) y3
    have hc := const_of_hasDerivAt_zero hEg hs hs0
    simp only [hρT, hρN, hρB] at hc
    rw [b1, b2, b3] at hc
    exact q1.2 (by linarith [q2.1, q3.1])
  have hD : ∀ s ∈ Ioo a b, HasDerivAt (fun u => β u - ρ (α u)) 0 s := by
    intro s hs
    have := (F2 s hs).1.sub (hr (F1 s hs).1)
    rw [hTT s hs, sub_self] at this
    exact this
  refine ⟨fun x => ρ x + (β s0 - ρ (α s0)), ⟨ρ, β s0 - ρ (α s0), by rw [hdet]; norm_num,
    fun x => rfl⟩, fun s hs => ?_⟩
  have := const_of_hasDerivAt_zero hD hs hs0
  simp only at this ⊢
  rw [← this]
  abel

end FrenetBuild

set_option maxHeartbeats 4000000 in
open DoCarmoDG in
theorem solution
    (a b : ℝ) (k tau : ℝ → ℝ)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Set.Ioo a b))
    (htau : ContDiffOn ℝ (⊤ : ℕ∞) tau (Set.Ioo a b))
    (hkpos : ∀ s ∈ Set.Ioo a b, 0 < k s) :
    (∃ alpha : ℝ → EuclideanSpace ℝ (Fin 3),
        IsArcLengthCurve (Set.Ioo a b) alpha ∧
        (∀ s ∈ Set.Ioo a b, curvature alpha s = k s) ∧
        (∀ s ∈ Set.Ioo a b, torsion alpha s = tau s)) ∧
      (∀ alpha beta : ℝ → EuclideanSpace ℝ (Fin 3),
        IsArcLengthCurve (Set.Ioo a b) alpha →
        IsArcLengthCurve (Set.Ioo a b) beta →
        (∀ s ∈ Set.Ioo a b, curvature alpha s = k s ∧ torsion alpha s = tau s) →
        (∀ s ∈ Set.Ioo a b, curvature beta s = k s ∧ torsion beta s = tau s) →
        ∃ M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
          IsRigidMotion M ∧ ∀ s ∈ Set.Ioo a b, beta s = M (alpha s)) := by
  exact ⟨FrenetBuild.existence a b k tau hk htau hkpos,
    fun alpha beta h1 h2 h3 h4 => FrenetBuild.uniqueness a b k tau hk hkpos alpha beta h1 h2 h3 h4⟩
