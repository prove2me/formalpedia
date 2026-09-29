-- Prove2me | solution 1 for DoCarmoDG.four_vertex_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T15:30:22.408796+00:00
-- url     : https://prove2.me/submissions/845b7f91-dc32-457b-bf91-2638c1154cc4

import Mathlib
import Definitions.Def_DoCarmo_plane_curves

/-! 0f3bc25f DoCarmoDG.four_vertex_theorem (do Carmo 1-7, Theorem 2: a simple closed convex curve has
at least four vertices).  do Carmo's route, with every step made local:
* if k' = 0 everywhere, every parameter is a vertex;
* otherwise take a global min a and max b of k in [0,l); if two further zeros of k' exist in the
  window (a, a+l) we are done (reduce them into [0,l));
* else k' >= 0 on [a,b'] and <= 0 on [b',a+l] (b' = b or b+l), by IVT + strict monotonicity;
* convexity has a global orientation (the two alternatives cut R into closed sets; a common point
  puts the curve on a line, forcing k = 0);
* the chord line h(s) = <alpha s - p, J(q-p)>: three collinear curve points force the middle
  tangent to be the line, so the line supports the curve; a supporting chord forces k = 0 at both
  ends (the tangent line at a meets the curve again, so F(s) = <q - alpha s, J alpha' s> has an
  extremum at a with F'(a) = -k(a)<q-p, alpha'(a)>); so h has fixed opposite signs on the arcs;
* do Carmo's lemma (5) without integrals: h k' = (h k + <alpha', q - p>)' with the bracket periodic,
  so h k' >= 0 on a period forces h k' = 0, contradicting h(s0) k'(s0) != 0 at an MVT point.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

open Set Filter Topology DoCarmoDG

namespace FourVertex

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-! ## Coordinates in the plane -/

theorem inner_eq2 (u v : E2) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem innerJ (u v : E2) : inner ℝ u (rot90 v) = -(u 0) * v 1 + u 1 * v 0 := by
  simp [inner_eq2, rot90]

theorem ext2 {u v : E2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem pos_of_ne {w : E2} (hw : w ≠ 0) : 0 < w 0 ^ 2 + w 1 ^ 2 := by
  by_contra h
  push Not at h
  have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  exact hw (ext2 (by simp [h0]) (by simp [h1]))

noncomputable def rotLin : E2 →ₗ[ℝ] E2 where
  toFun := rot90
  map_add' u v := by ext i; fin_cases i <;> simp [rot90]; ring
  map_smul' c u := by ext i; fin_cases i <;> simp [rot90]

noncomputable def rotL : E2 →L[ℝ] E2 := LinearMap.toContinuousLinearMap rotLin

theorem rotL_apply (w : E2) : rotL w = rot90 w := rfl

/-! ## Periodic derivatives -/

theorem per_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {l : ℝ}
    (h : Function.Periodic f l) : Function.Periodic (deriv f) l := fun x => by
  rw [← deriv_comp_add_const]; congr 1; funext y; exact h y


/-! ## One-variable real lemmas -/

/-- If `Φ' = φ ≥ 0` on `[c, e]` and `Φ c = Φ e`, then `φ = 0` on `(c, e)`. -/
theorem phi_lemma {Φ φ : ℝ → ℝ} {c e : ℝ} (hce : c < e) (hΦ : ∀ s, HasDerivAt Φ (φ s) s)
    (hφ : ∀ s ∈ Icc c e, 0 ≤ φ s) (heq : Φ c = Φ e) : ∀ s ∈ Ioo c e, φ s = 0 := by
  have hmono : MonotoneOn Φ (Icc c e) := monotoneOn_of_deriv_nonneg (convex_Icc c e)
    (fun s _ => (hΦ s).continuousAt.continuousWithinAt)
    (fun s _ => (hΦ s).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hΦ s).deriv]; exact hφ s (Ioo_subset_Icc_self hs))
  have hconst : ∀ s ∈ Icc c e, Φ s = Φ c := by
    intro s hs
    have h1 := hmono hs (right_mem_Icc.2 hce.le) hs.2
    have h2 := hmono (left_mem_Icc.2 hce.le) hs hs.1
    rw [← heq] at h1
    exact le_antisymm h1 h2
  intro s hs
  have hev : Φ =ᶠ[𝓝 s] fun _ => Φ c :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) (fun u hu => hconst u (Ioo_subset_Icc_self hu))
  exact (hΦ s).unique ((hasDerivAt_const s (Φ c)).congr_of_eventuallyEq hev)

/-- A continuous function vanishing at `a, b` and nowhere in between has one sign on `[a, b]`. -/
theorem sign_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (ha : f a = 0) (hb : f b = 0)
    (hz : ∀ r ∈ Ioo a b, f r ≠ 0) : (∀ s ∈ Icc a b, 0 ≤ f s) ∨ (∀ s ∈ Icc a b, f s ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨s1, hs1, h1⟩, ⟨s2, hs2, h2⟩⟩ := hcon
  have hs1' : s1 ∈ Ioo a b := ⟨lt_of_le_of_ne hs1.1 (fun h => by rw [← h] at h1; linarith),
    lt_of_le_of_ne hs1.2 (fun h => by rw [h] at h1; linarith)⟩
  have hs2' : s2 ∈ Ioo a b := ⟨lt_of_le_of_ne hs2.1 (fun h => by rw [← h] at h2; linarith),
    lt_of_le_of_ne hs2.2 (fun h => by rw [h] at h2; linarith)⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_uIcc hf.continuousOn
    (show (0 : ℝ) ∈ uIcc (f s1) (f s2) from mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩))
  exact hz r (ordConnected_Ioo.uIcc_subset hs1' hs2' hr) hr0

theorem neg_of_no_zero {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ} (hy : f y < 0)
    (hz : ∀ r ∈ uIcc x y, f r ≠ 0) : f x < 0 := by
  by_contra h
  push Not at h
  obtain ⟨r, hr, hr0⟩ := intermediate_value_uIcc hf.continuousOn
    (show (0 : ℝ) ∈ uIcc (f x) (f y) from mem_uIcc.2 (Or.inr ⟨hy.le, h⟩))
  exact hz r hr hr0

/-- Between a global minimum `u` and a global maximum `v`, a derivative with at most one zero
is nonnegative. -/
theorem sign_minmax {g g' : ℝ → ℝ} {u v : ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    (hg' : Continuous g') (hmin : ∀ t, g u ≤ g t) (hmax : ∀ t, g t ≤ g v)
    (hone : ∀ r1 ∈ Ioo u v, ∀ r2 ∈ Ioo u v, g' r1 = 0 → g' r2 = 0 → r1 = r2) :
    ∀ s ∈ Ioo u v, 0 ≤ g' s := by
  intro s hs
  by_contra hneg
  push Not at hneg
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  by_cases hA : ∀ r ∈ Ioo u s, g' r ≠ 0
  · have hneg' : ∀ t ∈ Ioo u s, g' t < 0 := by
      intro t ht
      apply neg_of_no_zero hg' hneg
      intro r hr
      rw [uIcc_of_le ht.2.le] at hr
      rcases eq_or_lt_of_le hr.2 with h | h
      · rw [h]; exact hneg.ne
      · exact hA r ⟨lt_of_lt_of_le ht.1 hr.1, h⟩
    have hanti : StrictAntiOn g (Icc u s) := strictAntiOn_of_deriv_neg (convex_Icc u s)
      hgc.continuousOn (fun x hx => by
        rw [interior_Icc] at hx; rw [(hg x).deriv]; exact hneg' x hx)
    have := hanti (left_mem_Icc.2 hs.1.le) (right_mem_Icc.2 hs.1.le) hs.1
    linarith [hmin s]
  · push Not at hA
    obtain ⟨r1, hr1, hr1z⟩ := hA
    have hB : ∀ r ∈ Ioo s v, g' r ≠ 0 := by
      intro r hr hrz
      have := hone r1 ⟨hr1.1, lt_trans hr1.2 hs.2⟩ r ⟨lt_trans hs.1 hr.1, hr.2⟩ hr1z hrz
      linarith [hr1.2, hr.1]
    have hneg' : ∀ t ∈ Ioo s v, g' t < 0 := by
      intro t ht
      apply neg_of_no_zero hg' hneg
      intro r hr
      rw [uIcc_of_ge ht.1.le] at hr
      rcases eq_or_lt_of_le hr.1 with h | h
      · rw [← h]; exact hneg.ne
      · exact hB r ⟨h, lt_of_le_of_lt hr.2 ht.2⟩
    have hanti : StrictAntiOn g (Icc s v) := strictAntiOn_of_deriv_neg (convex_Icc s v)
      hgc.continuousOn (fun x hx => by
        rw [interior_Icc] at hx; rw [(hg x).deriv]; exact hneg' x hx)
    have := hanti (left_mem_Icc.2 hs.2.le) (right_mem_Icc.2 hs.2.le) hs.2
    linarith [hmax s]

/-! ## Reduction of a window `[a, a + l)` into `[0, l)` -/

noncomputable def hat (l r : ℝ) : ℝ := if r < l then r else r - l

theorem hat_mem {l a r : ℝ} (ha : a ∈ Ico 0 l) (hr : r ∈ Ico a (a + l)) : hat l r ∈ Ico 0 l := by
  unfold hat; split_ifs with h
  · exact ⟨le_trans ha.1 hr.1, h⟩
  · push Not at h; exact ⟨by linarith, by linarith [hr.2, ha.2]⟩

theorem hat_per {F : Type*} {f : ℝ → F} {l : ℝ} (hf : Function.Periodic f l) (r : ℝ) :
    f (hat l r) = f r := by
  unfold hat; split_ifs
  · rfl
  · exact hf.sub_eq r

theorem hat_inj {l a r1 r2 : ℝ} (h1 : r1 ∈ Ico a (a + l)) (h2 : r2 ∈ Ico a (a + l))
    (hne : r1 ≠ r2) : hat l r1 ≠ hat l r2 := by
  unfold hat; split_ifs with c1 c2 c2
  · exact hne
  · intro h; linarith [h1.1, h2.2]
  · intro h; linarith [h2.1, h1.2]
  · intro h; exact hne (by linarith)

/-! ## Basic facts on a smooth unit-speed plane curve -/

section Curve

variable {α : ℝ → E2}

theorem c1 (hα : ContDiff ℝ (⊤ : ℕ∞) α) : ContDiff ℝ (⊤ : ℕ∞) (deriv α) :=
  (contDiff_infty_iff_deriv.1 hα).2

theorem hd0 (hα : ContDiff ℝ (⊤ : ℕ∞) α) (s : ℝ) : HasDerivAt α (deriv α s) s :=
  ((hα.differentiable (by simp)) s).hasDerivAt

theorem hd1 (hα : ContDiff ℝ (⊤ : ℕ∞) α) (s : ℝ) :
    HasDerivAt (deriv α) (deriv (deriv α) s) s :=
  hd0 (c1 hα) s

theorem unit2 (hunit : ∀ t, ‖deriv α t‖ = 1) (s : ℝ) :
    deriv α s 0 ^ 2 + deriv α s 1 ^ 2 = 1 := by
  have h := real_inner_self_eq_norm_sq (deriv α s)
  rw [hunit s, inner_eq2] at h
  linear_combination h

theorem orth (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) (s : ℝ) :
    deriv α s 0 * deriv (deriv α) s 0 + deriv α s 1 * deriv (deriv α) s 1 = 0 := by
  have h1 := (hd1 hα s).inner ℝ (hd1 hα s)
  have hc : (fun t => inner ℝ (deriv α t) (deriv α t)) = fun _ => (1 : ℝ) := by
    funext t; rw [real_inner_self_eq_norm_sq, hunit t]; norm_num
  rw [hc] at h1
  have := h1.unique (hasDerivAt_const s (1 : ℝ))
  rw [inner_eq2, inner_eq2] at this
  linarith

theorem k_eq (s : ℝ) : signedCurvature α s =
    -(deriv (deriv α) s 0) * deriv α s 1 + deriv (deriv α) s 1 * deriv α s 0 := by
  simp only [signedCurvature, innerJ]

theorem fx (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) (s : ℝ) :
    deriv (deriv α) s 0 = -(signedCurvature α s) * deriv α s 1 := by
  rw [k_eq]
  linear_combination (-(deriv (deriv α) s 0)) * unit2 hunit s + deriv α s 0 * orth hα hunit s

theorem fy (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) (s : ℝ) :
    deriv (deriv α) s 1 = signedCurvature α s * deriv α s 0 := by
  rw [k_eq]
  linear_combination (-(deriv (deriv α) s 1)) * unit2 hunit s + deriv α s 1 * orth hα hunit s

theorem k_contDiff (hα : ContDiff ℝ (⊤ : ℕ∞) α) : ContDiff ℝ (⊤ : ℕ∞) (signedCurvature α) := by
  have e : signedCurvature α = fun s =>
      -(deriv (deriv α) s 0) * deriv α s 1 + deriv (deriv α) s 1 * deriv α s 0 := funext k_eq
  rw [e]
  have a0 := (contDiff_piLp 2).1 (c1 hα) 0
  have a1 := (contDiff_piLp 2).1 (c1 hα) 1
  have b0 := (contDiff_piLp 2).1 (c1 (c1 hα)) 0
  have b1 := (contDiff_piLp 2).1 (c1 (c1 hα)) 1
  exact (b0.neg.mul a1).add (b1.mul a0)

theorem k_per {l : ℝ} (hper : Function.Periodic α l) :
    Function.Periodic (signedCurvature α) l := fun s => by
  unfold signedCurvature
  rw [per_deriv (per_deriv hper) s, per_deriv hper s]

/-- The linear function of the chord line through `p` with direction `w`. -/
noncomputable def hfun (α : ℝ → E2) (p w : E2) (s : ℝ) : ℝ := inner ℝ (α s - p) (rot90 w)

theorem hfun_eq (p w : E2) (s : ℝ) :
    hfun α p w s = -(α s 0 - p 0) * w 1 + (α s 1 - p 1) * w 0 := by
  simp only [hfun, innerJ, PiLp.sub_apply]

theorem hfun_hasDeriv (hα : ContDiff ℝ (⊤ : ℕ∞) α) (p w : E2) (s : ℝ) :
    HasDerivAt (hfun α p w) (inner ℝ (deriv α s) (rot90 w)) s := by
  have := ((hd0 hα s).sub_const p).inner ℝ (hasDerivAt_const s (rot90 w))
  rw [inner_zero_right, zero_add] at this
  exact this

theorem hfun_cont (hα : ContDiff ℝ (⊤ : ℕ∞) α) (p w : E2) : Continuous (hfun α p w) :=
  continuous_iff_continuousAt.2 fun s => (hfun_hasDeriv hα p w s).continuousAt

theorem hfun_per {l : ℝ} (hper : Function.Periodic α l) (p w : E2) :
    Function.Periodic (hfun α p w) l := fun s => by simp only [hfun, hper s]

/-- A curve lying on a line has zero curvature. -/
theorem line_flat (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) (p w : E2)
    (hw : w ≠ 0) (hz : ∀ u, hfun α p w u = 0) (u : ℝ) : signedCurvature α u = 0 := by
  have hz' : hfun α p w = fun _ => 0 := funext hz
  have e1 : ∀ t, inner ℝ (deriv α t) (rot90 w) = 0 := fun t => by
    have := hfun_hasDeriv hα p w t
    rw [hz'] at this
    exact this.unique (hasDerivAt_const t 0)
  have hd : ∀ t, HasDerivAt (fun t => inner ℝ (deriv α t) (rot90 w))
      (inner ℝ (deriv (deriv α) t) (rot90 w)) t := fun t => by
    have := (hd1 hα t).inner ℝ (hasDerivAt_const t (rot90 w))
    rw [inner_zero_right, zero_add] at this
    exact this
  have e2 : inner ℝ (deriv (deriv α) u) (rot90 w) = 0 := by
    have := hd u
    rw [show (fun t => inner ℝ (deriv α t) (rot90 w)) = fun _ => (0 : ℝ) from funext e1] at this
    exact this.unique (hasDerivAt_const u 0)
  simp only [innerJ] at e1 e2
  have E1 := e1 u
  rw [fx hα hunit, fy hα hunit] at e2
  have U := unit2 hunit u
  have hN := pos_of_ne hw
  set k := signedCurvature α u
  set x1 := deriv α u 0
  set y1 := deriv α u 1
  have hsq : (x1 * w 0 + y1 * w 1) ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    linear_combination (w 0 ^ 2 + w 1 ^ 2) * U - (-(x1) * w 1 + y1 * w 0) * E1
  have hk : k * (x1 * w 0 + y1 * w 1) = 0 := by linear_combination e2
  rcases mul_eq_zero.1 hk with h | h
  · exact h
  · rw [h] at hsq; linarith

/-- Convexity has a global orientation unless the curve is flat. -/
theorem global_sigma (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1)
    (hconv : IsConvexPlaneCurve α) (hk : ∃ s, signedCurvature α s ≠ 0) :
    (∀ t u, 0 ≤ inner ℝ (α u - α t) (rot90 (deriv α t))) ∨
      (∀ t u, inner ℝ (α u - α t) (rot90 (deriv α t)) ≤ 0) := by
  set S1 := {t : ℝ | ∀ u, 0 ≤ inner ℝ (α u - α t) (rot90 (deriv α t))} with hS1def
  set S2 := {t : ℝ | ∀ u, inner ℝ (α u - α t) (rot90 (deriv α t)) ≤ 0} with hS2def
  have hcont : ∀ u, Continuous (fun t => inner ℝ (α u - α t) (rot90 (deriv α t))) := fun u =>
    (continuous_const.sub hα.continuous).inner (rotL.continuous.comp (c1 hα).continuous)
  have hS1 : IsClosed S1 := by
    have : S1 = ⋂ u, {t | 0 ≤ inner ℝ (α u - α t) (rot90 (deriv α t))} := by
      ext t; simp [S1]
    rw [this]; exact isClosed_iInter fun u => isClosed_le continuous_const (hcont u)
  have hS2 : IsClosed S2 := by
    have : S2 = ⋂ u, {t | inner ℝ (α u - α t) (rot90 (deriv α t)) ≤ 0} := by
      ext t; simp [S2]
    rw [this]; exact isClosed_iInter fun u => isClosed_le (hcont u) continuous_const
  have hdisj : ∀ t, t ∈ S1 → t ∈ S2 → False := by
    intro t h1 h2
    have hz : ∀ u, hfun α (α t) (deriv α t) u = 0 := fun u => le_antisymm (h2 u) (h1 u)
    have hw : deriv α t ≠ 0 := by
      intro h; have := hunit t; rw [h, norm_zero] at this; exact zero_ne_one this
    obtain ⟨s, hs⟩ := hk
    exact hs (line_flat hα hunit _ _ hw hz s)
  have hunion : ∀ t, t ∈ S1 ∨ t ∈ S2 := hconv
  have heq : S1 = S2ᶜ := by
    ext t; constructor
    · intro h h'; exact hdisj t h h'
    · intro h; exact (hunion t).resolve_right h
  have hclopen : IsClopen S1 := ⟨hS1, by rw [heq]; exact hS2.isOpen_compl⟩
  rcases isClopen_iff.1 hclopen with h | h
  · right; intro t u
    have : t ∈ S2 := (hunion t).resolve_left (by rw [h]; exact fun x => x)
    exact this u
  · left; intro t u
    have : t ∈ S1 := by rw [h]; trivial
    exact this u

/-- If the tangent line at `t0` passes through another point of a (globally oriented) convex
curve, the curvature vanishes at `t0`. -/
theorem F_lemma (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) (t0 t1 : ℝ)
    (hext : (∀ s, 0 ≤ inner ℝ (α t1 - α s) (rot90 (deriv α s))) ∨
      (∀ s, inner ℝ (α t1 - α s) (rot90 (deriv α s)) ≤ 0))
    (h0 : inner ℝ (α t1 - α t0) (rot90 (deriv α t0)) = 0) (hne : α t1 ≠ α t0) :
    signedCurvature α t0 = 0 := by
  set F : ℝ → ℝ := fun s => inner ℝ (α t1 - α s) (rot90 (deriv α s)) with hFdef
  have hF : HasDerivAt F (inner ℝ (α t1 - α t0) (rotL (deriv (deriv α) t0)) +
      inner ℝ (-deriv α t0) ((rotL ∘ deriv α) t0)) t0 :=
    ((hd0 hα t0).const_sub (α t1)).inner ℝ (rotL.hasFDerivAt.comp_hasDerivAt t0 (hd1 hα t0))
  have hd : deriv F t0 = 0 := by
    rcases hext with h | h
    · exact IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall (fun s => by
        show F t0 ≤ F s
        simp only [hFdef]; rw [h0]; exact h s))
    · exact IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall (fun s => by
        show F s ≤ F t0
        simp only [hFdef]; rw [h0]; exact h s))
  rw [hF.deriv] at hd
  simp only [Function.comp, rotL_apply, innerJ, PiLp.sub_apply, PiLp.neg_apply] at hd h0
  rw [fx hα hunit, fy hα hunit] at hd
  have U := unit2 hunit t0
  have hD : α t1 - α t0 ≠ 0 := sub_ne_zero.2 hne
  have hN := pos_of_ne hD
  simp only [PiLp.sub_apply] at hN
  set k := signedCurvature α t0
  set x1 := deriv α t0 0
  set y1 := deriv α t0 1
  set d0 := α t1 0 - α t0 0
  set d1 := α t1 1 - α t0 1
  have hsq : (d0 * x1 + d1 * y1) ^ 2 = d0 ^ 2 + d1 ^ 2 := by
    linear_combination (d0 ^ 2 + d1 ^ 2) * U - (-(d0) * y1 + d1 * x1) * h0
  have hk : k * (d0 * x1 + d1 * y1) = 0 := by linear_combination -hd
  rcases mul_eq_zero.1 hk with h | h
  · exact h
  · rw [h] at hsq; linarith

/-- Degenerate case: if the chord line through `α c, α d` supports the whole curve, the
curvature vanishes at both ends. -/
theorem degen (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1)
    (hσ : (∀ t u, 0 ≤ inner ℝ (α u - α t) (rot90 (deriv α t))) ∨
      (∀ t u, inner ℝ (α u - α t) (rot90 (deriv α t)) ≤ 0)) (c d : ℝ) (hne : α c ≠ α d)
    (hone : (∀ u, 0 ≤ hfun α (α c) (α d - α c) u) ∨ (∀ u, hfun α (α c) (α d - α c) u ≤ 0)) :
    signedCurvature α c = 0 ∧ signedCurvature α d = 0 := by
  have hc0 : hfun α (α c) (α d - α c) c = 0 := by simp [hfun]
  have hd0' : hfun α (α c) (α d - α c) d = 0 := by
    rw [hfun_eq]; simp only [PiLp.sub_apply]; ring
  have hderiv : ∀ t, hfun α (α c) (α d - α c) t = 0 →
      inner ℝ (deriv α t) (rot90 (α d - α c)) = 0 := by
    intro t ht
    have hdz : deriv (hfun α (α c) (α d - α c)) t = 0 := by
      rcases hone with h | h
      · exact IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall (fun s => by rw [ht]; exact h s))
      · exact IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall (fun s => by rw [ht]; exact h s))
    rw [(hfun_hasDeriv hα _ _ t).deriv] at hdz
    exact hdz
  have ext_of : ∀ t1, (∀ s, 0 ≤ inner ℝ (α t1 - α s) (rot90 (deriv α s))) ∨
      (∀ s, inner ℝ (α t1 - α s) (rot90 (deriv α s)) ≤ 0) := by
    intro t1
    rcases hσ with h | h
    · exact Or.inl fun s => h s t1
    · exact Or.inr fun s => h s t1
  constructor
  · apply F_lemma hα hunit c d (ext_of d) _ hne.symm
    have := hderiv c hc0
    rw [innerJ] at this ⊢
    simp only [PiLp.sub_apply] at this ⊢
    linear_combination -this
  · apply F_lemma hα hunit d c (ext_of c) _ hne
    have := hderiv d hd0'
    rw [innerJ] at this ⊢
    simp only [PiLp.sub_apply] at this ⊢
    linear_combination this

/-- Three collinear points: if the middle one (in the order along the line) lies on the curve,
convexity at it forces the whole curve to one side of the line. -/
theorem mid_lemma (hunit : ∀ t, ‖deriv α t‖ = 1) (hconv : IsConvexPlaneCurve α) (p w : E2)
    (ti tj tk : ℝ) (hi : hfun α p w ti = 0) (hj : hfun α p w tj = 0) (hk : hfun α p w tk = 0)
    (hord : (inner ℝ (α ti - p) w - inner ℝ (α tj - p) w) *
      (inner ℝ (α tk - p) w - inner ℝ (α tj - p) w) < 0) (hw : w ≠ 0) :
    (∀ u, 0 ≤ hfun α p w u) ∨ (∀ u, hfun α p w u ≤ 0) := by
  have U := unit2 hunit tj
  have hN := pos_of_ne hw
  have hj' := hj
  rw [hfun_eq] at hj'
  simp only [inner_eq2, PiLp.sub_apply] at hord
  have hG : ∀ t, hfun α p w t = 0 →
      inner ℝ (α t - α tj) (rot90 (deriv α tj)) * (w 0 ^ 2 + w 1 ^ 2) =
      (((α t 0 - p 0) * w 0 + (α t 1 - p 1) * w 1) -
        ((α tj 0 - p 0) * w 0 + (α tj 1 - p 1) * w 1)) *
        (-(w 0) * deriv α tj 1 + w 1 * deriv α tj 0) := by
    intro t ht
    rw [hfun_eq] at ht
    rw [innerJ]; simp only [PiLp.sub_apply]
    linear_combination (deriv α tj 0 * w 0 + deriv α tj 1 * w 1) * (ht - hj')
  have hGi := hG ti hi
  have hGk := hG tk hk
  have hC0 : -(w 0) * deriv α tj 1 + w 1 * deriv α tj 0 = 0 := by
    by_contra hC0
    have hC2 : 0 < (-(w 0) * deriv α tj 1 + w 1 * deriv α tj 0) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hC0))
    have hsame : 0 ≤ inner ℝ (α ti - α tj) (rot90 (deriv α tj)) *
        inner ℝ (α tk - α tj) (rot90 (deriv α tj)) := by
      rcases hconv tj with h | h
      · exact mul_nonneg (h ti) (h tk)
      · exact mul_nonneg_of_nonpos_of_nonpos (h ti) (h tk)
    have hprod : inner ℝ (α ti - α tj) (rot90 (deriv α tj)) *
        inner ℝ (α tk - α tj) (rot90 (deriv α tj)) * (w 0 ^ 2 + w 1 ^ 2) ^ 2 =
        ((((α ti 0 - p 0) * w 0 + (α ti 1 - p 1) * w 1) -
          ((α tj 0 - p 0) * w 0 + (α tj 1 - p 1) * w 1)) *
        (((α tk 0 - p 0) * w 0 + (α tk 1 - p 1) * w 1) -
          ((α tj 0 - p 0) * w 0 + (α tj 1 - p 1) * w 1))) *
        (-(w 0) * deriv α tj 1 + w 1 * deriv α tj 0) ^ 2 := by
      linear_combination
        (inner ℝ (α tk - α tj) (rot90 (deriv α tj)) * (w 0 ^ 2 + w 1 ^ 2)) * hGi +
        ((((α ti 0 - p 0) * w 0 + (α ti 1 - p 1) * w 1) -
          ((α tj 0 - p 0) * w 0 + (α tj 1 - p 1) * w 1)) *
          (-(w 0) * deriv α tj 1 + w 1 * deriv α tj 0)) * hGk
    have h1 : 0 ≤ inner ℝ (α ti - α tj) (rot90 (deriv α tj)) *
        inner ℝ (α tk - α tj) (rot90 (deriv α tj)) * (w 0 ^ 2 + w 1 ^ 2) ^ 2 :=
      mul_nonneg hsame (sq_nonneg _)
    have h2 := mul_neg_of_neg_of_pos hord hC2
    linarith
  have hμ : ∀ u, hfun α p w u =
      (w 0 * deriv α tj 0 + w 1 * deriv α tj 1) * inner ℝ (α u - α tj) (rot90 (deriv α tj)) := by
    intro u
    rw [hfun_eq, innerJ]; simp only [PiLp.sub_apply]
    linear_combination hj' +
      ((α u 0 - α tj 0) * (-(deriv α tj 0)) + (α u 1 - α tj 1) * (-(deriv α tj 1))) * hC0 +
      ((α u 0 - α tj 0) * w 1 - (α u 1 - α tj 1) * w 0) * U
  rcases hconv tj with h | h <;>
    rcases le_total 0 (w 0 * deriv α tj 0 + w 1 * deriv α tj 1) with hm | hm
  · exact Or.inl fun u => by rw [hμ u]; exact mul_nonneg hm (h u)
  · exact Or.inr fun u => by rw [hμ u]; exact mul_nonpos_of_nonpos_of_nonneg hm (h u)
  · exact Or.inr fun u => by rw [hμ u]; exact mul_nonpos_of_nonneg_of_nonpos hm (h u)
  · exact Or.inl fun u => by rw [hμ u]; exact mul_nonneg_of_nonpos_of_nonpos hm (h u)

theorem tau_inj (p w : E2) (hw : w ≠ 0) (s t : ℝ) (hs : hfun α p w s = 0)
    (ht : hfun α p w t = 0) (heq : inner ℝ (α s - p) w = inner ℝ (α t - p) w) : α s = α t := by
  rw [hfun_eq] at hs ht
  simp only [inner_eq2, PiLp.sub_apply] at heq
  have hN := pos_of_ne hw
  have e0 : (α s 0 - α t 0) * (w 0 ^ 2 + w 1 ^ 2) = 0 := by
    linear_combination (w 0) * heq - (w 1) * (hs - ht)
  have e1 : (α s 1 - α t 1) * (w 0 ^ 2 + w 1 ^ 2) = 0 := by
    linear_combination (w 1) * heq + (w 0) * (hs - ht)
  have f0 := (mul_eq_zero.1 e0).resolve_right hN.ne'
  have f1 := (mul_eq_zero.1 e1).resolve_right hN.ne'
  exact ext2 (by linarith) (by linarith)

/-- A line meeting a convex curve in three distinct points supports the curve. -/
theorem three_pt (hunit : ∀ t, ‖deriv α t‖ = 1) (hconv : IsConvexPlaneCurve α) (p w : E2)
    (hw : w ≠ 0) (t1 t2 t3 : ℝ) (h1 : hfun α p w t1 = 0) (h2 : hfun α p w t2 = 0)
    (h3 : hfun α p w t3 = 0) (d12 : α t1 ≠ α t2) (d13 : α t1 ≠ α t3) (d23 : α t2 ≠ α t3) :
    (∀ u, 0 ≤ hfun α p w u) ∨ (∀ u, hfun α p w u ≤ 0) := by
  have n12 : inner ℝ (α t1 - p) w ≠ inner ℝ (α t2 - p) w :=
    fun h => d12 (tau_inj p w hw t1 t2 h1 h2 h)
  have n13 : inner ℝ (α t1 - p) w ≠ inner ℝ (α t3 - p) w :=
    fun h => d13 (tau_inj p w hw t1 t3 h1 h3 h)
  have n23 : inner ℝ (α t2 - p) w ≠ inner ℝ (α t3 - p) w :=
    fun h => d23 (tau_inj p w hw t2 t3 h2 h3 h)
  by_cases m2 : (inner ℝ (α t1 - p) w - inner ℝ (α t2 - p) w) *
      (inner ℝ (α t3 - p) w - inner ℝ (α t2 - p) w) < 0
  · exact mid_lemma hunit hconv p w t1 t2 t3 h1 h2 h3 m2 hw
  by_cases m1 : (inner ℝ (α t2 - p) w - inner ℝ (α t1 - p) w) *
      (inner ℝ (α t3 - p) w - inner ℝ (α t1 - p) w) < 0
  · exact mid_lemma hunit hconv p w t2 t1 t3 h2 h1 h3 m1 hw
  apply mid_lemma hunit hconv p w t1 t3 t2 h1 h3 h2 _ hw
  push Not at m1 m2
  generalize inner ℝ (α t1 - p) w = x1 at *
  generalize inner ℝ (α t2 - p) w = x2 at *
  generalize inner ℝ (α t3 - p) w = x3 at *
  rcases lt_or_gt_of_ne n12 with a | a <;> rcases lt_or_gt_of_ne n13 with b | b <;>
    rcases lt_or_gt_of_ne n23 with c | c <;> nlinarith

/-- The core of do Carmo's argument. -/
theorem key (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hunit : ∀ t, ‖deriv α t‖ = 1) {l : ℝ}
    (hper : Function.Periodic α l) (hconv : IsConvexPlaneCurve α) {c d : ℝ} (hcd : c < d)
    (hdc : d < c + l) (hinj : ∀ s ∈ Ico c (c + l), ∀ t ∈ Ico c (c + l), s ≠ t → α s ≠ α t)
    (hkcd : signedCurvature α c < signedCurvature α d)
    (hk1 : ∀ s ∈ Icc c d, 0 ≤ deriv (signedCurvature α) s)
    (hk2 : ∀ s ∈ Icc d (c + l), deriv (signedCurvature α) s ≤ 0) : False := by
  have hl : 0 < l := by linarith
  have hkC := k_contDiff hα
  have hkd : ∀ s, HasDerivAt (signedCurvature α) (deriv (signedCurvature α) s) s :=
    fun s => ((hkC.differentiable (by simp)) s).hasDerivAt
  obtain ⟨s0, hs0, hs0eq⟩ := exists_deriv_eq_slope (signedCurvature α) hcd
    hkC.continuous.continuousOn (fun x _ => (hkd x).differentiableAt.differentiableWithinAt)
  have hs0pos : 0 < deriv (signedCurvature α) s0 := by
    rw [hs0eq]; exact div_pos (by linarith) (by linarith)
  have hσ := global_sigma hα hunit hconv (by
    by_contra hall; push Not at hall; linarith [hall c, hall d])
  have hcmem : c ∈ Ico c (c + l) := ⟨le_refl c, by linarith⟩
  have hdmem : d ∈ Ico c (c + l) := ⟨hcd.le, hdc⟩
  have hne : α c ≠ α d := hinj c hcmem d hdmem hcd.ne
  have hw : α d - α c ≠ 0 := sub_ne_zero.2 hne.symm
  have hc0 : hfun α (α c) (α d - α c) c = 0 := by simp [hfun]
  have hd0' : hfun α (α c) (α d - α c) d = 0 := by
    rw [hfun_eq]; simp only [PiLp.sub_apply]; ring
  have hcl0 : hfun α (α c) (α d - α c) (c + l) = 0 := by
    rw [hfun_per hper]; exact hc0
  have hnd : ¬ ((∀ u, 0 ≤ hfun α (α c) (α d - α c) u) ∨
      (∀ u, hfun α (α c) (α d - α c) u ≤ 0)) := by
    intro H
    obtain ⟨e1, e2⟩ := degen hα hunit hσ c d hne H
    linarith
  have hz : ∀ r, c < r → r < c + l → r ≠ d → hfun α (α c) (α d - α c) r ≠ 0 := by
    intro r hr1 hr2 hrd h0
    have hrmem : r ∈ Ico c (c + l) := ⟨hr1.le, hr2⟩
    exact hnd (three_pt hunit hconv (α c) (α d - α c) hw c d r hc0 hd0' h0 hne
      (hinj c hcmem r hrmem hr1.ne) (hinj d hdmem r hrmem hrd.symm))
  have hhc := hfun_cont hα (α c) (α d - α c)
  have sg1 := sign_Icc hhc hc0 hd0' (fun r hr => hz r hr.1 (by linarith [hr.2]) hr.2.ne)
  have sg2 := sign_Icc hhc hd0' hcl0 (fun r hr => hz r (by linarith [hr.1]) hr.2 hr.1.ne')
  have hglob : ∀ (P : ℝ → Prop), (∀ s ∈ Icc c (c + l), P (hfun α (α c) (α d - α c) s)) →
      ∀ u, P (hfun α (α c) (α d - α c) u) := by
    intro P hP u
    obtain ⟨y, hy, hyeq⟩ := (hfun_per hper (α c) (α d - α c)).exists_mem_Ico hl u c
    rw [hyeq]; exact hP y (Ico_subset_Icc_self hy)
  have hs0z : hfun α (α c) (α d - α c) s0 ≠ 0 := hz s0 hs0.1 (by linarith [hs0.2]) hs0.2.ne
  have hΦ : ∀ s, HasDerivAt (fun s => hfun α (α c) (α d - α c) s * signedCurvature α s +
      inner ℝ (deriv α s) (α d - α c))
      (hfun α (α c) (α d - α c) s * deriv (signedCurvature α) s) s := by
    intro s
    have h1 := (hfun_hasDeriv hα (α c) (α d - α c) s).mul (hkd s)
    have h2 := (hd1 hα s).inner ℝ (hasDerivAt_const s (α d - α c))
    rw [inner_zero_right, zero_add] at h2
    have h3 := h1.add h2
    have e : inner ℝ (deriv α s) (rot90 (α d - α c)) * signedCurvature α s +
        hfun α (α c) (α d - α c) s * deriv (signedCurvature α) s +
        inner ℝ (deriv (deriv α) s) (α d - α c) =
        hfun α (α c) (α d - α c) s * deriv (signedCurvature α) s := by
      rw [innerJ, inner_eq2, fx hα hunit, fy hα hunit]; ring
    rw [e] at h3
    exact h3
  have hΦper : (fun s => hfun α (α c) (α d - α c) s * signedCurvature α s +
      inner ℝ (deriv α s) (α d - α c)) c =
      (fun s => hfun α (α c) (α d - α c) s * signedCurvature α s +
      inner ℝ (deriv α s) (α d - α c)) (c + l) := by
    simp only [hfun_per hper (α c) (α d - α c) c, k_per hper c, per_deriv hper c]
  have hs0mem : s0 ∈ Ioo c (c + l) := ⟨hs0.1, by linarith [hs0.2]⟩
  rcases sg1 with A | A <;> rcases sg2 with B | B
  · exact hnd (Or.inl (hglob (fun x => 0 ≤ x) (fun s hs => by
      rcases le_total s d with h' | h'
      · exact A s ⟨hs.1, h'⟩
      · exact B s ⟨h', hs.2⟩)))
  · have := phi_lemma (by linarith : c < c + l) hΦ (fun s hs => by
      rcases le_total s d with h' | h'
      · nlinarith [A s ⟨hs.1, h'⟩, hk1 s ⟨hs.1, h'⟩]
      · nlinarith [B s ⟨h', hs.2⟩, hk2 s ⟨h', hs.2⟩]) hΦper s0 hs0mem
    rcases mul_eq_zero.1 this with h' | h'
    · exact hs0z h'
    · exact hs0pos.ne' h'
  · have := phi_lemma (by linarith : c < c + l) (fun s => (hΦ s).neg) (fun s hs => by
      rcases le_total s d with h' | h'
      · nlinarith [A s ⟨hs.1, h'⟩, hk1 s ⟨hs.1, h'⟩]
      · nlinarith [B s ⟨h', hs.2⟩, hk2 s ⟨h', hs.2⟩]) (congrArg Neg.neg hΦper) s0 hs0mem
    rcases mul_eq_zero.1 (neg_eq_zero.1 this) with h' | h'
    · exact hs0z h'
    · exact hs0pos.ne' h'
  · exact hnd (Or.inr (hglob (fun x => x ≤ 0) (fun s hs => by
      rcases le_total s d with h' | h'
      · exact A s ⟨hs.1, h'⟩
      · exact B s ⟨h', hs.2⟩)))

end Curve


theorem main (l : ℝ) (α : ℝ → E2) (halpha : IsSimpleClosedCurve l α)
    (hconv : IsConvexPlaneCurve α) :
    ∃ t₁ ∈ Set.Ico (0 : ℝ) l, ∃ t₂ ∈ Set.Ico (0 : ℝ) l, ∃ t₃ ∈ Set.Ico (0 : ℝ) l,
      ∃ t₄ ∈ Set.Ico (0 : ℝ) l,
        t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ ∧
        IsVertex α t₁ ∧ IsVertex α t₂ ∧ IsVertex α t₃ ∧ IsVertex α t₄ := by
  obtain ⟨⟨hl, hα, hper', hunit⟩, hsimple⟩ := halpha
  have hper : Function.Periodic α l := hper'
  simp only [IsVertex]
  have hkC := k_contDiff hα
  have hkd : ∀ s, HasDerivAt (signedCurvature α) (deriv (signedCurvature α) s) s :=
    fun s => ((hkC.differentiable (by simp)) s).hasDerivAt
  have hk'c : Continuous (deriv (signedCurvature α)) := hkC.continuous_deriv (by simp)
  have hkper := k_per hper
  have hk'per := per_deriv hkper
  by_cases hall : ∀ t, deriv (signedCurvature α) t = 0
  · refine ⟨0, ⟨le_refl 0, hl⟩, l / 4, ⟨by linarith, by linarith⟩, l / 2, ⟨by linarith, by linarith⟩,
      3 * l / 4, ⟨by linarith, by linarith⟩, ne_of_lt (by linarith), ne_of_lt (by linarith),
      ne_of_lt (by linarith), ne_of_lt (by linarith), ne_of_lt (by linarith),
      ne_of_lt (by linarith), hall _, hall _, hall _, hall _⟩
  push Not at hall
  -- a global minimum and a global maximum of the curvature, taken in [0, l)
  obtain ⟨a0, -, ha0⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hl.le)
    (hkC.continuous.continuousOn (s := Icc 0 l))
  have hamin0 : ∀ t, signedCurvature α a0 ≤ signedCurvature α t := by
    intro t
    obtain ⟨y, hy, hyeq⟩ := hkper.exists_mem_Ico₀ hl t
    rw [hyeq]; exact isMinOn_iff.1 ha0 y (Ico_subset_Icc_self hy)
  obtain ⟨a, ha, haeq⟩ := hkper.exists_mem_Ico₀ hl a0
  have hamin : ∀ t, signedCurvature α a ≤ signedCurvature α t := fun t => by
    rw [← haeq]; exact hamin0 t
  obtain ⟨b0, -, hb0⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hl.le)
    (hkC.continuous.continuousOn (s := Icc 0 l))
  have hbmax0 : ∀ t, signedCurvature α t ≤ signedCurvature α b0 := by
    intro t
    obtain ⟨y, hy, hyeq⟩ := hkper.exists_mem_Ico₀ hl t
    rw [hyeq]; exact isMaxOn_iff.1 hb0 y (Ico_subset_Icc_self hy)
  obtain ⟨b, hb, hbeq⟩ := hkper.exists_mem_Ico₀ hl b0
  have hbmax : ∀ t, signedCurvature α t ≤ signedCurvature α b := fun t => by
    rw [← hbeq]; exact hbmax0 t
  have hka : deriv (signedCurvature α) a = 0 :=
    IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall hamin)
  have hkb : deriv (signedCurvature α) b = 0 :=
    IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall hbmax)
  have hab : signedCurvature α a < signedCurvature α b := by
    rcases lt_or_eq_of_le (hamin b) with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := hall
      apply ht
      have hconst : signedCurvature α = fun _ => signedCurvature α a := by
        funext s; exact le_antisymm (by rw [h]; exact hbmax s) (hamin s)
      rw [hconst]; exact deriv_const t _
  have hab' : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  -- the maximum, placed in the window (a, a + l)
  obtain ⟨b', hb'1, hb'2, hkb', hbb'⟩ : ∃ b', a < b' ∧ b' < a + l ∧
      signedCurvature α b' = signedCurvature α b ∧ (b' = b ∨ b' = b + l) := by
    rcases lt_or_gt_of_ne hab' with h | h
    · exact ⟨b, h, by linarith [hb.2, ha.1], rfl, Or.inl rfl⟩
    · exact ⟨b + l, by linarith [hb.1, ha.2], by linarith, hkper b, Or.inr rfl⟩
  have hkb'd : deriv (signedCurvature α) b' = 0 := by
    rcases hbb' with h | h
    · rw [h]; exact hkb
    · rw [h, hk'per b]; exact hkb
  have ma : a ∈ Ico a (a + l) := ⟨le_refl a, by linarith⟩
  have mb' : b' ∈ Ico a (a + l) := ⟨hb'1.le, hb'2⟩
  have hata : hat l a = a := by unfold hat; rw [if_pos ha.2]
  have hatb : hat l b' = b := by
    unfold hat
    rcases hbb' with h | h
    · rw [if_pos (by rw [h]; exact hb.2), h]
    · rw [if_neg (by rw [h]; linarith [hb.1]), h]; ring
  have hinj : ∀ s ∈ Ico a (a + l), ∀ t ∈ Ico a (a + l), s ≠ t → α s ≠ α t := by
    intro s hs t ht hst heq
    exact hsimple _ (hat_mem ha hs) _ (hat_mem ha ht) (hat_inj hs ht hst)
      (by rw [hat_per hper, hat_per hper]; exact heq)
  by_cases two : ∃ r1 ∈ Ioo a (a + l), ∃ r2 ∈ Ioo a (a + l), r1 ≠ b' ∧ r2 ≠ b' ∧ r1 ≠ r2 ∧
      deriv (signedCurvature α) r1 = 0 ∧ deriv (signedCurvature α) r2 = 0
  · obtain ⟨r1, hr1, r2, hr2, n1, n2, n12, z1, z2⟩ := two
    have m1 : r1 ∈ Ico a (a + l) := Ioo_subset_Ico_self hr1
    have m2 : r2 ∈ Ico a (a + l) := Ioo_subset_Ico_self hr2
    refine ⟨a, ha, b, hb, hat l r1, hat_mem ha m1, hat l r2, hat_mem ha m2, hab', ?_, ?_, ?_, ?_,
      hat_inj m1 m2 n12, hka, hkb, by rw [hat_per hk'per]; exact z1,
      by rw [hat_per hk'per]; exact z2⟩
    · intro h; exact hat_inj m1 ma (ne_of_gt hr1.1) (by rw [hata]; exact h.symm)
    · intro h; exact hat_inj m2 ma (ne_of_gt hr2.1) (by rw [hata]; exact h.symm)
    · intro h; exact hat_inj m1 mb' n1 (by rw [hatb]; exact h.symm)
    · intro h; exact hat_inj m2 mb' n2 (by rw [hatb]; exact h.symm)
  · exfalso
    push Not at two
    have hone1 : ∀ r1 ∈ Ioo a b', ∀ r2 ∈ Ioo a b', deriv (signedCurvature α) r1 = 0 →
        deriv (signedCurvature α) r2 = 0 → r1 = r2 := by
      intro r1 h1 r2 h2 z1 z2
      by_contra hne
      exact two r1 ⟨h1.1, by linarith [h1.2]⟩ r2 ⟨h2.1, by linarith [h2.2]⟩ h1.2.ne h2.2.ne hne z1 z2
    have hone2 : ∀ r1 ∈ Ioo b' (a + l), ∀ r2 ∈ Ioo b' (a + l), -deriv (signedCurvature α) r1 = 0 →
        -deriv (signedCurvature α) r2 = 0 → r1 = r2 := by
      intro r1 h1 r2 h2 z1 z2
      by_contra hne
      exact two r1 ⟨by linarith [h1.1], h1.2⟩ r2 ⟨by linarith [h2.1], h2.2⟩ h1.1.ne' h2.1.ne' hne
        (neg_eq_zero.1 z1) (neg_eq_zero.1 z2)
    have S1 := sign_minmax hkd hk'c hamin (fun t => by rw [hkb']; exact hbmax t) hone1
    have S2 := sign_minmax (g := fun t => -signedCurvature α t)
      (g' := fun t => -deriv (signedCurvature α) t) (fun s => (hkd s).neg) hk'c.neg
      (fun t => by simp only [neg_le_neg_iff]; rw [hkb']; exact hbmax t)
      (fun t => by simp only [neg_le_neg_iff]; rw [hkper a]; exact hamin t) hone2
    refine key hα hunit hper hconv hb'1 hb'2 hinj (by rw [hkb']; exact hab) ?_ ?_
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact hka.ge
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · rw [h']; exact hkb'd.ge
      exact S1 s ⟨h, h'⟩
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact hkb'd.le
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · rw [h', hk'per a]; exact hka.le
      have := S2 s ⟨h, h'⟩
      linarith

end FourVertex

set_option maxHeartbeats 4000000 in
open DoCarmoDG in
theorem solution
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsSimpleClosedCurve l alpha)
    (hconv : IsConvexPlaneCurve alpha) :
    ∃ t₁ ∈ Set.Ico (0 : ℝ) l, ∃ t₂ ∈ Set.Ico (0 : ℝ) l, ∃ t₃ ∈ Set.Ico (0 : ℝ) l,
      ∃ t₄ ∈ Set.Ico (0 : ℝ) l,
        t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ ∧
        IsVertex alpha t₁ ∧ IsVertex alpha t₂ ∧ IsVertex alpha t₃ ∧ IsVertex alpha t₄ := by
  exact FourVertex.main l alpha halpha hconv
