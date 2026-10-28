-- Prove2me | solution 1 for EthierKurtz.kmt_permutation_bilinear_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T01:23:15.295063+00:00
-- url     : https://prove2.me/submissions/7665ad50-8ba1-42da-8cd7-cab4dd6e9783

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X11_Cr3

/-! R4 / Cr3: smoothed cumulant functions, saddle point, Legendre expansion.
`Ls G σ t = cgf t + t²σ²/2` (cgf of `G ∗ N(0,σ²)`), `L1s = Ls'`, `L2s = Ls''`.
* `L1s_mono`: `L1s` increases at rate `≥ 1/2` on `[-t1,t1]`; `saddle`: `L1s t = c` solvable for `|c| ≤ t1/2`, `|t| ≤ 2|c|`;
* `Ls_taylor`: Taylor bounds; `leg_at`: Legendre expansion of `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

end Cr3

end P99bcb804

end X11_Cr3

section X13_Nd1

/-! R4 / Nd1 (Q5 node, near region): ratio of the smoothed density at `N(c±δ)` to `N c`.
`near_ratio`: `f(N(c+δ)) f(N(c-δ)) = f(Nc)² exp(-Nδ²/L2s tc) exp(±K(1/√N + |δ| + N|δ|³))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

/-- density of the smoothed iid sum `Σ_ι G + N(0, card·σ²)` at `a`. -/
noncomputable def fS (G : Measure ℝ) (ι : Type) [Fintype ι] (σ a : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
    ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))

section Nd1

end Nd1

end P99bcb804

end X13_Nd1

section X23_Nd5

/-! R4 / Nd5: the standardised conditional density of the half-difference given the total.
`ffN x = fS(Nc + s x/2) fS(Nc - s x/2)`, `s = √(2N L2s tc)`, `hN = ffN / ZN`. Integrability,
`near_x` (near bounds in the `x` variable) and `ZN_low` (`ZN ≥ 2 fS(Nc)² e^{-1}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ tc : ℝ) : ℝ :=
  √(2 * Fintype.card ι * L2s G σ tc)

noncomputable def ffN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  fS G ι σ (Fintype.card ι * c + sN G ι σ tc * x / 2) *
    fS G ι σ (Fintype.card ι * c - sN G ι σ tc * x / 2)

noncomputable def ZN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc : ℝ) : ℝ :=
  ∫ x, ffN G ι σ c tc x

noncomputable def hN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  ffN G ι σ c tc x / ZN G ι σ c tc

section Nd5

variable {G : Measure ℝ} [IsProbabilityMeasure G]

end Nd5

end P99bcb804

end X23_Nd5

section X38_Cram2

/-! KMT 1976 II, Lemma B: the elementary estimates of the tilt parameter, cumulant and
variance, and the final two-sided combination. -/

open Real Finset

namespace P99bcb804

variable {N : ℕ}

lemma exp_neg_two_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) : exp (-(2 * r)) ≤ 1 - r := by
  have ha := add_one_le_exp (2 * r)
  have key : 1 ≤ (1 - r) * exp (2 * r) := by
    have := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 1 - r)
    nlinarith
  calc exp (-(2 * r)) ≤ exp (-(2 * r)) * ((1 - r) * exp (2 * r)) :=
        le_mul_of_one_le_right (exp_pos _).le key
    _ = 1 - r := by rw [mul_comm (1 - r), ← mul_assoc, ← exp_add]; simp

/-- Final combination: an additive error `r` relative to `ψ` plus two-sided log bounds. -/
lemma combine {P L0 ψu G x lo hi r T : ℝ} (hψ : 0 < ψu) (hG : 0 < G)
    (hP : |P - exp L0 * ψu| ≤ exp L0 * (r * ψu)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (hlo : G * exp (x ^ 2 / 2) * exp lo ≤ ψu) (hhi : ψu ≤ G * exp (x ^ 2 / 2) * exp hi)
    (hT1 : -T ≤ L0 + x ^ 2 / 2 + lo - 2 * r) (hT2 : L0 + x ^ 2 / 2 + hi + r ≤ T) :
    G * exp (-T) ≤ P ∧ P ≤ G * exp T := by
  rw [abs_le] at hP
  have hE := exp_pos L0
  constructor
  · have h1 : exp L0 * ψu * exp (-(2 * r)) ≤ exp L0 * ψu * (1 - r) :=
      mul_le_mul_of_nonneg_left (exp_neg_two_le hr0 hr1) (by positivity)
    have h2 : G * exp (x ^ 2 / 2) * exp lo * (exp L0 * exp (-(2 * r))) ≤
        ψu * (exp L0 * exp (-(2 * r))) := mul_le_mul_of_nonneg_right hlo (by positivity)
    have e : G * exp (x ^ 2 / 2) * exp lo * (exp L0 * exp (-(2 * r))) =
        G * exp (L0 + x ^ 2 / 2 + lo - 2 * r) := by
      rw [show L0 + x ^ 2 / 2 + lo - 2 * r = x ^ 2 / 2 + lo + (L0 + -(2 * r)) by ring,
        exp_add, exp_add, exp_add]; ring
    have h3 : G * exp (-T) ≤ G * exp (L0 + x ^ 2 / 2 + lo - 2 * r) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.2 hT1) hG.le
    nlinarith
  · have h1 : exp L0 * ψu * (1 + r) ≤ exp L0 * ψu * exp r :=
      mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp r]) (by positivity)
    have h2 : ψu * (exp L0 * exp r) ≤ G * exp (x ^ 2 / 2) * exp hi * (exp L0 * exp r) :=
      mul_le_mul_of_nonneg_right hhi (by positivity)
    have e : G * exp (x ^ 2 / 2) * exp hi * (exp L0 * exp r) =
        G * exp (L0 + x ^ 2 / 2 + hi + r) := by
      rw [show L0 + x ^ 2 / 2 + hi + r = x ^ 2 / 2 + hi + (L0 + r) by ring,
        exp_add, exp_add, exp_add]; ring
    have h3 : G * exp (L0 + x ^ 2 / 2 + hi + r) ≤ G * exp T :=
      mul_le_mul_of_nonneg_left (exp_le_exp.2 hT2) hG.le
    nlinarith

end P99bcb804

end X38_Cram2

section X40_L4

/-! KMT 1976 Part II, Lemma 4 (p.46): for `Σ aᵢ = 0`, `|aᵢ| ≤ A` and a uniformly random
permutation `w`, `E exp(t Σ aᵢ d_{w i}) ≤ exp(t² A² Σ dᵢ²)`.
Proof: swap-symmetrisation for balanced `{-1,0,1}` vectors (pairs `(i, e i)`), then
Krein–Milman + convexity (the extreme points of `{Σ b = 0, |bᵢ| ≤ 1}` are balanced, Lemma 5). -/

open Finset Real

namespace P99bcb804

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Swap-averaging step: `E e^{H + c} ≤ E e^{H + c²/2}` when `H` is swap invariant and `c` is
swap anti-invariant. -/
lemma swap_step (σ : Equiv.Perm α) (H c : Equiv.Perm α → ℝ)
    (hH : ∀ w, H (w * σ) = H w) (hc : ∀ w, c (w * σ) = -c w) :
    ∑ w, exp (H w + c w) ≤ ∑ w, exp (H w + c w ^ 2 / 2) := by
  have e1 : ∑ w, exp (H w + c w) = ∑ w, exp (H (w * σ) + c (w * σ)) :=
    (Equiv.sum_comp (Equiv.mulRight σ) (fun w => exp (H w + c w))).symm
  have e2 : ∑ w, exp (H w + c w) = ∑ w, exp (H w) * cosh (c w) := by
    have h2 : 2 * ∑ w, exp (H w + c w) = 2 * ∑ w, exp (H w) * cosh (c w) := by
      calc 2 * ∑ w, exp (H w + c w)
          = ∑ w, exp (H w + c w) + ∑ w, exp (H (w * σ) + c (w * σ)) := by rw [← e1]; ring
        _ = ∑ w, 2 * (exp (H w) * cosh (c w)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hH, hc, cosh_eq, exp_add, exp_add]; ring
        _ = 2 * ∑ w, exp (H w) * cosh (c w) := by rw [Finset.mul_sum]
    linarith
  rw [e2]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [exp_add]
  exact mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq _) (exp_pos _).le

/-- Pair-difference statistic `Σ_{i∈P} (d_{w i} - d_{w (e i)})`. -/
noncomputable def pairG (d : α → ℝ) (P : Finset α) (e : α → α)
    (w : Equiv.Perm α) : ℝ :=
  ∑ i ∈ P, (d (w i) - d (w (e i)))

/-- Its squared version. -/
noncomputable def pairW (d : α → ℝ) (P : Finset α) (e : α → α)
    (w : Equiv.Perm α) : ℝ :=
  ∑ i ∈ P, (d (w i) - d (w (e i))) ^ 2

/-- `e` pairs `P` injectively with positions outside `P`. -/
def IsPairing (P : Finset α) (e : α → α) : Prop :=
  (∀ i ∈ P, ∀ j ∈ P, e i ≠ j) ∧ (∀ i ∈ P, ∀ j ∈ P, e i = e j → i = j)

lemma pairing_mono {P : Finset α} {a : α} {e : α → α}
    (h : IsPairing (insert a P) e) : IsPairing P e :=
  ⟨fun i hi j hj => h.1 i (mem_insert_of_mem hi) j (mem_insert_of_mem hj),
    fun i hi j hj => h.2 i (mem_insert_of_mem hi) j (mem_insert_of_mem hj)⟩

lemma swap_fix {i a b : α} (hia : i ≠ a) (hib : i ≠ b) (w : Equiv.Perm α) :
    (w * Equiv.swap a b) i = w i := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hib]

theorem pair_mgf (d : α → ℝ) (e : α → α) (t : ℝ) (P : Finset α) :
    IsPairing P e → ∀ R : Equiv.Perm α → ℝ,
      (∀ i ∈ P, ∀ w, R (w * Equiv.swap i (e i)) = R w) →
      ∑ w, exp (t * pairG d P e w + R w) ≤ ∑ w, exp (t ^ 2 / 2 * pairW d P e w + R w) := by
  classical
  induction P using Finset.induction_on with
  | empty => intro _ R _; simp [pairG, pairW]
  | insert a P haP ih =>
    intro hp R hR
    have hp' := pairing_mono hp
    have ha : a ∈ insert a P := mem_insert_self a P
    have hea : e a ≠ a := hp.1 a ha a ha
    have hne : ∀ i ∈ P, i ≠ a ∧ i ≠ e a ∧ e i ≠ a ∧ e i ≠ e a := by
      intro i hi
      have hi' : i ∈ insert a P := mem_insert_of_mem hi
      refine ⟨fun h => haP (h ▸ hi), fun h => hp.1 a ha i hi' h.symm, hp.1 i hi' a ha,
        fun h => haP ((hp.2 i hi' a ha h) ▸ hi)⟩
    set c : Equiv.Perm α → ℝ := fun w => d (w a) - d (w (e a)) with hcdef
    have hG : ∀ w, pairG d (insert a P) e w = c w + pairG d P e w := fun w => by
      simp only [pairG, sum_insert haP, c]
    have hW : ∀ w, pairW d (insert a P) e w = c w ^ 2 + pairW d P e w := fun w => by
      simp only [pairW, sum_insert haP, c]
    have hc_inv : ∀ i ∈ P, ∀ w, c (w * Equiv.swap i (e i)) = c w := by
      intro i hi w
      obtain ⟨h1, h2, h3, h4⟩ := hne i hi
      simp only [c]
      rw [swap_fix (Ne.symm h1) (Ne.symm h3), swap_fix (Ne.symm h2) (Ne.symm h4)]
    have step1 := ih hp' (fun w => t * c w + R w) (fun i hi w => by
      rw [hc_inv i hi w, hR i (mem_insert_of_mem hi) w])
    have hW_inv : ∀ w, pairW d P e (w * Equiv.swap a (e a)) = pairW d P e w := by
      intro w
      unfold pairW
      refine sum_congr rfl fun i hi => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hne i hi
      rw [swap_fix h1 h2, swap_fix h3 h4]
    have step2 := swap_step (Equiv.swap a (e a)) (fun w => t ^ 2 / 2 * pairW d P e w + R w)
      (fun w => t * c w) (fun w => by rw [hW_inv, hR a ha]) (fun w => by
        simp only [c]
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        ring)
    calc ∑ w, exp (t * pairG d (insert a P) e w + R w)
        = ∑ w, exp (t * pairG d P e w + (t * c w + R w)) := by
          refine sum_congr rfl fun w _ => ?_; rw [hG]; congr 1; ring
      _ ≤ ∑ w, exp (t ^ 2 / 2 * pairW d P e w + (t * c w + R w)) := step1
      _ = ∑ w, exp ((t ^ 2 / 2 * pairW d P e w + R w) + t * c w) := by
          refine sum_congr rfl fun w _ => ?_; congr 1; ring
      _ ≤ ∑ w, exp ((t ^ 2 / 2 * pairW d P e w + R w) + (t * c w) ^ 2 / 2) := step2
      _ = ∑ w, exp (t ^ 2 / 2 * pairW d (insert a P) e w + R w) := by
          refine sum_congr rfl fun w _ => ?_; rw [hW]; congr 1; ring

lemma pairW_le (d : α → ℝ) {P : Finset α} {e : α → α} (hp : IsPairing P e)
    (w : Equiv.Perm α) : pairW d P e w ≤ 2 * ∑ i, d i ^ 2 := by
  classical
  have h1 : pairW d P e w ≤ ∑ i ∈ P, 2 * (d (w i) ^ 2 + d (w (e i)) ^ 2) := by
    unfold pairW
    exact sum_le_sum fun i _ => by nlinarith [sq_nonneg (d (w i) + d (w (e i)))]
  have hinj : Set.InjOn e P := by
    intro i hi j hj h; exact hp.2 i hi j hj h
  have h2 : ∑ i ∈ P, d (w (e i)) ^ 2 = ∑ j ∈ P.image e, d (w j) ^ 2 :=
    (sum_image (f := fun j => d (w j) ^ 2) hinj).symm
  have hdisj : Disjoint P (P.image e) := by
    rw [disjoint_left]
    intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj'
    exact hp.1 i hi (e i) hj rfl
  have h3 : ∑ j ∈ P ∪ P.image e, d (w j) ^ 2 ≤ ∑ j, d (w j) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  have h4 : ∑ j, d (w j) ^ 2 = ∑ i, d i ^ 2 := Equiv.sum_comp w (fun i => d i ^ 2)
  rw [sum_union hdisj, ← h2, h4] at h3
  calc pairW d P e w ≤ _ := h1
    _ = 2 * (∑ i ∈ P, d (w i) ^ 2 + ∑ i ∈ P, d (w (e i)) ^ 2) := by
      rw [← sum_add_distrib, mul_sum]
    _ ≤ _ := by linarith

theorem pair_mgf_bound (d : α → ℝ) {P : Finset α} {e : α → α}
    (hp : IsPairing P e) (t : ℝ) :
    ∑ w, exp (t * pairG d P e w) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * ∑ i, d i ^ 2) := by
  have h := pair_mgf d e t P hp (fun _ => 0) (fun _ _ _ => rfl)
  simp only [add_zero] at h
  refine h.trans ?_
  calc ∑ w, exp (t ^ 2 / 2 * pairW d P e w)
      ≤ ∑ _w : Equiv.Perm α, exp (t ^ 2 * ∑ i, d i ^ 2) := by
        refine sum_le_sum fun w _ => exp_le_exp.2 ?_
        have hw := pairW_le d hp w
        have ht : 0 ≤ t ^ 2 / 2 := by positivity
        nlinarith
    _ = _ := by simp

/-! ## Convexity / Krein–Milman reduction to balanced vectors. -/

/-- The permutation moment generating function as a function of the weight vector. -/
noncomputable def permF (t : ℝ) (d : α → ℝ) (b : α → ℝ) : ℝ :=
  ∑ w : Equiv.Perm α, exp (t * ∑ i, b i * d (w i))

/-- `{b : Σ b = 0, |bᵢ| ≤ 1}`. -/
def B1 (α : Type) [Fintype α] : Set (α → ℝ) :=
  {b | ∑ i, b i = 0} ∩ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

lemma isCompact_B1 : IsCompact (B1 α) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc).inter_left ?_
  exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma convex_B1 : Convex ℝ (B1 α) := by
  refine Convex.inter ?_ (convex_pi fun _ _ => convex_Icc _ _)
  intro x hx y hy a b _ _ _
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hx, hy]; ring

lemma permF_convex (t : ℝ) (d : α → ℝ) : ConvexOn ℝ Set.univ (permF t d) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [permF, smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  have h := convexOn_exp.2 (Set.mem_univ (t * ∑ i, x i * d (w i)))
    (Set.mem_univ (t * ∑ i, y i * d (w i))) ha hb hab
  simp only [smul_eq_mul] at h
  have hl : t * ∑ i, (a • x + b • y) i * d (w i)
      = a * (t * ∑ i, x i * d (w i)) + b * (t * ∑ i, y i * d (w i)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hl]; exact h

lemma continuous_permF (t : ℝ) (d : α → ℝ) : Continuous (permF t d) := by
  unfold permF; fun_prop

lemma mem_B1_abs {b : α → ℝ} (hb : b ∈ B1 α) (i : α) : |b i| ≤ 1 := by
  have := hb.2 i (Set.mem_univ i)
  exact abs_le.2 this

/-- Two coordinates strictly inside `(-1,1)` contradict extremality. -/
lemma ext_two {b : α → ℝ} (hb : b ∈ (B1 α).extremePoints ℝ) {i j : α} (hij : i ≠ j)
    (hi : |b i| < 1) (hj : |b j| < 1) : False := by
  rw [mem_extremePoints] at hb
  obtain ⟨hbB, hext⟩ := hb
  set δ := min (1 - |b i|) (1 - |b j|) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδi : δ ≤ 1 - |b i| := min_le_left _ _
  have hδj : δ ≤ 1 - |b j| := min_le_right _ _
  set v : α → ℝ := Pi.single i δ - Pi.single j δ with hvdef
  have hvi : v i = δ := by simp [v, hij]
  have hsum : ∑ k, v k = 0 := by simp [v, sum_sub_distrib]
  have mem : ∀ s : ℝ, |s| ≤ 1 → b + s • v ∈ B1 α := by
    intro s hs
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_add_distrib, ← mul_sum, hsum, hbB.1]; ring
    · intro k _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Set.mem_Icc, ← abs_le]
      have hsδ : |s * δ| ≤ δ := by
        rw [abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg s]
      by_cases hki : k = i
      · subst hki
        rw [hvi]
        calc |b k + s * δ| ≤ |b k| + |s * δ| := abs_add_le _ _
          _ ≤ 1 := by linarith
      · by_cases hkj : k = j
        · subst hkj
          have hvj : v k = -δ := by simp [v, hki]
          rw [hvj]
          calc |b k + s * -δ| ≤ |b k| + |s * -δ| := abs_add_le _ _
            _ ≤ 1 := by rw [mul_neg, abs_neg]; linarith
        · have hvk : v k = 0 := by simp [v, hki, hkj]
          rw [hvk, mul_zero, add_zero]; exact mem_B1_abs hbB k
  have h1 := mem 1 (by norm_num)
  have h2 := mem (-1) (by norm_num)
  have hseg : b ∈ openSegment ℝ (b + (1 : ℝ) • v) (b + (-1 : ℝ) • v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (hext _ h1 _ h2 hseg).1
  have hv0 : v i = 0 := by
    have := congrFun this i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this
    linarith
  rw [hvi] at hv0
  exact hδ.ne' hv0

/-- Extreme points of `B1` have coordinates in `{-1, 0, 1}` (KMT Lemma 5). -/
lemma ext_vals {b : α → ℝ} (hb : b ∈ (B1 α).extremePoints ℝ) (i : α) :
    b i = 1 ∨ b i = -1 ∨ b i = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hbB := hb.1
  have hi : |b i| < 1 := by
    have := mem_B1_abs hbB i
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · rcases abs_eq (zero_le_one) |>.1 h with h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
  have hother : ∀ j, j ≠ i → b j = 1 ∨ b j = -1 := by
    intro j hj
    have hj1 := mem_B1_abs hbB j
    rcases lt_or_eq_of_le hj1 with h | h
    · exact (ext_two hb hj h hi).elim
    · exact abs_eq zero_le_one |>.1 h
  have hsum : b i + ∑ j ∈ univ.erase i, b j = 0 := by
    rw [add_sum_erase _ _ (mem_univ i)]; exact hbB.1
  have hint : ∑ j ∈ univ.erase i, b j ∈ (Int.castAddHom ℝ).range := by
    refine AddSubgroup.sum_mem _ fun j hj => ?_
    rcases hother j (ne_of_mem_erase hj) with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  obtain ⟨n, hn⟩ := hint
  simp only [Int.coe_castAddHom] at hn
  have hbi : b i = -(n : ℝ) := by linarith
  rw [hbi, abs_neg] at hi
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hi
    rw [abs_lt] at this; omega
  rw [hbi, hn0] at h3
  simp at h3

/-- A balanced `{-1,0,1}` vector is a pair-difference statistic. -/
lemma balanced_pairG (d : α → ℝ) (b : α → ℝ)
    (hv : ∀ i, b i = 1 ∨ b i = -1 ∨ b i = 0) (hs : ∑ i, b i = 0) :
    ∃ (P : Finset α) (e : α → α), IsPairing P e ∧
      ∀ w : Equiv.Perm α, ∑ i, b i * d (w i) = pairG d P e w := by
  classical
  set P := univ.filter (fun i => b i = 1) with hP
  set Q := univ.filter (fun i => b i = -1) with hQ
  have hpt : ∀ i (x : ℝ), b i * x = (if b i = 1 then x else 0) - (if b i = -1 then x else 0) := by
    intro i x
    rcases hv i with h | h | h <;> simp [h] <;> norm_num
  have hcard : P.card = Q.card := by
    have h := hs
    have : ∑ i, b i = (P.card : ℝ) - (Q.card : ℝ) := by
      rw [show (∑ i, b i) = ∑ i, b i * 1 by simp]
      simp_rw [hpt _ (1 : ℝ)]
      rw [sum_sub_distrib, ← sum_filter, ← sum_filter]
      simp [P, Q]
    rw [this] at h
    have : (P.card : ℝ) = Q.card := by linarith
    exact_mod_cast this
  have hcardT : Fintype.card {x // x ∈ P} = Fintype.card {x // x ∈ Q} := by
    simp [Fintype.card_coe, hcard]
  set eqv := Fintype.equivOfCardEq hcardT
  let e : α → α := fun i => if h : i ∈ P then (eqv ⟨i, h⟩ : α) else i
  have heP : ∀ i (h : i ∈ P), e i = (eqv ⟨i, h⟩ : α) := fun i h => by simp [e, h]
  have heQ : ∀ i ∈ P, e i ∈ Q := fun i h => by rw [heP i h]; exact (eqv ⟨i, h⟩).2
  have hPQ : ∀ j, j ∈ P → j ∈ Q → False := by
    intro j hjP hjQ
    simp only [P, Q, mem_filter, mem_univ, true_and] at hjP hjQ
    rw [hjP] at hjQ; norm_num at hjQ
  refine ⟨P, e, ⟨fun i hi j hj h => hPQ j hj (h ▸ heQ i hi), fun i hi j hj h => ?_⟩, ?_⟩
  · rw [heP i hi, heP j hj] at h
    have := eqv.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro w
    have hsplit : ∑ i, b i * d (w i) = ∑ i ∈ P, d (w i) - ∑ i ∈ Q, d (w i) := by
      simp_rw [hpt]
      rw [sum_sub_distrib, ← sum_filter, ← sum_filter]
    have hQsum : ∑ i ∈ Q, d (w i) = ∑ i ∈ P, d (w (e i)) := by
      symm
      refine Finset.sum_bij (fun i _ => e i) (fun i hi => heQ i hi) ?_ ?_ (fun _ _ => rfl)
      · intro i hi j hj h
        rw [heP i hi, heP j hj] at h
        exact congrArg Subtype.val (eqv.injective (Subtype.ext h))
      · intro j hj
        refine ⟨(eqv.symm ⟨j, hj⟩ : α), (eqv.symm ⟨j, hj⟩).2, ?_⟩
        rw [heP _ (eqv.symm ⟨j, hj⟩).2]
        simp
    rw [hsplit, hQsum, pairG, sum_sub_distrib]

lemma permF_ext (d : α → ℝ) (t : ℝ) {b : α → ℝ} (hb : b ∈ (B1 α).extremePoints ℝ) :
    permF t d b ≤ (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * ∑ i, d i ^ 2) := by
  obtain ⟨P, e, hp, hG⟩ := balanced_pairG d b (ext_vals hb) hb.1.1
  unfold permF
  simp_rw [hG]
  exact pair_mgf_bound d hp t

theorem permF_B1 (d : α → ℝ) (t : ℝ) {b : α → ℝ} (hb : b ∈ B1 α) :
    permF t d b ≤ (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * ∑ i, d i ^ 2) := by
  have hK := closure_convexHull_extremePoints (isCompact_B1 (α := α)) convex_B1
  have hclosed : IsClosed {x | permF t d x ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * ∑ i, d i ^ 2)} :=
    isClosed_le (continuous_permF t d) continuous_const
  have hsub : convexHull ℝ ((B1 α).extremePoints ℝ) ⊆ {x | permF t d x ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * ∑ i, d i ^ 2)} := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (permF_convex t d).exists_ge_of_mem_convexHull (Set.subset_univ _) hx
    exact hxy.trans (permF_ext d t hy)
  rw [← hK] at hb
  exact closure_minimal hsub hclosed hb

/-- **KMT 1976 Part II, Lemma 4** (summed form): for `Σ aᵢ = 0`, `|aᵢ| ≤ A`,
`Σ_w exp(t Σ aᵢ d_{w i}) ≤ N! · exp(t² A² Σ dᵢ²)`. -/
theorem perm_mgf (d a : α → ℝ) {A : ℝ} (hA : 0 ≤ A) (hs : ∑ i, a i = 0)
    (ha : ∀ i, |a i| ≤ A) (t : ℝ) :
    ∑ w : Equiv.Perm α, exp (t * ∑ i, a i * d (w i)) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * A ^ 2 * ∑ i, d i ^ 2) := by
  rcases eq_or_lt_of_le hA with h0 | hpos
  · have ha0 : ∀ i, a i = 0 := fun i => by
      have := ha i; rw [← h0] at this; exact abs_nonpos_iff.1 this
    simp [ha0, ← h0]
  · set b : α → ℝ := fun i => a i / A with hbdef
    have hb : b ∈ B1 α := by
      refine ⟨?_, fun i _ => ?_⟩
      · simp only [Set.mem_ofPred_eq, b]; rw [← sum_div, hs, zero_div]
      · show b i ∈ Set.Icc (-1) 1
        rw [Set.mem_Icc, ← abs_le]; simp only [b, abs_div, abs_of_pos hpos]
        rw [div_le_one hpos]; exact ha i
    have h := permF_B1 d (t * A) hb
    unfold permF at h
    have hl : ∀ w : Equiv.Perm α, t * A * ∑ i, b i * d (w i) = t * ∑ i, a i * d (w i) := by
      intro w
      simp only [b]
      rw [mul_assoc, mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      field_simp
    simp_rw [hl] at h
    refine h.trans (le_of_eq ?_)
    congr 2; ring

/-! ## The quadratic exponential bound ("consequently" part of Lemma 4). -/

open MeasureTheory ProbabilityTheory in
lemma pdf_mul_exp_sq' (l x : ℝ) :
    gaussianPDFReal 0 1 x * exp (l * x ^ 2) = (√(2 * π))⁻¹ * exp (-(1 / 2 - l) * x ^ 2) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

open MeasureTheory ProbabilityTheory in
/-- Exponential moment of a squared standard Gaussian. -/
theorem gauss_sq_mgf' {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => exp (l * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, exp (l * x ^ 2) ∂gaussianReal 0 1 = (√(1 - 2 * l))⁻¹ := by
  have hb : 0 < 1 / 2 - l := by linarith
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have : (fun x => (gaussianPDF 0 1 x).toReal • exp (l * x ^ 2)) =
        fun x => (√(2 * π))⁻¹ * exp (-(1 / 2 - l) * x ^ 2) := by
      funext x
      rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul,
        pdf_mul_exp_sq']
    rw [this]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, pdf_mul_exp_sq']
    rw [integral_const_mul, integral_gaussian]
    have h1 : 0 < 1 - 2 * l := by linarith
    have e : π / (1 / 2 - l) = 2 * π / (1 - 2 * l) := by field_simp
    rw [e, Real.sqrt_div' _ h1.le]
    have h2 : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have h3 : 0 < √(1 - 2 * l) := Real.sqrt_pos.mpr h1
    field_simp

open MeasureTheory ProbabilityTheory in
/-- A sub-Gaussian moment generating function bound `Σ e^{tX} ≤ C e^{t² D}` gives
`Σ e^{u X²/D} ≤ C (1-4u)^{-1/2}` for `0 ≤ u < 1/4` (Gaussian linearisation). -/
theorem sq_exp_of_mgf {ι : Type} [Fintype ι] (X : ι → ℝ) {D C : ℝ} (hD : 0 < D)
    (hmgf : ∀ t : ℝ, ∑ i, exp (t * X i) ≤ C * exp (t ^ 2 * D)) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) :
    ∑ i, exp (u * X i ^ 2 / D) ≤ C * (√(1 - 4 * u))⁻¹ := by
  set s := √(2 * u / D) with hs
  have hs2 : s ^ 2 = 2 * u / D := Real.sq_sqrt (by positivity)
  have hlin : ∀ i, exp (u * X i ^ 2 / D) = ∫ z, exp ((s * X i) * z) ∂gaussianReal 0 1 := by
    intro i
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (s * X i)
    simp only [mgf, id, zero_mul, zero_add, NNReal.coe_one, one_mul] at h
    rw [h]; congr 1
    rw [mul_pow, hs2]; field_simp
  have hint : ∀ i, Integrable (fun z => exp ((s * X i) * z)) (gaussianReal 0 1) := fun i =>
    integrable_exp_mul_gaussianReal (s * X i)
  have hq := gauss_sq_mgf' (l := 2 * u) (by linarith)
  calc ∑ i, exp (u * X i ^ 2 / D) = ∑ i, ∫ z, exp ((s * X i) * z) ∂gaussianReal 0 1 :=
        Finset.sum_congr rfl fun i _ => hlin i
    _ = ∫ z, ∑ i, exp ((s * z) * X i) ∂gaussianReal 0 1 := by
        rw [← integral_finsetSum _ fun i _ => hint i]
        congr 1; funext z; exact Finset.sum_congr rfl fun i _ => by ring_nf
    _ ≤ ∫ z, C * exp ((2 * u) * z ^ 2) ∂gaussianReal 0 1 := by
        refine integral_mono (integrable_finsetSum _ fun i _ => ?_) (hq.1.const_mul C) fun z => ?_
        · simpa [mul_comm, mul_left_comm, mul_assoc] using hint i
        · refine (hmgf (s * z)).trans (le_of_eq ?_)
          congr 2
          rw [mul_pow, hs2]; field_simp
    _ = C * (√(1 - 4 * u))⁻¹ := by
        rw [integral_const_mul, hq.2]; congr 3; ring

/-- **KMT 1976 Part II, Lemma 4, second part**: with `D = A² Σ dᵢ²`,
`Σ_w exp(u (Σ aᵢ d_{w i})² / D) ≤ N! (1-4u)^{-1/2}` for `0 ≤ u < 1/4`. -/
theorem perm_sq_exp (d a : α → ℝ) {A : ℝ} (hA : 0 ≤ A) (hs : ∑ i, a i = 0)
    (ha : ∀ i, |a i| ≤ A) (hD : 0 < A ^ 2 * ∑ i, d i ^ 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) :
    ∑ w : Equiv.Perm α, exp (u * (∑ i, a i * d (w i)) ^ 2 / (A ^ 2 * ∑ i, d i ^ 2)) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * (√(1 - 4 * u))⁻¹ := by
  have hm : ∀ t : ℝ, ∑ w : Equiv.Perm α, exp (t * ∑ i, a i * d (w i)) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) * exp (t ^ 2 * (A ^ 2 * ∑ i, d i ^ 2)) := by
    intro t
    have h := perm_mgf d a hA hs ha t
    rw [mul_assoc (t ^ 2)] at h
    exact h
  exact sq_exp_of_mgf (fun w : Equiv.Perm α => ∑ i, a i * d (w i)) hD hm hu0 hu

/-! ## KMT (4.9): the cross-product statistic `η` is sub-Gaussian. Population indexed by
`Fin N ⊕ Fin N` (first half `inl`, second half `inr`). -/

/-- `η = -(1/√N) Σᵢ x_{w(inl i)} x_{w(inr i)}` (KMT 1976 II, p.44, with `Σ x = 0`). -/
noncomputable def etaV {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  -(1 / √(N : ℝ)) * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))

lemma inv_sqrt_le_exp {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) : (√(1 - 4 * u))⁻¹ ≤ exp (4 * u) := by
  set v := 4 * u with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 / 2 := by linarith
  have hpos : 0 < √(1 - v) := Real.sqrt_pos.2 (by linarith)
  have h1 : 1 ≤ (1 - v) * exp (2 * v) := by nlinarith [add_one_le_exp (2 * v)]
  have h2 : √(1 - v) * exp v = √((1 - v) * exp (2 * v)) := by
    rw [Real.sqrt_mul (by linarith), show exp (2 * v) = exp v ^ 2 by rw [← exp_nat_mul]; ring_nf,
      Real.sqrt_sq (exp_pos v).le]
  have h3 : 1 ≤ √(1 - v) * exp v := by
    rw [h2]; calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith

lemma sum_sq_le {β : Type} [Fintype β] (y : β → ℝ) {K : ℝ} (hy : ∀ i, |y i| ≤ K) :
    ∑ i, y i ^ 2 ≤ Fintype.card β * K ^ 2 := by
  calc ∑ i, y i ^ 2 ≤ ∑ _i : β, K ^ 2 := sum_le_sum fun i _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy i) 2
    _ = _ := by simp

/-- **KMT 1976 II, (4.9)** (with explicit constant): for `Σ x = 0`, `|xᵢ| ≤ K`,
`1/√N ≤ |t| ≤ √N/(16K²)`: `E e^{tη} ≤ exp((2K² + 4K⁴) t²)`. -/
theorem eta_mgf {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (t : ℝ) (ht1 : 1 ≤ |t| * √(N : ℝ))
    (ht2 : |t| * (16 * K ^ 2) ≤ √(N : ℝ)) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (t * etaV x w) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp ((2 * K ^ 2 + 4 * K ^ 4) * t ^ 2) := by
  classical
  set n : ℝ := (N : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast hN
  set r := √n with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn.le
  set cN : ℝ := (Fintype.card (Equiv.Perm (Fin N)) : ℝ) with hcN
  set cA : ℝ := (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) with hcA
  have hcN0 : 0 < cN := by rw [hcN]; exact_mod_cast Fintype.card_pos
  set Sb : Equiv.Perm (Fin N ⊕ Fin N) → ℝ := fun w => ∑ i, x (w (Sum.inl i)) with hSb
  -- inner bound, for a fixed first half
  have inner : ∀ w : Equiv.Perm (Fin N ⊕ Fin N),
      ∑ τ : Equiv.Perm (Fin N), exp (t * etaV x (w * Equiv.sumCongr 1 τ)) ≤
        exp (t * Sb w ^ 2 / (n * r)) * (cN * exp (4 * K ^ 4 * t ^ 2)) := by
    intro w
    set b : Fin N → ℝ := fun i => x (w (Sum.inl i)) with hb
    set y : Fin N → ℝ := fun j => x (w (Sum.inr j)) with hy
    have hsum0 : ∑ i, b i + ∑ j, y j = 0 := by
      have h1 : ∑ a, x (w a) = ∑ a, x a := Equiv.sum_comp w x
      rw [Fintype.sum_sum_type] at h1
      rw [h1, hs]
    set a : Fin N → ℝ := fun i => (∑ k, b k) / n - b i with ha
    have hcard : (Fintype.card (Fin N) : ℝ) = n := by simp [hndef]
    have hasum : ∑ i, a i = 0 := by
      simp only [a, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]
      field_simp; ring
    have habs : ∀ i, |a i| ≤ 2 * K := by
      intro i
      have hbK : ∀ k, |b k| ≤ K := fun k => hx _
      have hmean : |(∑ k, b k) / n| ≤ K := by
        rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
        calc |∑ k, b k| ≤ ∑ k, |b k| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : Fin N, K := sum_le_sum fun k _ => hbK k
          _ = K * n := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]; ring
      calc |a i| ≤ |(∑ k, b k) / n| + |b i| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hbK i]
    have heta : ∀ τ : Equiv.Perm (Fin N), t * etaV x (w * Equiv.sumCongr 1 τ)
        = t * Sb w ^ 2 / (n * r) + t / r * ∑ i, a i * y (τ i) := by
      intro τ
      have hyτ : ∑ i, y (τ i) = ∑ j, y j := Equiv.sum_comp τ y
      have key : ∑ i, b i * y (τ i) = -(∑ k, b k) ^ 2 / n - ∑ i, a i * y (τ i) := by
        have : ∑ i, a i * y (τ i) = (∑ k, b k) / n * ∑ i, y (τ i) - ∑ i, b i * y (τ i) := by
          simp only [a, sub_mul, sum_sub_distrib, mul_sum]
        rw [this, hyτ]
        have hy' : ∑ j, y j = -∑ k, b k := by linarith
        rw [hy']; field_simp; ring
      have hev : etaV x (w * Equiv.sumCongr 1 τ) = -(1 / r) * ∑ i, b i * y (τ i) := by
        simp [etaV, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, b, y, hrdef, hndef]
      rw [hev, key]
      simp only [Sb]
      field_simp
      ring
    simp_rw [heta, exp_add]
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
    have hpm := perm_mgf y a (by linarith : (0 : ℝ) ≤ 2 * K) hasum habs (t / r)
    refine hpm.trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hcN0.le)
    have hy2 : ∑ i, y i ^ 2 ≤ n * K ^ 2 := by
      have := sum_sq_le y (fun j => hx (w (Sum.inr j))); rwa [hcard] at this
    have e1 : (t / r) ^ 2 = t ^ 2 / n := by rw [div_pow, hr2]
    rw [e1]
    have ht2' : 0 ≤ t ^ 2 / n * (2 * K) ^ 2 := by positivity
    calc t ^ 2 / n * (2 * K) ^ 2 * ∑ i, y i ^ 2 ≤ t ^ 2 / n * (2 * K) ^ 2 * (n * K ^ 2) :=
          mul_le_mul_of_nonneg_left hy2 ht2'
      _ = 4 * K ^ 4 * t ^ 2 := by field_simp; ring
  -- averaging over the second-half rearrangements
  have avg : cN * ∑ w, exp (t * etaV x w) =
      ∑ w, ∑ τ : Equiv.Perm (Fin N), exp (t * etaV x (w * Equiv.sumCongr 1 τ)) := by
    rw [sum_comm, hcN, ← nsmul_eq_mul, ← card_univ, ← sum_const]
    refine sum_congr rfl fun τ _ => ?_
    exact (Equiv.sum_comp (Equiv.mulRight (Equiv.sumCongr 1 τ)) (fun w => exp (t * etaV x w))).symm
  -- outer bound
  have outer : ∑ w, exp (t * Sb w ^ 2 / (n * r)) ≤ cA * exp (2 * K ^ 2 * t ^ 2) := by
    rcases le_or_gt t 0 with htn | htp
    · calc ∑ w, exp (t * Sb w ^ 2 / (n * r)) ≤ ∑ _w : Equiv.Perm (Fin N ⊕ Fin N), (1 : ℝ) :=
            sum_le_sum fun w _ => by
              rw [exp_le_one_iff]
              exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg htn (sq_nonneg _))
                (by positivity)
        _ = cA := by simp [hcA]
        _ ≤ cA * exp (2 * K ^ 2 * t ^ 2) := by
            have : 0 ≤ cA := by positivity
            nlinarith [one_le_exp (by positivity : (0 : ℝ) ≤ 2 * K ^ 2 * t ^ 2)]
    · have htabs : |t| = t := abs_of_pos htp
      rw [htabs] at ht1 ht2
      set S2 := ∑ i, x i ^ 2 with hS2
      have hS2le : S2 ≤ 2 * n * K ^ 2 := by
        have := sum_sq_le x hx
        simp only [Fintype.card_sum, Fintype.card_fin] at this
        rw [hndef]; push_cast at this; linarith
      rcases eq_or_lt_of_le (sum_nonneg fun i _ => sq_nonneg (x i) : (0 : ℝ) ≤ S2) with h0 | hS2p
      · have hx0 : ∀ i, x i = 0 := by
          intro i
          have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i)).1 h0.symm i (mem_univ i)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        have : ∀ w, Sb w = 0 := fun w => by simp [Sb, hx0]
        simp only [this]
        simp [hcA]
        nlinarith [one_le_exp (by positivity : (0 : ℝ) ≤ 2 * K ^ 2 * t ^ 2),
          (by positivity : (0 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ))]
      · set a' : Fin N ⊕ Fin N → ℝ := Sum.elim (fun _ => 1 / 2) (fun _ => -(1 / 2)) with ha'
        have ha's : ∑ i, a' i = 0 := by simp [a', Fintype.sum_sum_type]
        have ha'b : ∀ i, |a' i| ≤ 1 / 2 := by
          intro i; cases i <;> simp [a'] <;> norm_num
        have hSb : ∀ w : Equiv.Perm (Fin N ⊕ Fin N), ∑ i, a' i * x (w i) = Sb w := by
          intro w
          have h1 : ∑ a, x (w a) = ∑ a, x a := Equiv.sum_comp w x
          rw [Fintype.sum_sum_type, hs] at h1
          rw [Fintype.sum_sum_type]
          simp only [a', Sum.elim_inl, Sum.elim_inr, Sb]
          rw [← mul_sum]
          have e : ∑ a₂, -(1 / 2 : ℝ) * x (w (Sum.inr a₂)) = -(1 / 2) * ∑ a₂, x (w (Sum.inr a₂)) := by
            rw [mul_sum]
          rw [e]
          linarith
        set D := (1 / 2 : ℝ) ^ 2 * S2 with hD
        have hDp : 0 < D := by positivity
        set u := t * D / (n * r) with hu
        have hu0 : 0 ≤ u := by positivity
        have hu8 : u ≤ 1 / 8 := by
          rw [hu, div_le_iff₀ (by positivity)]
          have : t * D ≤ t * (n * K ^ 2 / 2) := by
            apply mul_le_mul_of_nonneg_left _ htp.le; rw [hD]; nlinarith
          have h16 : t * K ^ 2 ≤ r / 16 := by nlinarith
          nlinarith [mul_pos hn hr]
        have hpq := perm_sq_exp x a' (by norm_num : (0 : ℝ) ≤ 1 / 2) ha's ha'b hDp hu0
          (by linarith)
        have hterm : ∀ w, exp (t * Sb w ^ 2 / (n * r)) =
            exp (u * (∑ i, a' i * x (w i)) ^ 2 / ((1 / 2) ^ 2 * ∑ i, x i ^ 2)) := by
          intro w; rw [hSb w]; congr 1
          have hD0 : D ≠ 0 := hDp.ne'
          change t * Sb w ^ 2 / (n * r) = u * Sb w ^ 2 / D
          rw [hu]; field_simp
        simp_rw [hterm]
        refine hpq.trans (mul_le_mul_of_nonneg_left ((inv_sqrt_le_exp hu0 hu8).trans
          (exp_le_exp.2 ?_)) (by positivity))
        -- 4u ≤ 2K² t²
        have h4u : 4 * u ≤ 2 * K ^ 2 * t / r := by
          have e : 4 * u = t * S2 / n / r := by rw [hu, hD]; field_simp; ring
          rw [e]
          apply div_le_div_of_nonneg_right _ hr.le
          rw [div_le_iff₀ hn]
          nlinarith [mul_le_mul_of_nonneg_left hS2le htp.le]
        have htr : t / r ≤ t ^ 2 := by
          rw [div_le_iff₀ hr]; nlinarith
        have hm := mul_le_mul_of_nonneg_left htr (by positivity : (0 : ℝ) ≤ 2 * K ^ 2)
        have e2 : 2 * K ^ 2 * t / r = 2 * K ^ 2 * (t / r) := by ring
        linarith
  -- combine
  have hfin : cN * ∑ w, exp (t * etaV x w) ≤ cN * (cA * exp ((2 * K ^ 2 + 4 * K ^ 4) * t ^ 2)) := by
    rw [avg]
    calc ∑ w, ∑ τ : Equiv.Perm (Fin N), exp (t * etaV x (w * Equiv.sumCongr 1 τ))
        ≤ ∑ w, exp (t * Sb w ^ 2 / (n * r)) * (cN * exp (4 * K ^ 4 * t ^ 2)) :=
          sum_le_sum fun w _ => inner w
      _ = (∑ w, exp (t * Sb w ^ 2 / (n * r))) * (cN * exp (4 * K ^ 4 * t ^ 2)) := by
          rw [sum_mul]
      _ ≤ (cA * exp (2 * K ^ 2 * t ^ 2)) * (cN * exp (4 * K ^ 4 * t ^ 2)) :=
          mul_le_mul_of_nonneg_right outer (by positivity)
      _ = cN * (cA * exp ((2 * K ^ 2 + 4 * K ^ 4) * t ^ 2)) := by
          rw [show (2 * K ^ 2 + 4 * K ^ 4) * t ^ 2 = 2 * K ^ 2 * t ^ 2 + 4 * K ^ 4 * t ^ 2 by ring,
            exp_add]; ring
  exact le_of_mul_le_mul_left hfin hcN0

/-! ## KMT (4.10): `E e^{v η²} ≤ e^{C v}` for small `v`, uniformly in `N`. -/

end P99bcb804

end X40_L4

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {N : ℕ},
      (1 : ℕ) ≤ N →
        ∀ (x : Fin N ⊕ Fin N → ℝ) {K : ℝ},
          (0 : ℝ) < K →
            (∀ (i : Fin N ⊕ Fin N), |x i| ≤ K) →
              ∑ i : Fin N ⊕ Fin N, x i = (0 : ℝ) →
                ∀ (t : ℝ),
                  (1 : ℝ) ≤ |t| * √↑N →
                    |t| * ((16 : ℝ) * K ^ (2 : ℕ)) ≤ √↑N →
                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N),
                          Real.exp (t * (-((1 : ℝ) / √↑N) * ∑ i : Fin N, x (w (Sum.inl i)) * x (w (Sum.inr i)))) ≤
                        ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                          Real.exp (((2 : ℝ) * K ^ (2 : ℕ) + (4 : ℝ) * K ^ (4 : ℕ)) * t ^ (2 : ℕ)) := by
  first
  | exact P99bcb804.eta_mgf
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.eta_mgf <;> assumption)
