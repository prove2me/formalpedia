-- Prove2me | solution 1 for BigDataNV.Reg.theorem4_uniform_stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:27:28.802819+00:00
-- url     : https://prove2.me/submissions/bb040ee7-4a73-48bd-adb0-9054ac4db83a

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting



namespace BigDataNV.Reg

lemma th4_cost_eq (b h q d : ℝ) : nvCost b h q d = h * max (q - d) 0 + b * max (d - q) 0 := rfl

lemma th4_max_cvx (u v t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max ((1 - t) * u + t * v) 0 ≤ (1 - t) * max u 0 + t * max v 0 := by
  have h1 : 0 ≤ 1 - t := by linarith
  refine max_le ?_ ?_
  · have a1 := mul_le_mul_of_nonneg_left (le_max_left u 0) h1
    have a2 := mul_le_mul_of_nonneg_left (le_max_left v 0) ht0
    linarith
  · exact add_nonneg (mul_nonneg h1 (le_max_right _ _)) (mul_nonneg ht0 (le_max_right _ _))

lemma th4_cost_cvx (b h d a a' t : ℝ) (hb : 0 < b) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nvCost b h ((1 - t) * a + t * a') d ≤ (1 - t) * nvCost b h a d + t * nvCost b h a' d := by
  rw [th4_cost_eq, th4_cost_eq, th4_cost_eq]
  have e1 : (1 - t) * a + t * a' - d = (1 - t) * (a - d) + t * (a' - d) := by ring
  have e2 : d - ((1 - t) * a + t * a') = (1 - t) * (d - a) + t * (d - a') := by ring
  rw [e1, e2]
  have c1 := th4_max_cvx (a - d) (a' - d) t ht0 ht1
  have c2 := th4_max_cvx (d - a) (d - a') t ht0 ht1
  nlinarith [mul_le_mul_of_nonneg_left c1 hh.le, mul_le_mul_of_nonneg_left c2 hb.le]

lemma th4_cost_lip (b h d a a' : ℝ) (hb : 0 < b) (hh : 0 < h) :
    |nvCost b h a d - nvCost b h a' d| ≤ max b h * |a - a'| := by
  rw [th4_cost_eq, th4_cost_eq]
  have hb' : b ≤ max b h := le_max_left _ _
  have hh' : h ≤ max b h := le_max_right _ _
  set σ := max b h
  rcases le_total a d with h1 | h1 <;> rcases le_total a' d with h2 | h2
  · rw [max_eq_right (by linarith : a - d ≤ 0), max_eq_right (by linarith : a' - d ≤ 0),
      max_eq_left (by linarith : 0 ≤ d - a), max_eq_left (by linarith : 0 ≤ d - a')]
    rw [abs_le]
    rcases le_total a a' with h3 | h3
    · rw [abs_of_nonpos (by linarith)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 h3)]
    · rw [abs_of_nonneg (by linarith)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 h3)]
  · rw [max_eq_right (by linarith : a - d ≤ 0), max_eq_left (by linarith : 0 ≤ a' - d),
      max_eq_left (by linarith : 0 ≤ d - a), max_eq_right (by linarith : d - a' ≤ 0)]
    rw [abs_of_nonpos (by linarith : a - a' ≤ 0), abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 h1),
      mul_nonneg (sub_nonneg.2 hh') (sub_nonneg.2 h2), mul_nonneg hb.le (sub_nonneg.2 h2),
      mul_nonneg hh.le (sub_nonneg.2 h1)]
  · rw [max_eq_left (by linarith : 0 ≤ a - d), max_eq_right (by linarith : a' - d ≤ 0),
      max_eq_right (by linarith : d - a ≤ 0), max_eq_left (by linarith : 0 ≤ d - a')]
    rw [abs_of_nonneg (by linarith : 0 ≤ a - a'), abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 h2),
      mul_nonneg (sub_nonneg.2 hh') (sub_nonneg.2 h1), mul_nonneg hb.le (sub_nonneg.2 h1),
      mul_nonneg hh.le (sub_nonneg.2 h2)]
  · rw [max_eq_left (by linarith : 0 ≤ a - d), max_eq_left (by linarith : 0 ≤ a' - d),
      max_eq_right (by linarith : d - a ≤ 0), max_eq_right (by linarith : d - a' ≤ 0)]
    rw [abs_le]
    rcases le_total a a' with h3 | h3
    · rw [abs_of_nonpos (by linarith)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hh') (sub_nonneg.2 h3)]
    · rw [abs_of_nonneg (by linarith)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hh') (sub_nonneg.2 h3)]

/-- convexity inequality along a segment -/
def Cvx {E : Type*} [AddCommGroup E] [Module ℝ E] (Φ : E → ℝ) : Prop :=
  ∀ q g : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Φ (q + t • (g - q)) ≤ (1 - t) * Φ q + t * Φ g

lemma th4_cvx_smul {E : Type*} [AddCommGroup E] [Module ℝ E] {Φ : E → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (h : Cvx Φ) : Cvx (fun g => c * Φ g) := by
  intro q g t h0 h1
  have := mul_le_mul_of_nonneg_left (h q g t h0 h1) hc
  linarith

lemma th4_cvx_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} (s : Finset ι)
    (Φ : ι → E → ℝ) (h : ∀ j ∈ s, Cvx (Φ j)) : Cvx (fun g => ∑ j ∈ s, Φ j g) := by
  intro q g t h0 h1
  have : ∑ j ∈ s, Φ j (q + t • (g - q)) ≤ ∑ j ∈ s, ((1 - t) * Φ j q + t * Φ j g) :=
    Finset.sum_le_sum (fun j hj => h j hj q g t h0 h1)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  exact this

lemma th4_cvx_add {E : Type*} [AddCommGroup E] [Module ℝ E] {Φ Ψ : E → ℝ}
    (h : Cvx Φ) (h' : Cvx Ψ) : Cvx (fun g => Φ g + Ψ g) := by
  intro q g t h0 h1
  have := add_le_add (h q g t h0 h1) (h' q g t h0 h1)
  linarith

/-- strong convexity of minimizer of convex + lam‖·‖² -/
lemma th4_strong {p : ℕ} (Φ : EuclideanSpace ℝ (Fin p) → ℝ) (hΦ : Cvx Φ) (lam : ℝ) (hlam : 0 ≤ lam)
    (q : EuclideanSpace ℝ (Fin p))
    (hq : ∀ g, Φ q + lam * ‖q‖ ^ 2 ≤ Φ g + lam * ‖g‖ ^ 2) (g : EuclideanSpace ℝ (Fin p)) :
    Φ q + lam * ‖q‖ ^ 2 + lam * ‖g - q‖ ^ 2 ≤ Φ g + lam * ‖g‖ ^ 2 := by
  set Δ := g - q with hΔ
  set Y := lam * ‖Δ‖ ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (Φ g - Φ q + 2 * lam * inner ℝ q Δ) + t * Y := by
    intro t ht0 ht1
    have h1 := hq (q + t • Δ)
    have h2 := hΦ q g t ht0.le ht1
    have h3 : ‖q + t • Δ‖ ^ 2 = ‖q‖ ^ 2 + 2 * t * inner ℝ q Δ + t ^ 2 * ‖Δ‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [h3] at h1
    have : t * (Φ g - Φ q + 2 * lam * inner ℝ q Δ + t * Y) ≥ 0 := by
      simp only [hY] at *
      nlinarith
    have := (mul_nonneg_iff_of_pos_left ht0).mp (by linarith : 0 ≤ t * (Φ g - Φ q + 2 * lam * inner ℝ q Δ + t * Y))
    linarith
  have hX : 0 ≤ Φ g - Φ q + 2 * lam * inner ℝ q Δ := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    set t := min 1 (ε / (Y + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos hε (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ ε / (Y + 1) := min_le_right _ _
    have h4 : t * Y ≤ ε := by
      calc t * Y ≤ ε / (Y + 1) * Y := mul_le_mul_of_nonneg_right ht2 hY0
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
    have := key t ht0 ht1
    linarith
  have h5 : ‖g‖ ^ 2 = ‖q‖ ^ 2 + 2 * inner ℝ q Δ + ‖Δ‖ ^ 2 := by
    have : g = q + Δ := by simp [hΔ]
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  simp only [hY] at hX ⊢
  nlinarith


theorem th4_core {p n : ℕ} (b h lam Xmax : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (hS : ∀ j, ‖(S j).1‖ ^ 2 ≤ Xmax ^ 2)
    (i : Fin n) (q q' : EuclideanSpace ℝ (Fin p))
    (hq : IsNVRegSolution b h lam S q) (hq' : IsNVRegLooSolution b h lam S i q') :
    ∀ x : EuclideanSpace ℝ (Fin p), ‖x‖ ^ 2 ≤ Xmax ^ 2 → ∀ d : ℝ,
      |nvCost b h (inner ℝ q x) d - nvCost b h (inner ℝ q' x) d| ≤
        (max b h) ^ 2 * Xmax ^ 2 / (2 * (n : ℝ) * lam) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  set σ := max b h with hσ
  have hσ0 : 0 < σ := lt_max_of_lt_left hb
  set T : EuclideanSpace ℝ (Fin p) → Fin n → ℝ :=
    fun g j => nvCost b h (inner ℝ g (S j).1) (S j).2 with hT
  have hTc : ∀ j, Cvx (T · j) := by
    intro j q g t h0 h1
    have e : inner ℝ (q + t • (g - q)) (S j).1 = (1 - t) * inner ℝ q (S j).1 + t * inner ℝ g (S j).1 := by
      rw [inner_add_left, inner_smul_left, inner_sub_left]; simp; ring
    simp only [hT]
    rw [e]
    exact th4_cost_cvx b h _ _ _ t hb hh h0 h1
  set ΦG : EuclideanSpace ℝ (Fin p) → ℝ := fun g => (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.erase i, T g j
    with hΦG
  set ΦF : EuclideanSpace ℝ (Fin p) → ℝ := fun g => (1 / (n : ℝ)) * ∑ j, T g j with hΦF
  have hΦGc : Cvx ΦG := th4_cvx_smul _ (by positivity) (th4_cvx_sum _ _ (fun j _ => hTc j))
  have hΦFc : Cvx ΦF := th4_cvx_smul _ (by positivity) (th4_cvx_sum _ _ (fun j _ => hTc j))
  have hF : ∀ g, nvRegObjective b h lam S g = ΦF g + lam * ‖g‖ ^ 2 := fun g => rfl
  have hG : ∀ g, nvRegLooObjective b h lam S i g = ΦG g + lam * ‖g‖ ^ 2 := fun g => rfl
  have hFG : ∀ g, ΦF g = ΦG g + (1 / (n : ℝ)) * T g i := by
    intro g
    simp only [hΦF, hΦG]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  have s1 := th4_strong ΦF hΦFc lam hlam.le q (fun g => by rw [← hF, ← hF]; exact hq g) q'
  have s2 := th4_strong ΦG hΦGc lam hlam.le q' (fun g => by rw [← hG, ← hG]; exact hq' g) q
  set D := ‖q' - q‖ with hD
  have hD' : ‖q - q'‖ = D := by rw [hD, norm_sub_rev]
  rw [hD'] at s2
  have hFGq := hFG q
  have hFGq' := hFG q'
  have hsum : 2 * lam * D ^ 2 ≤ (1 / (n : ℝ)) * (T q' i - T q i) := by
    nlinarith
  have hxi : ‖(S i).1‖ ≤ Xmax := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg (S i).1, hS i]
  have hTi : T q' i - T q i ≤ σ * (D * Xmax) := by
    have h1 := th4_cost_lip b h (S i).2 (inner ℝ q' (S i).1) (inner ℝ q (S i).1) hb hh
    have h2 : |inner ℝ q' (S i).1 - inner ℝ q (S i).1| ≤ D * Xmax := by
      rw [← inner_sub_left]
      calc _ ≤ ‖q' - q‖ * ‖(S i).1‖ := abs_real_inner_le_norm _ _
        _ ≤ D * Xmax := mul_le_mul_of_nonneg_left hxi (norm_nonneg _)
    have h3 := le_abs_self (nvCost b h (inner ℝ q' (S i).1) (S i).2 - nvCost b h (inner ℝ q (S i).1) (S i).2)
    simp only [hT]
    nlinarith [mul_le_mul_of_nonneg_left h2 hσ0.le]
  set r := σ * Xmax / (2 * (n : ℝ) * lam) with hr
  have hr0 : 0 ≤ r := by positivity
  have hDr : D ≤ r := by
    by_contra hc
    push_neg at hc
    have hDpos : 0 < D := lt_of_le_of_lt hr0 hc
    have : 2 * lam * D ≤ σ * Xmax / n := by
      have h6 : 2 * lam * D ^ 2 ≤ (1 / (n : ℝ)) * (σ * (D * Xmax)) :=
        hsum.trans (mul_le_mul_of_nonneg_left hTi (by positivity))
      have h7 : (2 * lam * D) * D ≤ (σ * Xmax / n) * D := by
        calc (2 * lam * D) * D = 2 * lam * D ^ 2 := by ring
          _ ≤ _ := h6
          _ = _ := by ring
      exact le_of_mul_le_mul_right h7 hDpos
    have : D ≤ r := by
      rw [hr, le_div_iff₀ (by positivity)]
      have : σ * Xmax / n * n = σ * Xmax := by field_simp
      nlinarith
    linarith
  intro x hx d
  have hxn : ‖x‖ ≤ Xmax := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg x]
  have h1 := th4_cost_lip b h d (inner ℝ q x) (inner ℝ q' x) hb hh
  have h2 : |inner ℝ q x - inner ℝ q' x| ≤ D * Xmax := by
    rw [← inner_sub_left]
    calc _ ≤ ‖q - q'‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ D * Xmax := by rw [hD']; exact mul_le_mul_of_nonneg_left hxn (by positivity)
  calc _ ≤ σ * |inner ℝ q x - inner ℝ q' x| := h1
    _ ≤ σ * (D * Xmax) := mul_le_mul_of_nonneg_left h2 hσ0.le
    _ ≤ σ * (r * Xmax) := by
        apply mul_le_mul_of_nonneg_left _ hσ0.le
        exact mul_le_mul_of_nonneg_right hDr hX
    _ = σ ^ 2 * Xmax ^ 2 / (2 * (n : ℝ) * lam) := by rw [hr]; field_simp

end BigDataNV.Reg

open BigDataNV.Reg


theorem solution {p n : ℕ} (b h lam Xmax : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (hS : ∀ j, ‖(S j).1‖ ^ 2 ≤ Xmax ^ 2)
    (i : Fin n) (q q' : EuclideanSpace ℝ (Fin p))
    (hq : IsNVRegSolution b h lam S q) (hq' : IsNVRegLooSolution b h lam S i q') :
    ∀ x : EuclideanSpace ℝ (Fin p), ‖x‖ ^ 2 ≤ Xmax ^ 2 → ∀ d : ℝ,
      |nvCost b h (inner ℝ q x) d - nvCost b h (inner ℝ q' x) d| ≤
        (max b h) ^ 2 * Xmax ^ 2 / (2 * (n : ℝ) * lam) := by
  exact th4_core b h lam Xmax hb hh hlam hX S hS i q q' hq hq'
