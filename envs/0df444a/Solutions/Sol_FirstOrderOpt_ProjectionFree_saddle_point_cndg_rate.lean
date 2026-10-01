-- Prove2me | solution 1 for FirstOrderOpt.ProjectionFree.saddle_point_cndg_rate
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:03:19.962044+00:00
-- url     : https://prove2.me/submissions/9489b884-3a0d-4dd2-8e33-e9868cac3f8a

import Mathlib

namespace Cex2a38

noncomputable section

open scoped RealInnerProductSpace

abbrev V := EuclideanSpace ℝ (Fin 2)

noncomputable def pt (a b : ℝ) : V := WithLp.toLp 2 ![a, b]

@[simp] lemma pt0 (a b : ℝ) : (pt a b) 0 = a := by simp [pt]
@[simp] lemma pt1 (a b : ℝ) : (pt a b) 1 = b := by simp [pt]

lemma inner_V (a b : V) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma norm_V (a : V) : ‖a‖ = Real.sqrt (a 0 ^ 2 + a 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma cont0 : Continuous (fun p : V => p 0) := (EuclideanSpace.proj (0 : Fin 2) : V →L[ℝ] ℝ).continuous
lemma cont1 : Continuous (fun p : V => p 1) := (EuclideanSpace.proj (1 : Fin 2) : V →L[ℝ] ℝ).continuous

def X : Set V := {p | 0 ≤ p 0 ∧ p 0 ≤ 4 * p 1 ∧ p 1 ≤ 1}

lemma X_conv : Convex ℝ X := by
  intro a ha b hb s t hs ht hst
  simp only [X, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨by nlinarith [mul_nonneg hs a1, mul_nonneg ht b1], ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left a2 hs, mul_le_mul_of_nonneg_left b2 ht]
  · nlinarith [mul_le_mul_of_nonneg_left a3 hs, mul_le_mul_of_nonneg_left b3 ht]

lemma X_compact : IsCompact X := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : X = {p : V | 0 ≤ p 0} ∩ ({p : V | p 0 ≤ 4 * p 1} ∩ {p : V | p 1 ≤ 1}) := by
      ext p; simp [X]
    rw [this]
    exact (isClosed_le continuous_const cont0).inter
      ((isClosed_le cont0 (continuous_const.mul cont1)).inter (isClosed_le cont1 continuous_const))
  · rw [Metric.isBounded_iff_subset_closedBall (0 : V)]
    refine ⟨5, fun p hp => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp
    rw [mem_closedBall_zero_iff, norm_V]
    rw [show (5 : ℝ) = Real.sqrt (5 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_le_sqrt
    nlinarith

noncomputable def P0 : V := pt 0 (-1)
noncomputable def P1 : V := pt (-2) 7
noncomputable def Pm : V := pt (-1) 3
noncomputable def Y : Set V := segment ℝ P0 P1

lemma Y_conv : Convex ℝ Y := convex_segment _ _
lemma Y_compact : IsCompact Y := by
  unfold Y; rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

lemma mem_Y {p : V} (hp : p ∈ Y) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p 0 = -2 * t ∧ p 1 = -1 + 8 * t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  refine ⟨b, hb, by linarith, ?_, ?_⟩
  · simp [P0, P1]; ring
  · simp [P0, P1]; linear_combination (-1) * hab

lemma pt_mem_Y (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : pt (-2 * t) (-1 + 8 * t) ∈ Y := by
  refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
  ext i; fin_cases i <;> simp [P0, P1] <;> ring

noncomputable def fhat (p : V) : ℝ := if p = Pm then -1 else p 0 ^ 2 - 1

lemma fhat_le (p : V) : fhat p ≤ p 0 ^ 2 - 1 := by
  unfold fhat; split_ifs <;> nlinarith [sq_nonneg (p 0)]

lemma fhat_ge (p : V) : -1 ≤ fhat p := by
  unfold fhat; split_ifs <;> nlinarith [sq_nonneg (p 0)]

noncomputable def A : V →L[ℝ] V := ContinuousLinearMap.id ℝ V

lemma normA : ‖A‖ = 1 := ContinuousLinearMap.norm_id

noncomputable def f (x : V) : ℝ := sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y)

def wq (x : V) : ℝ := x 1 - x 0 / 4
def q (x : V) : ℝ := 1 - x 1 + 4 * wq x ^ 2
def ell (x : V) : ℝ := 1 + 3 * x 1 - x 0

lemma fbdd (x : V) : BddAbove ((fun y => ⟪A x, y⟫ - fhat y) '' Y) := by
  refine ⟨2 * |x 0| + 7 * |x 1| + 1, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, t0, t1, e0, e1⟩ := mem_Y hp
  have hf := fhat_ge p
  simp only [A, ContinuousLinearMap.id_apply, inner_V, e0, e1]
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), le_abs_self (x 0), neg_abs_le (x 0),
    le_abs_self (x 1), neg_abs_le (x 1),
    mul_nonneg t0 (by linarith [neg_abs_le (x 0)] : 0 ≤ |x 0| + x 0),
    mul_nonneg (by linarith : 0 ≤ 1 - t) (abs_nonneg (x 0)),
    mul_nonneg t0 (by linarith [le_abs_self (x 1)] : 0 ≤ |x 1| - x 1),
    mul_nonneg (by linarith : 0 ≤ 1 - t) (by linarith [neg_abs_le (x 1)] : 0 ≤ |x 1| + x 1)]

lemma f_le (x : V) : f x ≤ max (q x) (ell x) := by
  apply csSup_le ((Set.nonempty_of_mem (left_mem_segment ℝ P0 P1)).image _)
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, t0, t1, e0, e1⟩ := mem_Y hp
  simp only [A, ContinuousLinearMap.id_apply]
  by_cases hpm : p = Pm
  · subst hpm
    apply le_max_of_le_right
    simp [fhat, Pm, inner_V, ell]; ring_nf; linarith
  · apply le_max_of_le_left
    simp only [fhat, hpm, if_false, inner_V, e0, e1, q, wq]
    nlinarith [sq_nonneg (x 1 - x 0 / 4 - t)]

lemma ell_le_f (x : V) : ell x ≤ f x := by
  apply le_csSup_of_le (fbdd x) ⟨Pm, ?_, rfl⟩
  · simp [A, fhat, Pm, inner_V, ell]; ring_nf; linarith
  · have := pt_mem_Y (1/2) (by norm_num) (by norm_num)
    convert this using 2 <;> norm_num [Pm]

lemma q_le_f (x : V) (h0 : 0 ≤ wq x) (h1 : wq x ≤ 1) : q x ≤ f x := by
  apply le_csSup_of_le (fbdd x) ⟨_, pt_mem_Y (wq x) h0 h1, rfl⟩
  have := fhat_le (pt (-2 * wq x) (-1 + 8 * wq x))
  simp only [A, ContinuousLinearMap.id_apply, inner_V, pt0, pt1] at this ⊢
  simp only [q, wq] at *
  nlinarith

lemma wq_mem {z : V} (hz : z ∈ X) : 0 ≤ wq z ∧ wq z ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hz
  unfold wq; constructor <;> linarith

def xs (k : ℕ) : V := if k ≤ 2 then 0 else if k = 3 then pt 0 1 else pt 4 1
def ys (k : ℕ) : V := if k ≤ 2 then 0 else if k = 3 then pt 0 (1/2) else pt 4 1
def al (k : ℕ) : ℝ := if k = 3 then 1/2 else 1
def fe (k : ℕ) (z : V) : ℝ := if k ≤ 2 then 1 + 3 * wq z else 1 + q z
def G (k : ℕ) (a : V) : V := if k ≤ 2 then pt (-3/4) 3 else pt (-2 * wq a) (-1 + 8 * wq a)
def fG (k : ℕ) (a : V) : V →L[ℝ] ℝ := innerSL ℝ (G k a)

lemma zero_mem_X : (0 : V) ∈ X := by simp [X]
lemma pt41_mem_X : pt 4 1 ∈ X := by norm_num [X]
lemma pt01_mem_X : pt 0 1 ∈ X := by norm_num [X]
lemma pt0h_mem_X : pt 0 (1/2) ∈ X := by norm_num [X]

lemma xs_mem (k : ℕ) : xs k ∈ X := by
  unfold xs; split_ifs
  · exact zero_mem_X
  · exact pt01_mem_X
  · exact pt41_mem_X

lemma ys_mem (k : ℕ) : ys k ∈ X := by
  unfold ys; split_ifs
  · exact zero_mem_X
  · exact pt0h_mem_X
  · exact pt41_mem_X

lemma q_nonneg {z : V} (hz : z ∈ X) : 0 ≤ q z := by
  obtain ⟨h1, h2, h3⟩ := hz
  unfold q; nlinarith [sq_nonneg (wq z)]

lemma f_xstar : f (pt 4 1) ≤ 0 := by
  have := f_le (pt 4 1)
  simp [q, wq, ell] at this; norm_num at this; linarith

lemma ell_nonneg {z : V} (hz : z ∈ X) : 0 ≤ ell z := by
  obtain ⟨h1, h2, h3⟩ := hz
  unfold ell; linarith

lemma sandwich (k : ℕ) (z : V) (hz : z ∈ X) : f z ≤ fe k z ∧ fe k z ≤ f z + 1 * 1 ^ 2 := by
  have hle := f_le z
  have hl := ell_le_f z
  obtain ⟨w0, w1⟩ := wq_mem hz
  obtain ⟨h1, h2, h3⟩ := hz
  unfold fe; split_ifs
  · constructor
    · refine hle.trans (max_le ?_ ?_) <;> simp only [q, ell] at * <;> unfold wq at * <;> nlinarith
    · simp only [ell] at hl; unfold wq; linarith
  · have hq := q_le_f z w0 w1
    constructor
    · refine hle.trans (max_le ?_ ?_)
      · linarith
      · simp only [q, ell]; unfold wq; nlinarith [sq_nonneg (2 * (z 1 - z 0 / 4) - 1)]
    · linarith

lemma smooth (k : ℕ) (a b : V) :
    ‖fG k a - fG k b‖ ≤ (‖A‖ ^ 2 / (2 / 17 * 1)) * ‖a - b‖ := by
  unfold fG
  rw [← map_sub, innerSL_apply_norm, normA]
  unfold G; split_ifs
  · simp only [sub_self, norm_zero]; positivity
  · rw [norm_V, norm_V]
    simp only [PiLp.sub_apply, pt0, pt1, wq]
    rw [show (1 : ℝ) ^ 2 / (2 / 17 * 1) = Real.sqrt ((17/2) ^ 2) by rw [Real.sqrt_sq] <;> norm_num,
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (4 * (a 0 - b 0) + (a 1 - b 1))]

lemma cvx (k : ℕ) (a b : V) : fe k a + (fG k a) (b - a) ≤ fe k b := by
  unfold fe fG G
  split_ifs
  · simp only [innerSL_apply_apply, inner_V, PiLp.sub_apply, pt0, pt1, wq]; linarith
  · simp only [innerSL_apply_apply, inner_V, PiLp.sub_apply, pt0, pt1, q, wq]
    nlinarith [sq_nonneg ((b 1 - b 0 / 4) - (a 1 - a 0 / 4))]

theorem cex : ¬ (∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (Y : Set F) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y)
    (A : E →L[ℝ] F) (fhat : F → ℝ)
    (f : E → ℝ) (hf : ∀ x, f x = sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (hfbdd : ∀ x, BddAbove ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (σv DY : ℝ) (hσv : 0 < σv) (hDY : 0 < DY)
    (η : ℕ → ℝ) (hηpos : ∀ k, 1 ≤ k → 0 < η k) (hηmono : ∀ k, 1 ≤ k → η (k + 1) ≤ η k)
    (fη : ℕ → E → ℝ) (fηGrad : ℕ → E → E →L[ℝ] ℝ)
    (hsandwich : ∀ k, 1 ≤ k → ∀ z ∈ X, f z ≤ fη k z ∧ fη k z ≤ f z + η k * DY ^ 2)
    (hηSmooth : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X,
      ‖fηGrad k a - fηGrad k b‖ ≤ (‖A‖ ^ 2 / (σv * η k)) * ‖a - b‖)
    (hcvx : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X, fη k a + (fηGrad k a) (b - a) ≤ fη k b)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X) (hy : ∀ k, y k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fηGrad k (y (k - 1))) (x k) ≤ (fηGrad k (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      fη k (y k) ≤ fη k ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k),
    f (y k) - f xstar ≤ (2 / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) * η i * DY ^ 2 +
        (‖A‖ ^ 2 / (σv * η i)) * ‖x i - y (i - 1)‖ ^ 2)) := by
  intro h
  have key := @h V V _ _ _ _ X X_conv X_compact Y Y_conv Y_compact A fhat f (fun _ => rfl) fbdd
    (2/17) 1 (by norm_num) (by norm_num) (fun _ => 1) (fun _ _ => one_pos) (fun _ _ => le_rfl)
    fe fG (fun k _ z hz => sandwich k z hz) (fun k _ a _ b _ => smooth k a b)
    (fun k _ a _ b _ => cvx k a b) xs ys (xs_mem 0) (by simp [xs, ys]) (fun k _ => xs_mem k) ys_mem
    ?hLO al ?hal ?hyDef ?hyk (pt 4 1) pt41_mem_X
    (fun z hz => f_xstar.trans ((ell_nonneg hz).trans (ell_le_f z))) 3 (by norm_num)
  case hLO =>
    intro k hk z hz
    obtain ⟨z1, z2, z3⟩ := hz
    unfold fG G
    simp only [innerSL_apply_apply, inner_V]
    by_cases h2 : k ≤ 2
    · simp only [h2, if_true, xs, pt0, pt1, PiLp.zero_apply]; nlinarith
    · simp only [h2, if_false, pt0, pt1]
      by_cases h3 : k = 3
      · subst h3; simp [xs, ys, wq]; linarith
      · obtain ⟨w0, w1⟩ := wq_mem (ys_mem (k - 1))
        simp only [xs, h2, h3, if_false, pt0, pt1]
        nlinarith [mul_nonneg w0 (by linarith : 0 ≤ 4 * z 1 - z 0)]
  case hal =>
    intro k _; unfold al; split_ifs <;> constructor <;> norm_num
  case hyDef =>
    intro k hk
    by_cases h2 : k ≤ 2
    · simp [xs, ys, al, h2, show k - 1 ≤ 2 by omega, show k ≠ 3 by omega]
    · by_cases h3 : k = 3
      · subst h3; ext i; fin_cases i <;> simp [xs, ys, al] <;> norm_num
      · simp [xs, ys, al, h2, h3]
  case hyk =>
    intro k hk
    have hγ0 : 0 ≤ 2 / ((k : ℝ) + 1) := by positivity
    have hγ1 : 2 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hmem : (1 - 2 / ((k : ℝ) + 1)) • ys (k - 1) + (2 / ((k : ℝ) + 1)) • xs k ∈ X :=
      X_conv (ys_mem _) (xs_mem _) (by linarith) hγ0 (by ring)
    obtain ⟨w0, w1⟩ := wq_mem hmem
    by_cases h2 : k ≤ 2
    · simp only [fe, h2, if_true]
      have : ys k = 0 := by simp [ys, h2]
      rw [this]; simp [wq] at w0 ⊢
      linarith
    · by_cases h3 : k = 3
      · subst h3
        have e : (1 - 2 / (((3 : ℕ) : ℝ) + 1)) • ys (3 - 1) + (2 / (((3 : ℕ) : ℝ) + 1)) • xs 3
            = ys 3 := by
          ext i; fin_cases i <;> simp [xs, ys] <;> norm_num
        rw [e]
      · simp only [fe, h2, if_false]
        have : ys k = pt 4 1 := by simp [ys, h2, h3]
        rw [this]
        have := q_nonneg hmem
        have e0 : q (pt 4 1) = 0 := by norm_num [q, wq]
        linarith
  clear h
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by rfl] at key
  have hy3 : ys 3 = pt 0 (1/2) := by simp [ys]
  have e1 : ‖xs 1 - ys 0‖ = 0 := by simp [xs, ys]
  have e2 : ‖xs 2 - ys 1‖ = 0 := by simp [xs, ys]
  have e3 : ‖xs 3 - ys 2‖ = 1 := by simp [xs, ys, norm_V]
  simp only [Finset.mem_singleton, Finset.sum_singleton, normA, hy3] at key
  norm_num [e1, e2, e3] at key
  have h1 := ell_le_f (ys 3)
  have h2 := f_xstar
  rw [hy3] at h1
  norm_num [ell] at h1
  linarith

end
end Cex2a38

-- Disproof of FirstOrderOpt.ProjectionFree.saddle_point_cndg_rate via the explicit
-- counterexample Cex2a38.cex (see Expl_dp_2a38f50b.md).
open scoped RealInnerProductSpace in
theorem solution : ¬ (∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (Y : Set F) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y)
    (A : E →L[ℝ] F) (fhat : F → ℝ)
    (f : E → ℝ) (hf : ∀ x, f x = sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (hfbdd : ∀ x, BddAbove ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (σv DY : ℝ) (hσv : 0 < σv) (hDY : 0 < DY)
    (η : ℕ → ℝ) (hηpos : ∀ k, 1 ≤ k → 0 < η k) (hηmono : ∀ k, 1 ≤ k → η (k + 1) ≤ η k)
    (fη : ℕ → E → ℝ) (fηGrad : ℕ → E → E →L[ℝ] ℝ)
    (hsandwich : ∀ k, 1 ≤ k → ∀ z ∈ X, f z ≤ fη k z ∧ fη k z ≤ f z + η k * DY ^ 2)
    (hηSmooth : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X,
      ‖fηGrad k a - fηGrad k b‖ ≤ (‖A‖ ^ 2 / (σv * η k)) * ‖a - b‖)
    (hcvx : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X, fη k a + (fηGrad k a) (b - a) ≤ fη k b)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X) (hy : ∀ k, y k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fηGrad k (y (k - 1))) (x k) ≤ (fηGrad k (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      fη k (y k) ≤ fη k ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k),
    f (y k) - f xstar ≤ (2 / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) * η i * DY ^ 2 +
        (‖A‖ ^ 2 / (σv * η i)) * ‖x i - y (i - 1)‖ ^ 2)) := by
  exact Cex2a38.cex
