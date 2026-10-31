-- Prove2me | solution 2 for DisclosureStatics.Aggregation.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:22:08.611276+00:00
-- url     : https://prove2.me/submissions/68e18c10-52e5-4473-82f5-6adcdc4bc06b

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model
open DisclosureStatics.Aggregation


noncomputable section

abbrev T3 := ULift.{0} (Fin 3)

lemma sum_T3 (f : T3 → ℝ) :
    ∑ i, f i = f (ULift.up 0) + f (ULift.up 1) + f (ULift.up 2) := by
  rw [show (Finset.univ : Finset T3) = {ULift.up 0, ULift.up 1, ULift.up 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; ring

lemma sum_T3_erase (f : T3 → ℝ) :
    ∑ i ∈ Finset.univ.erase (ULift.up 0), f i = f (ULift.up 1) + f (ULift.up 2) := by
  rw [show (Finset.univ : Finset T3).erase (ULift.up 0) = {ULift.up 1, ULift.up 2} by decide]
  rw [Finset.sum_pair (by decide)]

lemma tan_exp (x y : ℝ) : Real.exp (-y) ≥ Real.exp (-x) * (1 - (y - x)) := by
  have h := Real.add_one_le_exp (-(y - x))
  have : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  have := Real.exp_pos (-x)
  nlinarith

lemma tan_u (x y : ℝ) : cara 1 y ≤ cara 1 x + Real.exp (-x) * (y - x) := by
  unfold cara
  have := tan_exp x y
  simp only [neg_mul, one_mul, div_one]
  nlinarith

lemma tan_phi (v w : ℝ) : -Real.exp (-w) ≤ -Real.exp (-v) + Real.exp (-v) * (w - v) := by
  have := tan_exp v w; nlinarith

lemma tan_phiu (x y : ℝ) :
    -Real.exp (-(cara 1 y)) ≤ -Real.exp (-(cara 1 x)) +
      Real.exp (-(cara 1 x)) * Real.exp (-x) * (y - x) := by
  have h1 := tan_phi (cara 1 x) (cara 1 y)
  have h2 := tan_u x y
  have hp := Real.exp_pos (-(cara 1 x))
  nlinarith [mul_le_mul_of_nonneg_left h2 hp.le]

lemma exists_foc (r : ℝ) (hr : 0 < r) :
    ∃ x : ℝ, Real.exp (-(cara 1 x)) * Real.exp (-x) = r := by
  set t := Real.log r
  let g : ℝ → ℝ := fun x => Real.exp (-x) - 1 - x
  have hg : Continuous g := by fun_prop
  have h1 : g |t| ≤ t := by
    have : Real.exp (-|t|) ≤ 1 := by rw [Real.exp_le_one_iff]; simp
    simp only [g]; have := neg_abs_le t; linarith
  have h2 : t ≤ g (-|t|) := by
    have := Real.add_one_le_exp (|t|)
    simp only [g, neg_neg]; have := le_abs_self t; have := abs_nonneg t; linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc' (show -|t| ≤ |t| by
    have := abs_nonneg t; linarith) hg.continuousOn ⟨h1, h2⟩
  refine ⟨x, ?_⟩
  rw [← Real.exp_add, ← Real.exp_log hr]
  congr 1
  simp only [g] at hx
  unfold cara; simp only [neg_mul, one_mul, div_one]; linarith

def πF : Finpartition (Finset.univ : Finset T3) where
  parts := {{ULift.up 0},{ULift.up 1},{ULift.up 2}}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all <;> decide
  sup_parts := by decide
  bot_notMem := by decide

def ρF : Finpartition (Finset.univ : Finset T3) where
  parts := {{ULift.up 0},{ULift.up 1, ULift.up 2}}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all <;> decide
  sup_parts := by decide
  bot_notMem := by decide

def pv : Fin 3 → ℝ := ![1/3, 1/6, 1/2]

def MM (I : ℝ) : Market T3 :=
  ⟨ULift.up 0, fun _ => 1/3, fun i => pv i.down, fun _ => 0, I⟩

def φ0 (v : ℝ) : ℝ := -Real.exp (-v)

lemma hasDeriv_φ0 (v : ℝ) : HasDerivAt φ0 (Real.exp (-v)) v := by
  have h : HasDerivAt (fun v => -Real.exp (-v)) (-(Real.exp (-v) * -1)) v :=
    ((hasDerivAt_neg v).exp).neg
  rw [show -(Real.exp (-v) * -1) = Real.exp (-v) by ring] at h
  exact h

lemma deriv_φ0 : deriv φ0 = fun v => Real.exp (-v) := funext fun v => (hasDeriv_φ0 v).deriv

lemma deriv2_φ0 : deriv (deriv φ0) = fun v => -Real.exp (-v) := by
  rw [deriv_φ0]; funext v
  have := ((hasDerivAt_neg v).exp)
  rw [this.deriv]; ring

lemma averse_φ0 : AggregationAverse φ0 (Set.Iio (1 / 1)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : ContDiff ℝ 3 φ0 := by unfold φ0; fun_prop
    exact this.contDiffOn
  · intro v _; rw [deriv_φ0]; exact Real.exp_pos _
  · intro v _; rw [deriv2_φ0]; simp [Real.exp_pos]
  · intro x _ y _ _
    simp only [deriv2_φ0]
    simp only [deriv_φ0, neg_neg]
    rw [div_self (Real.exp_pos _).ne', div_self (Real.exp_pos _).ne']

lemma standing_MM (I : ℝ) : (MM I).Standing := by
  refine ⟨fun _ => by norm_num [MM], ?_, fun i => ?_, ?_⟩
  · rw [sum_T3]; simp [MM]; norm_num
  · simp only [MM, pv]; fin_cases i <;> simp <;> norm_num
  · rw [sum_T3]; simp [MM, pv]; norm_num

lemma budget_MM (I : ℝ) (x : T3 → ℝ) :
    Budget (MM I) x ↔ (1/3) * x (ULift.up 0) + (1/6) * x (ULift.up 1) +
      (1/2) * x (ULift.up 2) = I := by
  unfold Budget
  simp only [MM]
  rw [sum_T3_erase]
  simp [MM, pv]
  constructor <;> intro h <;> linarith

lemma loss_MM (I : ℝ) (x : T3 → ℝ) :
    Loss (MM I) x = (x (ULift.up 0) - x (ULift.up 1)) * (-1/6) +
      (x (ULift.up 0) - x (ULift.up 2)) * (1/6) := by
  unfold Loss
  simp only [MM]
  rw [sum_T3_erase]
  simp [MM, pv]; norm_num

lemma V_B (I : ℝ) (x : T3 → ℝ) :
    V (MM I) (cara 1) {ULift.up 1, ULift.up 2} x =
      (1/2) * cara 1 (x (ULift.up 1)) + (1/2) * cara 1 (x (ULift.up 2)) := by
  unfold V probE
  rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  simp [MM]; norm_num

lemma V_single (I : ℝ) (x : T3 → ℝ) (k : T3) :
    V (MM I) (cara 1) {k} x = cara 1 (x k) := by
  unfold V probE
  simp [MM]

lemma U_π (I : ℝ) (x : T3 → ℝ) :
    U (MM I) (cara 1) φ0 πF x = (1/3) * φ0 (cara 1 (x (ULift.up 0))) +
      (1/3) * φ0 (cara 1 (x (ULift.up 1))) + (1/3) * φ0 (cara 1 (x (ULift.up 2))) := by
  unfold U
  rw [show (πF).parts = {{ULift.up 0},{ULift.up 1},{ULift.up 2}} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [V_single]
  simp [probE, MM]; ring

lemma U_ρ (I : ℝ) (x : T3 → ℝ) :
    U (MM I) (cara 1) φ0 ρF x = (1/3) * φ0 (cara 1 (x (ULift.up 0))) +
      (2/3) * φ0 ((1/2) * cara 1 (x (ULift.up 1)) + (1/2) * cara 1 (x (ULift.up 2))) := by
  unfold U
  rw [show (ρF).parts = {{ULift.up 0},{ULift.up 1, ULift.up 2}} from rfl]
  rw [Finset.sum_pair (by decide)]
  simp only [V_single, V_B]
  simp [probE, MM]
  left; norm_num

lemma φ0_mono {v w : ℝ} (h : v ≤ w) : φ0 v ≤ φ0 w := by
  unfold φ0; have := Real.exp_le_exp.2 (neg_le_neg h); linarith

lemma exp_shift (b r : ℝ) (hr : 0 < r) : Real.exp (-(b - Real.log r)) = r * Real.exp (-b) := by
  rw [show -(b - Real.log r) = -b + Real.log r by ring, Real.exp_add, Real.exp_log hr]; ring

lemma cara_zero : cara 1 0 = 0 := by simp [cara]

theorem solution : ¬ (∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (hrB : rE M {M.s₁} ≤ rE M B) (hr1 : 1 ≤ rE M {M.s₁})
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct),
    Loss M c < Loss M ct ∧ Loss M c < Loss M cs ∧ Loss M cs < Loss M ct) := by
  intro h
  obtain ⟨x₂, hx₂⟩ := exists_foc (1/2) (by norm_num)
  obtain ⟨x₃, hx₃⟩ := exists_foc (3/2) (by norm_num)
  set I : ℝ := (1/6) * x₂ + (1/2) * x₃ with hI
  set L2 := Real.log (1/2)
  set L3 := Real.log (3/2)
  set b : ℝ := (3/2) * ((1/6) * x₂ + (1/2) * x₃ + (1/6) * L2 + (1/2) * L3) with hb
  set a : ℝ := I + (1/6) * L2 + (1/2) * L3 with ha
  let c : T3 → ℝ := fun i => ![0, x₂, x₃] i.down
  let cs : T3 → ℝ := fun i => ![0, b - L2, b - L3] i.down
  let ct : T3 → ℝ := fun i => ![a, a - L2, a - L3] i.down
  let B : Finset T3 := {ULift.up 1, ULift.up 2}
  let 𝒮 : Finset (Finset T3) := {{ULift.up 1}, {ULift.up 2}}
  have e2 : Real.exp (-(b - L2)) = (1/2) * Real.exp (-b) := exp_shift b _ (by norm_num)
  have e3 : Real.exp (-(b - L3)) = (3/2) * Real.exp (-b) := exp_shift b _ (by norm_num)
  have f2 : Real.exp (-(a - L2)) = (1/2) * Real.exp (-a) := exp_shift a _ (by norm_num)
  have f3 : Real.exp (-(a - L3)) = (3/2) * Real.exp (-a) := exp_shift a _ (by norm_num)
  -- hypotheses
  have hπ : IsPDS (MM I) πF := by
    show ({ULift.up 0} : Finset T3) ∈ ({{ULift.up 0},{ULift.up 1},{ULift.up 2}} : Finset (Finset T3))
    decide
  have hagg : IsOneStepAggregation (MM I) πF ρF 𝒮 B := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 𝒮 ⊆ ({{ULift.up 0},{ULift.up 1},{ULift.up 2}} : Finset (Finset T3)); decide
    · decide
    · show ({ULift.up 0} : Finset T3) ∉ 𝒮; decide
    · decide
    · show ({{ULift.up 0},{ULift.up 1, ULift.up 2}} : Finset (Finset T3)) =
        insert B (({{ULift.up 0},{ULift.up 1},{ULift.up 2}} : Finset (Finset T3)) \ 𝒮)
      decide
  have hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE (MM I) S ≠ rE (MM I) S' := by
    refine ⟨{ULift.up 1}, by decide, {ULift.up 2}, by decide, ?_⟩
    have : pv 2 = 1/2 := rfl
    have h1 : pv 1 = 1/6 := rfl
    simp only [rE, priceE, probE, Finset.sum_singleton, MM, ULift.down_up, this, h1]
    norm_num
  have hr1v : rE (MM I) {(MM I).s₁} = 1 := by
    simp [rE, priceE, probE, MM, pv]
  have hrBv : rE (MM I) B = 1 := by
    simp only [rE, priceE, probE, B]
    rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
    simp [MM, pv]; norm_num
  -- c solves DP-π
  have hc : IsDemand (MM I) (cara 1) φ0 πF c := by
    have c0 : c (ULift.up 0) = 0 := rfl
    have c1 : c (ULift.up 1) = x₂ := rfl
    have c2 : c (ULift.up 2) = x₃ := rfl
    refine ⟨(budget_MM I c).2 (by rw [c0, c1, c2, hI]; ring), fun y hy => ?_⟩
    rw [budget_MM] at hy
    rw [U_π, U_π, c0, c1, c2, cara_zero]
    have t0 := tan_phiu 0 (y (ULift.up 0))
    have t2 := tan_phiu x₂ (y (ULift.up 1))
    have t3 := tan_phiu x₃ (y (ULift.up 2))
    rw [hx₂] at t2; rw [hx₃] at t3
    simp only [cara_zero, neg_zero, Real.exp_zero, one_mul, sub_zero] at t0
    unfold φ0
    simp only [cara_zero, neg_zero, Real.exp_zero] at *
    linarith
  -- cs solves DP-B
  have hcs : IsIntermediate (MM I) (cara 1) φ0 B c cs := by
    have hsum : ∀ y : T3 → ℝ, ∑ i ∈ B, (MM I).p i * y i =
        (1/6) * y (ULift.up 1) + (1/2) * y (ULift.up 2) := by
      intro y; simp only [B]; rw [Finset.sum_pair (by decide)]; simp [MM, pv]
    have hoff : ∀ i ∉ B, i = ULift.up 0 := by
      intro i hi; obtain ⟨k⟩ := i; fin_cases k
      · rfl
      · exact absurd (by decide) hi
      · exact absurd (by decide) hi
    refine ⟨fun i hi => by rw [hoff i hi]; rfl, ?_, fun y hy1 hy2 => ?_⟩
    · rw [hsum, hsum]; simp [cs, c, hb]; ring
    · rw [hsum, hsum] at hy2
      have hpB : probE (MM I) B = 2/3 := by
        simp only [probE, B]; rw [Finset.sum_pair (by decide)]; simp [MM]; norm_num
      rw [hpB]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply φ0_mono
      rw [V_B, V_B]
      have t2 := tan_u (b - L2) (y (ULift.up 1))
      have t3 := tan_u (b - L3) (y (ULift.up 2))
      rw [e2] at t2; rw [e3] at t3
      simp only [c, cs] at hy2 ⊢
      simp at hy2 ⊢
      have key : Real.exp (-b) * ((1/6) * (y (ULift.up 1) - (b - L2)) +
          (1/2) * (y (ULift.up 2) - (b - L3))) = 0 := by
        rw [show (1/6) * (y (ULift.up 1) - (b - L2)) + (1/2) * (y (ULift.up 2) - (b - L3))
          = 0 by rw [hb]; linarith]
        ring
      nlinarith
  -- ct solves DP-ρ
  have hct : IsDemand (MM I) (cara 1) φ0 ρF ct := by
    refine ⟨(budget_MM I ct).2 (by simp [ct, ha]; ring), fun y hy => ?_⟩
    rw [budget_MM] at hy
    rw [U_ρ, U_ρ]
    have hWt : (1/2) * cara 1 (ct (ULift.up 1)) + (1/2) * cara 1 (ct (ULift.up 2)) =
        cara 1 a := by
      show (1/2) * cara 1 (a - L2) + (1/2) * cara 1 (a - L3) = cara 1 a
      unfold cara
      rw [neg_one_mul, neg_one_mul, neg_one_mul, f2, f3]; ring
    rw [hWt]
    have t0 := tan_phiu a (y (ULift.up 0))
    have tW := tan_phi (cara 1 a)
      ((1/2) * cara 1 (y (ULift.up 1)) + (1/2) * cara 1 (y (ULift.up 2)))
    have t2 := tan_u (a - L2) (y (ULift.up 1))
    have t3 := tan_u (a - L3) (y (ULift.up 2))
    rw [f2] at t2; rw [f3] at t3
    have hK := Real.exp_pos (-(cara 1 a))
    have hW : (1/2) * cara 1 (y (ULift.up 1)) + (1/2) * cara 1 (y (ULift.up 2)) - cara 1 a ≤
        Real.exp (-a) * ((1/4) * (y (ULift.up 1) - (a - L2)) +
          (3/4) * (y (ULift.up 2) - (a - L3))) := by
      rw [← hWt]; simp only [ct]; simp; linarith
    have hW' := mul_le_mul_of_nonneg_left hW hK.le
    have key : (1/3) * (y (ULift.up 0) - a) + (1/6) * (y (ULift.up 1) - (a - L2)) +
        (1/2) * (y (ULift.up 2) - (a - L3)) = 0 := by rw [ha]; linarith
    have key2 : Real.exp (-(cara 1 a)) * Real.exp (-a) * ((1/3) * (y (ULift.up 0) - a) +
        (1/6) * (y (ULift.up 1) - (a - L2)) + (1/2) * (y (ULift.up 2) - (a - L3))) = 0 := by
      rw [key, mul_zero]
    simp only [ct, φ0] at t0 tW ⊢
    simp at t0 tW ⊢
    nlinarith
  have hfin := (@h T3 _ _ (MM I) (standing_MM I) 1 one_pos φ0 averse_φ0 πF ρF hπ 𝒮 B
    hagg hhet (by rw [hr1v, hrBv]) (by rw [hr1v]) c cs ct hc hcs hct).2.2
  rw [loss_MM, loss_MM] at hfin
  simp [cs, ct] at hfin
  linarith
