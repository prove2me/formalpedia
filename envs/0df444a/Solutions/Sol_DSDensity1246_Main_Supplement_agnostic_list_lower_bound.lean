-- Prove2me | solution 1 for DSDensity1246.Main.Supplement.agnostic_list_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:26:51.848805+00:00
-- url     : https://prove2.me/submissions/09b07e92-257d-46a1-92fc-fa251375d1c6

import Mathlib
import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_natarajan
import Definitions.Def_DSDensity1246_Main_Supplement_learning

section
open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Dev.LBAgn



theorem sum_prod_mul {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] (w h : ι → Y → ℝ) :
    ∑ V : ι → Y, ∏ k, (w k (V k) * h k (V k)) = ∏ k, ∑ y, w k y * h k y := by
  have := Finset.prod_univ_sum (fun k : ι => (Finset.univ : Finset Y)) (fun k y => w k y * h k y)
  rw [this]
  simp [Fintype.piFinset_univ]

theorem cross_term {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] (w : ι → Y → ℝ) (hw1 : ∀ i, ∑ y, w i y = 1)
    (η : ι → Y → ℝ) (h0 : ∀ i, ∑ y, w i y * η i y = 0) (i j : ι) :
    ∑ V : ι → Y, (∏ k, w k (V k)) * (η i (V i) * η j (V j))
      = if i = j then ∑ y, w i y * η i y ^ 2 else 0 := by
  have key : ∀ V : ι → Y, (∏ k, w k (V k)) * (η i (V i) * η j (V j)) =
      ∏ k, (w k (V k) * ((if k = i then η i (V k) else 1) * (if k = j then η j (V k) else 1))) := by
    intro V
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']
  simp_rw [key]
  rw [sum_prod_mul w (fun k y => (if k = i then η i y else 1) * (if k = j then η j y else 1))]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    rw [Finset.prod_eq_single i]
    · simp [sq, mul_assoc]
    · intro k _ hk
      simp [hk, hw1]
    · simp
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hij, h0 i]

theorem var_sum {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] (w : ι → Y → ℝ) (hw1 : ∀ i, ∑ y, w i y = 1)
    (η : ι → Y → ℝ) (h0 : ∀ i, ∑ y, w i y * η i y = 0) :
    ∑ V : ι → Y, (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2 = ∑ i, ∑ y, w i y * η i y ^ 2 := by
  have e : ∀ V : ι → Y, (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2
      = ∑ i, ∑ j, (∏ k, w k (V k)) * (η i (V i) * η j (V j)) := by
    intro V
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp_rw [cross_term w hw1 η h0 i]
  simp

theorem cheb {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] (w : ι → Y → ℝ) (hw0 : ∀ i y, 0 ≤ w i y)
    (hw1 : ∀ i, ∑ y, w i y = 1) (ζ : ι → Y → ℝ) (hζ : ∀ i y, |ζ i y| ≤ 1) (t : ℝ) (ht : 0 < t) :
    ∑ V : ι → Y, (if ∑ i, ζ i (V i) ≤ (∑ i, ∑ y, w i y * ζ i y) - t then ∏ k, w k (V k) else 0)
      ≤ (Fintype.card ι : ℝ) / t ^ 2 := by
  set m : ι → ℝ := fun i => ∑ y, w i y * ζ i y with hm
  set η : ι → Y → ℝ := fun i y => ζ i y - m i with hη
  have h0 : ∀ i, ∑ y, w i y * η i y = 0 := by
    intro i
    simp only [hη, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
    simp [hm]
  have hvar := var_sum w hw1 η h0
  have hW0 : ∀ V : ι → Y, 0 ≤ ∏ k, w k (V k) := fun V => Finset.prod_nonneg (fun k _ => hw0 k _)
  have hpt : ∀ V : ι → Y, (if ∑ i, ζ i (V i) ≤ (∑ i, ∑ y, w i y * ζ i y) - t then ∏ k, w k (V k) else 0)
      ≤ (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2 / t ^ 2 := by
    intro V
    split_ifs with hc
    · have h1 : ∑ i, η i (V i) = ∑ i, ζ i (V i) - ∑ i, ∑ y, w i y * ζ i y := by
        simp only [hη, Finset.sum_sub_distrib, hm]
      have h2 : t ^ 2 ≤ (∑ i, η i (V i)) ^ 2 := by
        rw [h1]; nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc (∏ k, w k (V k)) * t ^ 2 ≤ (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (hW0 V)
        _ = _ := by ring
    · exact div_nonneg (mul_nonneg (hW0 V) (sq_nonneg _)) (sq_nonneg _)
  calc _ ≤ ∑ V : ι → Y, (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2 / t ^ 2 := Finset.sum_le_sum (fun V _ => hpt V)
    _ = (∑ V : ι → Y, (∏ k, w k (V k)) * (∑ i, η i (V i)) ^ 2) / t ^ 2 := by rw [Finset.sum_div]
    _ ≤ (Fintype.card ι : ℝ) / t ^ 2 := by
      rw [hvar]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have : ∀ i, ∑ y, w i y * η i y ^ 2 ≤ 1 := by
        intro i
        have e : ∑ y, w i y * η i y ^ 2 = ∑ y, w i y * ζ i y ^ 2 - m i ^ 2 := by
          have : ∀ y, w i y * η i y ^ 2 = w i y * ζ i y ^ 2 - 2 * m i * (w i y * ζ i y) + m i ^ 2 * w i y := by
            intro y; simp only [hη]; ring
          simp_rw [this]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1]
          have : ∑ y, w i y * ζ i y = m i := rfl
          rw [this]; ring
        rw [e]
        have : ∑ y, w i y * ζ i y ^ 2 ≤ ∑ y, w i y * 1 := by
          apply Finset.sum_le_sum; intro y _
          apply mul_le_mul_of_nonneg_left _ (hw0 i y)
          have := hζ i y
          have h3 : ζ i y ^ 2 ≤ 1 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (ζ i y)]
          exact h3
        simp only [mul_one, hw1] at this
        nlinarith [sq_nonneg (m i)]
      calc ∑ i, ∑ y, w i y * η i y ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => this i)
        _ = _ := by simp



def merge {I : Type} {Y : Type} (p : I → Prop) [DecidablePred p] (T : {x // p x} → Y)
    (V : {x // ¬ p x} → Y) : I → Y :=
  fun x => if h : p x then T ⟨x, h⟩ else V ⟨x, h⟩

theorem split_sum {I : Type} [Fintype I] [DecidableEq I] {Y : Type} [Fintype Y] (p : I → Prop) [DecidablePred p]
    (c : I → Y → ℝ) (φ : (I → Y) → ℝ) :
    ∑ F : I → Y, (∏ x, c x (F x)) * φ F =
      ∑ T : {x // p x} → Y, ∑ V : {x // ¬ p x} → Y,
        ((∏ x : {x // p x}, c x.1 (T x)) * (∏ x : {x // ¬ p x}, c x.1 (V x))) *
          φ (merge p T V) := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Y)
  rw [← Fintype.sum_equiv e.symm (fun q => (∏ x, c x (e.symm q x)) * φ (e.symm q)) _ (fun q => rfl),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro T _
  apply Finset.sum_congr rfl; intro V _
  have h1 : e.symm (T, V) = merge p T V := rfl
  rw [h1]
  congr 1
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  · refine Fintype.prod_congr _ _ (fun x => ?_)
    simp [merge, x.2]
  · refine Fintype.prod_congr _ _ (fun x => ?_)
    simp [merge, x.2]


theorem sum_prod_one {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y] (w : I → Y → ℝ)
    (hw : ∀ i, ∑ y, w i y = 1) : ∑ T : I → Y, ∏ i, w i (T i) = 1 := by
  have := sum_prod_mul w (fun _ _ => (1 : ℝ))
  simpa [hw] using this

theorem test_bound {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y] (w0 w1 : I → Y → ℝ)
    (h0 : ∀ i y, 0 ≤ w0 i y) (h1 : ∀ i y, 0 ≤ w1 i y)
    (s0 : ∀ i, ∑ y, w0 i y = 1) (s1 : ∀ i, ∑ y, w1 i y = 1) (test : (I → Y) → Bool) :
    (∏ i, ∑ y, Real.sqrt (w0 i y * w1 i y)) ^ 2 ≤
      2 * ∑ T : I → Y, (if test T then ∏ i, w0 i (T i) else ∏ i, w1 i (T i)) := by
  classical
  set q0 : (I → Y) → ℝ := fun T => ∏ i, w0 i (T i) with hq0
  set q1 : (I → Y) → ℝ := fun T => ∏ i, w1 i (T i) with hq1
  have q0n : ∀ T, 0 ≤ q0 T := fun T => Finset.prod_nonneg (fun i _ => h0 i _)
  have q1n : ∀ T, 0 ≤ q1 T := fun T => Finset.prod_nonneg (fun i _ => h1 i _)
  set r : (I → Y) → ℝ := fun T => if test T then q0 T else q1 T with hr
  set o : (I → Y) → ℝ := fun T => if test T then q1 T else q0 T with ho
  have rn : ∀ T, 0 ≤ r T := fun T => by simp only [hr]; split_ifs <;> simp [q0n, q1n]
  have on : ∀ T, 0 ≤ o T := fun T => by simp only [ho]; split_ifs <;> simp [q0n, q1n]
  have hro : ∀ T, r T * o T = q0 T * q1 T := by
    intro T; simp only [hr, ho]; split_ifs <;> ring
  have hsum : ∑ T, o T ≤ 2 := by
    have : ∑ T, o T ≤ ∑ T, (q0 T + q1 T) := by
      apply Finset.sum_le_sum; intro T _
      simp only [ho]; split_ifs <;> linarith [q0n T, q1n T]
    rw [Finset.sum_add_distrib] at this
    have e0 := sum_prod_one w0 s0
    have e1 := sum_prod_one w1 s1
    simp only [hq0, hq1] at this
    linarith
  have hprod : ∀ T, ∏ i, Real.sqrt (w0 i (T i) * w1 i (T i)) = Real.sqrt (r T) * Real.sqrt (o T) := by
    intro T
    rw [← Real.sqrt_mul (rn T), hro T]
    simp only [hq0, hq1]
    rw [Real.sqrt_mul (Finset.prod_nonneg (fun i _ => h0 i _)), Real.sqrt_prod _ (fun i _ => h0 i _),
      Real.sqrt_prod _ (fun i _ => h1 i _), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => Real.sqrt_mul (h0 i _) _)
  have hfac : ∏ i, ∑ y, Real.sqrt (w0 i y * w1 i y) = ∑ T : I → Y, ∏ i, Real.sqrt (w0 i (T i) * w1 i (T i)) := by
    have := sum_prod_mul (fun i y => Real.sqrt (w0 i y * w1 i y)) (fun _ _ => (1 : ℝ))
    simpa using this.symm
  rw [hfac]
  simp_rw [hprod]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun T => Real.sqrt (r T)) (fun T => Real.sqrt (o T))
  simp only [Real.sq_sqrt (rn _), Real.sq_sqrt (on _)] at cs
  have hrs : 0 ≤ ∑ T, r T := Finset.sum_nonneg (fun T _ => rn T)
  calc _ ≤ (∑ T, r T) * ∑ T, o T := cs
    _ ≤ (∑ T, r T) * 2 := mul_le_mul_of_nonneg_left hsum hrs
    _ = _ := by ring


section Model

variable (ℓ : ℕ)

def side (y : Fin (2 * ℓ)) : Bool := decide (ℓ ≤ y.val)

def sg (θ : Bool) (y : Fin (2 * ℓ)) : ℝ := if side ℓ y = θ then 1 else -1

noncomputable def pd (ε : ℝ) (θ : Bool) (y : Fin (2 * ℓ)) : ℝ := (1 + 4 * ε * sg ℓ θ y) / (2 * ℓ)

theorem card_side (θ : Bool) :
    (Finset.univ.filter (fun y : Fin (2 * ℓ) => side ℓ y = θ)).card = ℓ := by
  classical
  have hlt : (Finset.univ.filter (fun y : Fin (2 * ℓ) => y.val < ℓ)).card = ℓ := by
    have : (Finset.univ.filter (fun y : Fin (2 * ℓ) => y.val < ℓ)) =
        (Finset.univ : Finset (Fin ℓ)).map (Fin.castLEEmb (by omega : ℓ ≤ 2 * ℓ)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨⟨y.val, h⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩; exact a.2
    rw [this]; simp
  have hge : (Finset.univ.filter (fun y : Fin (2 * ℓ) => ℓ ≤ y.val)).card = ℓ := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * ℓ))))
      (fun y => y.val < ℓ)
    simp only [Finset.card_univ, Fintype.card_fin, not_lt] at h1
    omega
  cases θ
  · simpa [side] using hlt
  · simpa [side] using hge

theorem sum_sg (θ : Bool) : ∑ y : Fin (2 * ℓ), sg ℓ θ y = 0 := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (2 * ℓ))))
    (fun y => side ℓ y = θ) (fun y => sg ℓ θ y)
  have h2 := card_side ℓ θ
  have h3 : (Finset.univ.filter (fun y : Fin (2 * ℓ) => ¬ side ℓ y = θ)).card = ℓ := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * ℓ))))
      (fun y => side ℓ y = θ)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have e1 : ∑ y ∈ Finset.univ.filter (fun y : Fin (2 * ℓ) => side ℓ y = θ), sg ℓ θ y = ℓ := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp [h2]
    · intro y hy; simp [sg, (Finset.mem_filter.mp hy).2]
  have e2 : ∑ y ∈ Finset.univ.filter (fun y : Fin (2 * ℓ) => ¬ side ℓ y = θ), sg ℓ θ y = -ℓ := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℝ))]
    · simp [h3]
    · intro y hy; simp [sg, (Finset.mem_filter.mp hy).2]
  rw [← h1, e1, e2]; ring

theorem sg_flip (y : Fin (2 * ℓ)) : sg ℓ true y = - sg ℓ false y := by
  unfold sg; cases h : side ℓ y <;> simp

theorem sg_sq (θ : Bool) (y : Fin (2 * ℓ)) : sg ℓ θ y * sg ℓ θ y = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem sg_abs (θ : Bool) (y : Fin (2 * ℓ)) : |sg ℓ θ y| ≤ 1 := by
  unfold sg; split_ifs <;> norm_num

variable {ℓ}

theorem pd_nonneg (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (θ : Bool) (y : Fin (2 * ℓ)) :
    0 ≤ pd ℓ ε θ y := by
  unfold pd
  have := sg_abs ℓ θ y
  have h2 : 0 < (2 * (ℓ : ℝ)) := by have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
                                    linarith
  apply div_nonneg _ h2.le
  rcases abs_le.mp this with ⟨a, b⟩
  nlinarith

theorem pd_sum (hℓ : 1 ≤ ℓ) (ε : ℝ) (θ : Bool) : ∑ y : Fin (2 * ℓ), pd ℓ ε θ y = 1 := by
  unfold pd
  have h2 : (2 * (ℓ : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sg]
  simp
  omega

theorem pd_pair (hℓ : 1 ≤ ℓ) (ε : ℝ) (y : Fin (2 * ℓ)) :
    pd ℓ ε false y * pd ℓ ε true y = (1 - 16 * ε ^ 2) / (4 * (ℓ : ℝ) ^ 2) := by
  unfold pd
  have h2 : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  rw [sg_flip]
  have := sg_sq ℓ false y
  field_simp
  nlinarith [this]

theorem pd_sqrt_sum (hℓ : 1 ≤ ℓ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) :
    ∑ y : Fin (2 * ℓ), Real.sqrt (pd ℓ ε false y * pd ℓ ε true y) = Real.sqrt (1 - 16 * ε ^ 2) := by
  have h2 : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  simp_rw [pd_pair hℓ ε]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sqrt_div (by nlinarith), Real.sqrt_mul (by norm_num), Real.sqrt_sq h2.le]
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  push_cast
  field_simp

theorem pd_list (hℓ : 1 ≤ ℓ) (ε : ℝ) (θ : Bool) (L : Finset (Fin (2 * ℓ))) :
    ∑ y ∈ L, pd ℓ ε θ y = ((L.card : ℝ) + 4 * ε * ∑ y ∈ L, sg ℓ θ y) / (2 * ℓ) := by
  unfold pd
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem pd_half (hℓ : 1 ≤ ℓ) (ε : ℝ) (θ : Bool) :
    ∑ y : Fin (2 * ℓ), pd ℓ ε θ y * (if side ℓ y = θ then 1 else 0) = (1 + 4 * ε) / 2 := by
  classical
  have h2 : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have : ∀ y : Fin (2 * ℓ), pd ℓ ε θ y * (if side ℓ y = θ then 1 else 0) =
      if side ℓ y = θ then (1 + 4 * ε) / (2 * ℓ) else 0 := by
    intro y; unfold pd sg; split_ifs <;> simp
  simp_rw [this]
  rw [← Finset.sum_filter, Finset.sum_const, card_side, nsmul_eq_mul]
  field_simp

end Model


section Good

variable {ℓ : ℕ}

open Classical in
noncomputable def bestc (θ : Bool) {M : ℕ} (F : Fin M → Fin (2 * ℓ)) : ℝ :=
  ((Finset.univ.filter (fun x => side ℓ (F x) = θ)).card : ℝ)

open Classical in
noncomputable def covc {M : ℕ} (L : Fin M → Finset (Fin (2 * ℓ))) (F : Fin M → Fin (2 * ℓ)) : ℝ :=
  ((Finset.univ.filter (fun x => F x ∈ L x)).card : ℝ)

open Classical in
theorem diff_lower {M : ℕ} (p : Fin M → Prop) [DecidablePred p] (θ : Bool)
    (L : Fin M → Finset (Fin (2 * ℓ))) (T : {x // p x} → Fin (2 * ℓ))
    (V : {x // ¬ p x} → Fin (2 * ℓ)) :
    -((Finset.univ.filter p).card : ℝ) +
      ∑ x : {x // ¬ p x}, ((if side ℓ (V x) = θ then (1 : ℝ) else 0) - (if V x ∈ L x.1 then 1 else 0))
      ≤ bestc θ (merge p T V) - covc L (merge p T V) := by
  set F := merge p T V with hF
  have e1 : bestc θ F - covc L F = ∑ x : Fin M,
      ((if side ℓ (F x) = θ then (1 : ℝ) else 0) - (if F x ∈ L x then 1 else 0)) := by
    unfold bestc covc
    rw [Finset.sum_sub_distrib, Finset.card_filter, Finset.card_filter]
    push_cast; rfl
  rw [e1, ← Fintype.sum_subtype_add_sum_subtype p]
  have h2 : ∀ x : {x // ¬ p x}, F x.1 = V x := by
    intro x; simp [hF, merge, x.2]
  have h3 : -((Finset.univ.filter p).card : ℝ) ≤ ∑ x : {x // p x},
      ((if side ℓ (F x.1) = θ then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) := by
    have : ∀ x : {x // p x},  (-1 : ℝ) ≤
      ((if side ℓ (F x.1) = θ then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) := by
      intro x; split_ifs <;> norm_num
    calc -((Finset.univ.filter p).card : ℝ) = ∑ _x : {x // p x}, (-1 : ℝ) := by
          simp [Fintype.card_subtype]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => this x)
  have h4 : ∑ x : {x // ¬ p x},
      ((if side ℓ (F x.1) = θ then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) =
      ∑ x : {x // ¬ p x}, ((if side ℓ (V x) = θ then (1 : ℝ) else 0) - (if V x ∈ L x.1 then 1 else 0)) := by
    apply Finset.sum_congr rfl; intro x _; rw [h2]
  linarith

end Good


section Good2

variable {ℓ : ℕ}

theorem good_case (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) (M m : ℕ)
    (hM1 : 16 / ε ^ 2 ≤ M) (hM2 : 8 * m / ε ≤ M) (hM0 : 0 < M)
    (p : Fin M → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).card ≤ m)
    (θ : Bool) (L : Fin M → Finset (Fin (2 * ℓ))) (hL : ∀ x, (L x).card ≤ ℓ)
    (hD : ∑ x : {x // ¬ p x}, ∑ y ∈ L x.1, sg ℓ θ y ≤ 0)
    (T : {x // p x} → Fin (2 * ℓ)) :
    3 / 4 ≤ ∑ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ x, pd ℓ ε θ (V x)) *
      (if ε * M < bestc θ (merge p T V) - covc L (merge p T V) then 1 else 0) := by
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  set ζ : {x // ¬ p x} → Fin (2 * ℓ) → ℝ := fun x y =>
    (if side ℓ y = θ then (1 : ℝ) else 0) - (if y ∈ L x.1 then 1 else 0) with hζ
  have hζb : ∀ x y, |ζ x y| ≤ 1 := by
    intro x y; simp only [hζ]; split_ifs <;> norm_num
  set Ex : ℝ := ∑ x : {x // ¬ p x}, ∑ y, pd ℓ ε θ y * ζ x y with hEx
  have hExlow : 2 * ε * ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) ≤ Ex := by
    have h1 : ∀ x : {x // ¬ p x}, 2 * ε - 2 * ε / ℓ * ∑ y ∈ L x.1, sg ℓ θ y ≤ ∑ y, pd ℓ ε θ y * ζ x y := by
      intro x
      have e : ∑ y, pd ℓ ε θ y * ζ x y =
          (1 + 4 * ε) / 2 - ∑ y ∈ L x.1, pd ℓ ε θ y := by
        simp only [hζ, mul_sub, Finset.sum_sub_distrib, pd_half hℓ]
        congr 1
        simp [Finset.sum_ite_mem]
      rw [e, pd_list hℓ]
      have hc : ((L x.1).card : ℝ) ≤ ℓ := by exact_mod_cast hL x.1
      have : ((L x.1).card + 4 * ε * ∑ y ∈ L x.1, sg ℓ θ y) / (2 * ℓ) ≤
          (ℓ + 4 * ε * ∑ y ∈ L x.1, sg ℓ θ y) / (2 * ℓ) := by
        apply div_le_div_of_nonneg_right _ (by positivity); linarith
      have e2 : (ℓ + 4 * ε * ∑ y ∈ L x.1, sg ℓ θ y) / (2 * ℓ) =
          1 / 2 + 2 * ε / ℓ * ∑ y ∈ L x.1, sg ℓ θ y := by
        field_simp
        ring
      linarith
    have h2 : ∑ x : {x // ¬ p x}, (2 * ε - 2 * ε / ℓ * ∑ y ∈ L x.1, sg ℓ θ y) ≤ Ex :=
      Finset.sum_le_sum (fun x _ => h1 x)
    rw [Finset.sum_sub_distrib] at h2
    have hb : ∑ x : {x // ¬ p x}, 2 * ε / ℓ * ∑ y ∈ L x.1, sg ℓ θ y =
        2 * ε / ℓ * ∑ x : {x // ¬ p x}, ∑ y ∈ L x.1, sg ℓ θ y := (Finset.mul_sum _ _ _).symm
    rw [hb] at h2
    have h3 : 0 ≤ 2 * ε / ℓ * (-∑ x : {x // ¬ p x}, ∑ y ∈ L x.1, sg ℓ θ y) :=
      mul_nonneg (by positivity) (by linarith)
    have h4 : ∑ _x : {x // ¬ p x}, (2 * ε) = 2 * ε * ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) := by
      simp [Fintype.card_subtype]; ring
    linarith
  have hw0 : ∀ (_i : {x // ¬ p x}) (y : Fin (2 * ℓ)), 0 ≤ pd ℓ ε θ y :=
    fun _ y => pd_nonneg hℓ hε0.le (by linarith) θ y
  have hw1 : ∀ _i : {x // ¬ p x}, ∑ y, pd ℓ ε θ y = 1 := fun _ => pd_sum hℓ ε θ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have ht : 0 < ε * M / 2 := by positivity
  have hch := cheb (fun (_i : {x // ¬ p x}) y => pd ℓ ε θ y) hw0 hw1 ζ hζb (ε * M / 2) ht
  have hcard : (Fintype.card {x // ¬ p x} : ℝ) ≤ M := by
    have : Fintype.card {x // ¬ p x} ≤ M := by
      calc _ ≤ Fintype.card (Fin M) := Fintype.card_subtype_le _
        _ = M := Fintype.card_fin M
    exact_mod_cast this
  have hbound : (Fintype.card {x // ¬ p x} : ℝ) / (ε * M / 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h16 : 16 ≤ ε ^ 2 * M := by
      rw [div_le_iff₀ (by positivity)] at hM1; linarith
    have : (ε * M / 2) ^ 2 = ε ^ 2 * M * M / 4 := by ring
    rw [this]
    have hh : (Fintype.card {x // ¬ p x} : ℝ) ≤ M := hcard
    nlinarith
  -- the pointwise inequality
  have hcnt : ((Finset.univ.filter p).card : ℝ) + ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) = M := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M))) p
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hpR : ((Finset.univ.filter p).card : ℝ) ≤ m := by exact_mod_cast hp
  have hmε : (m : ℝ) ≤ ε * M / 8 := by
    rw [div_le_iff₀ hε0] at hM2; linarith
  have hpt : ∀ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ k, pd ℓ ε θ (V k)) -
      (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pd ℓ ε θ y * ζ x y) - ε * M / 2 then ∏ k, pd ℓ ε θ (V k) else 0)
      ≤ (∏ k, pd ℓ ε θ (V k)) * (if ε * M < bestc θ (merge p T V) - covc L (merge p T V) then 1 else 0) := by
    intro V
    have hW : 0 ≤ (∏ k, pd ℓ ε θ (V k)) := Finset.prod_nonneg (fun k _ => hw0 k _)
    by_cases hc : ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pd ℓ ε θ y * ζ x y) - ε * M / 2
    · rw [if_pos hc]
      rw [sub_self]
      exact mul_nonneg hW (by split_ifs <;> norm_num)
    · rw [if_neg hc]
      push Not at hc
      have hd := diff_lower p θ L T V
      have : ε * M < bestc θ (merge p T V) - covc L (merge p T V) := by
        have h5 : ∑ x : {x // ¬ p x}, ((if side ℓ (V x) = θ then (1 : ℝ) else 0) - (if V x ∈ L x.1 then 1 else 0))
            = ∑ x, ζ x (V x) := rfl
        rw [h5] at hd
        simp only [hEx] at hc hExlow
        have ho0 : (0 : ℝ) ≤ ((Finset.univ.filter p).card : ℝ) := Nat.cast_nonneg _
        have h6 : ε * ((Finset.univ.filter p).card : ℝ) ≤ ((Finset.univ.filter p).card : ℝ) / 8 := by
          nlinarith
        have h7 : 0 < ε * M := by positivity
        have h8 : 2 * ε * ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) =
            2 * ε * M - 2 * (ε * ((Finset.univ.filter p).card : ℝ)) := by
          have : ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) = M - ((Finset.univ.filter p).card : ℝ) := by
            linarith
          rw [this]; ring
        linarith
      rw [if_pos this]; simp
  have hsumW : ∑ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ k, pd ℓ ε θ (V k)) = 1 :=
    sum_prod_one (fun (_ : {x // ¬ p x}) y => pd ℓ ε θ y) hw1
  calc (3 : ℝ) / 4 ≤ ∑ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ k, pd ℓ ε θ (V k)) -
        ∑ V : {x // ¬ p x} → Fin (2 * ℓ),
          (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pd ℓ ε θ y * ζ x y) - ε * M / 2 then ∏ k, pd ℓ ε θ (V k) else 0) := by
        rw [hsumW]; linarith
    _ = ∑ V : {x // ¬ p x} → Fin (2 * ℓ), ((∏ k, pd ℓ ε θ (V k)) -
          (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pd ℓ ε θ y * ζ x y) - ε * M / 2 then ∏ k, pd ℓ ε θ (V k) else 0)) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun V _ => hpt V)

end Good2


section Point

variable {ℓ : ℕ}

theorem point_main (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) (M m : ℕ)
    (hM1 : 16 / ε ^ 2 ≤ M) (hM2 : 8 * m / ε ≤ M) (hM0 : 0 < M)
    (p : Fin M → Prop) [DecidablePred p] (hO : (Finset.univ.filter p).card ≤ m)
    (Pred : (Fin M → Fin (2 * ℓ)) → Fin M → Finset (Fin (2 * ℓ)))
    (hc : ∀ F x, (Pred F x).card ≤ ℓ)
    (hdep : ∀ F F' : Fin M → Fin (2 * ℓ), (∀ x, p x → F x = F' x) → Pred F = Pred F') :
    3 / 16 * (1 - 16 * ε ^ 2) ^ m ≤ ∑ θ : Bool, 1 / 2 *
      ∑ F : Fin M → Fin (2 * ℓ), (∏ x, pd ℓ ε θ (F x)) *
        (if ε * M < bestc θ F - covc (Pred F) F then 1 else 0) := by
  have hℓ0 : 0 < 2 * ℓ := by omega
  let y0 : Fin (2 * ℓ) := ⟨0, hℓ0⟩
  let V0 : {x // ¬ p x} → Fin (2 * ℓ) := fun _ => y0
  let PT : ({x // p x} → Fin (2 * ℓ)) → Fin M → Finset (Fin (2 * ℓ)) := fun T => Pred (merge p T V0)
  have hmerge : ∀ T V, Pred (merge p T V) = PT T := by
    intro T V
    apply hdep
    intro x hx
    simp [merge, hx]
  let Dsum : ({x // p x} → Fin (2 * ℓ)) → ℝ := fun T =>
    ∑ x : {x // ¬ p x}, ∑ y ∈ PT T x.1, sg ℓ false y
  let test : ({x // p x} → Fin (2 * ℓ)) → Bool := fun T => decide (Dsum T ≤ 0)
  have hsplit : ∀ θ : Bool, ∑ F : Fin M → Fin (2 * ℓ), (∏ x, pd ℓ ε θ (F x)) *
        (if ε * M < bestc θ F - covc (Pred F) F then 1 else 0) =
      ∑ T : {x // p x} → Fin (2 * ℓ), (∏ x : {x // p x}, pd ℓ ε θ (T x)) *
        ∑ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ x : {x // ¬ p x}, pd ℓ ε θ (V x)) *
          (if ε * M < bestc θ (merge p T V) - covc (PT T) (merge p T V) then 1 else 0) := by
    intro θ
    rw [split_sum p (fun _ y => pd ℓ ε θ y) (fun F => (if ε * M < bestc θ F - covc (Pred F) F then 1 else 0))]
    refine Finset.sum_congr (by ext; simp) (fun T _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr (by ext; simp) (fun V _ => ?_)
    rw [hmerge T V, mul_assoc]
  have hgood : ∀ (θ : Bool) (T : {x // p x} → Fin (2 * ℓ)),
      (if (if θ then !test T else test T) = true then (3 : ℝ) / 4 else 0) ≤
      ∑ V : {x // ¬ p x} → Fin (2 * ℓ), (∏ x : {x // ¬ p x}, pd ℓ ε θ (V x)) *
          (if ε * M < bestc θ (merge p T V) - covc (PT T) (merge p T V) then 1 else 0) := by
    intro θ T
    by_cases hg : (if θ then !test T else test T) = true
    · rw [if_pos hg]
      apply good_case hℓ hε0 hε M m hM1 hM2 hM0 p hO θ (PT T)
        (fun x => hc _ x)
      · cases θ
        · simpa [test, Dsum] using hg
        · have h1 : ∀ x : {x // ¬ p x}, ∑ y ∈ PT T x.1, sg ℓ true y = - ∑ y ∈ PT T x.1, sg ℓ false y := by
            intro x; simp [sg_flip, Finset.sum_neg_distrib]
          simp only [h1, Finset.sum_neg_distrib]
          have hg' : ¬ (Dsum T ≤ 0) := by simpa [test] using hg
          push Not at hg'
          change -Dsum T ≤ 0
          linarith
    · rw [if_neg hg]
      apply Finset.sum_nonneg; intro V _
      apply mul_nonneg
      · exact Finset.prod_nonneg (fun x _ => pd_nonneg hℓ hε0.le (by linarith) θ _)
      · split_ifs <;> norm_num
  have hq0 : ∀ (θ : Bool) (T : {x // p x} → Fin (2 * ℓ)), 0 ≤ ∏ x : {x // p x}, pd ℓ ε θ (T x) :=
    fun θ T => Finset.prod_nonneg (fun x _ => pd_nonneg hℓ hε0.le (by linarith) θ _)
  have hstep : ∀ θ : Bool, (1 / 2 : ℝ) * ∑ T : {x // p x} → Fin (2 * ℓ), (∏ x : {x // p x}, pd ℓ ε θ (T x)) *
        (if (if θ then !test T else test T) = true then (3 : ℝ) / 4 else 0) ≤
      1 / 2 * ∑ F : Fin M → Fin (2 * ℓ), (∏ x, pd ℓ ε θ (F x)) *
        (if ε * M < bestc θ F - covc (Pred F) F then 1 else 0) := by
    intro θ
    rw [hsplit θ]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum; intro T _
    exact mul_le_mul_of_nonneg_left (hgood θ T) (hq0 θ T)
  have hR := test_bound (fun (_ : {x // p x}) y => pd ℓ ε false y) (fun (_ : {x // p x}) y => pd ℓ ε true y)
    (fun _ y => pd_nonneg hℓ hε0.le (by linarith) false y)
    (fun _ y => pd_nonneg hℓ hε0.le (by linarith) true y)
    (fun _ => pd_sum hℓ ε false) (fun _ => pd_sum hℓ ε true) test
  have hBC : (∏ _i : {x // p x}, ∑ y : Fin (2 * ℓ), Real.sqrt (pd ℓ ε false y * pd ℓ ε true y)) ^ 2
      = (1 - 16 * ε ^ 2) ^ (Finset.univ.filter p).card := by
    simp_rw [pd_sqrt_sum hℓ ε hε0.le (by linarith)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype, ← pow_mul, mul_comm _ 2, pow_mul,
      Real.sq_sqrt (by nlinarith)]
  have hpow : (1 - 16 * ε ^ 2) ^ m ≤ (1 - 16 * ε ^ 2) ^ (Finset.univ.filter p).card :=
    pow_le_pow_of_le_one (by nlinarith) (by nlinarith) hO
  rw [hBC] at hR
  have hsum : ∑ θ : Bool, (1 / 2 : ℝ) * ∑ T : {x // p x} → Fin (2 * ℓ), (∏ x : {x // p x}, pd ℓ ε θ (T x)) *
        (if (if θ then !test T else test T) = true then (3 : ℝ) / 4 else 0) =
      3 / 8 * ∑ T : {x // p x} → Fin (2 * ℓ), (if test T then ∏ i : {x // p x}, pd ℓ ε false (T i)
        else ∏ i : {x // p x}, pd ℓ ε true (T i)) := by
    rw [Fintype.sum_bool, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    cases h : test T <;> simp [h] <;> ring
  calc 3 / 16 * (1 - 16 * ε ^ 2) ^ m ≤ 3 / 16 * (1 - 16 * ε ^ 2) ^ (Finset.univ.filter p).card := by
        gcongr
    _ ≤ 3 / 8 * ∑ T : {x // p x} → Fin (2 * ℓ), (if test T then ∏ i : {x // p x}, pd ℓ ε false (T i)
        else ∏ i : {x // p x}, pd ℓ ε true (T i)) := by linarith
    _ = _ := hsum.symm
    _ ≤ _ := Finset.sum_le_sum (fun θ _ => hstep θ)

end Point


open DSDensity1246.Main DSDensity1246.Main.Supplement


theorem avg_exists_w {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fc : Finset ι) (w : ι → ℝ≥0∞) (hw : ∀ f, w f ≠ ⊤) (E : ι → Set Ω) (c : ℝ≥0∞)
    (hsum : ∑ f ∈ Fc, w f = 1)
    (h : ∀ x, c ≤ ∑ f ∈ Fc, w f * (E f).indicator 1 x) :
    ∃ f ∈ Fc, c ≤ P (E f) := by
  classical
  by_contra hcon
  push Not at hcon
  have hhull : ∀ f, ∃ M : Set Ω, E f ⊆ M ∧ MeasurableSet M ∧ P M = P (E f) :=
    fun f => ⟨toMeasurable P (E f), subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
      measure_toMeasurable _⟩
  choose M hEM hMm hMP using hhull
  have key : c ≤ ∑ f ∈ Fc, w f * P (E f) := by
    calc c = ∫⁻ x, c ∂P := by simp
      _ ≤ ∫⁻ x, ∑ f ∈ Fc, w f * (M f).indicator 1 x ∂P := by
          apply lintegral_mono
          intro x
          refine (h x).trans ?_
          apply Finset.sum_le_sum; intro f _
          gcongr
          exact hEM f
      _ = ∑ f ∈ Fc, ∫⁻ x, w f * (M f).indicator 1 x ∂P := by
          rw [lintegral_finsetSum]
          intro f _
          exact (measurable_one.indicator (hMm f)).const_mul _
      _ = ∑ f ∈ Fc, w f * P (E f) := by
          apply Finset.sum_congr rfl; intro f _
          rw [lintegral_const_mul _ (measurable_one.indicator (hMm f)),
            lintegral_indicator_one (hMm f), hMP f]
  have hne : Fc.Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty] at hh
    rw [hh] at hsum; simp at hsum
  have hlt : ∑ f ∈ Fc, w f * P (E f) < ∑ f ∈ Fc, w f * c := by
    have : ∃ f ∈ Fc, w f ≠ 0 := by
      by_contra hh
      push Not at hh
      have : ∑ f ∈ Fc, w f = 0 := Finset.sum_eq_zero hh
      rw [this] at hsum; simp at hsum
    obtain ⟨f0, hf0, hw0⟩ := this
    rw [← Finset.add_sum_erase Fc _ hf0, ← Finset.add_sum_erase Fc (fun f => w f * c) hf0]
    have hrest : ∑ f ∈ Fc.erase f0, w f * P (E f) ≠ ⊤ := by
      apply ne_of_lt
      apply ENNReal.sum_lt_top.mpr
      intro f _
      exact ENNReal.mul_lt_top (hw f).lt_top (measure_lt_top _ _)
    refine ENNReal.add_lt_add_of_lt_of_le hrest ((ENNReal.mul_lt_mul_iff_right hw0 (hw f0)).mpr (hcon f0 hf0)) (Finset.sum_le_sum (fun f hf => mul_le_mul_right (hcon f (Finset.mem_of_mem_erase hf)).le _))
  have hlt' := hlt
  rw [← Finset.sum_mul, hsum, one_mul] at hlt
  exact absurd (lt_of_le_of_lt key hlt) (lt_irrefl _)


def pt {X Y : Type*} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y) (a : I) : X × Y := (S a, f a)

noncomputable def mkLaw {X Y : Type*} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y)
    (ν : ProbabilityMeasure (I)) : DataLaw (X × Y) :=
  ⟨⊤, letI : MeasurableSpace (X × Y) := ⊤
    ProbabilityMeasure.map ν (f := pt S f) (Measurable.of_discrete).aemeasurable⟩

theorem failure_ge {X Y R : Type*} [MeasurableSpace R] {ℓ : ℕ} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y)
    (ν : ProbabilityMeasure (I)) (ρ : ProbabilityMeasure R) (A : ListLearner X Y R ℓ)
    (ε δ : ℝ) (m : ℕ) (b : ℝ≥0∞) :
    ((Measure.pi (fun _ : Fin m => (ν : Measure (I)))).prod (ρ : Measure R))
      {x | b + ENNReal.ofReal ε <
        listError (mkLaw S f ν) (A ε δ m (fun j => pt S f (x.1 j)) x.2)}
      ≤ failureProbability (mkLaw S f ν) ρ A ε δ m b := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  unfold failureProbability trainingLaw iidLaw
  simp only [mkLaw]
  have h1 : (Measure.pi fun _ : Fin m => ((ν.map hmeas.aemeasurable : ProbabilityMeasure (X × Y)) : Measure (X × Y)))
      = (Measure.pi fun _ : Fin m => (ν : Measure (I))).map (fun s j => pt S f (s j)) := by
    rw [Measure.pi_map_pi (fun _ => hmeas.aemeasurable)]
    simp [ProbabilityMeasure.toMeasure_map]
  have h2 : Measurable (fun (s : Fin m → I) (j : Fin m) => pt S f (s j)) := Measurable.of_discrete
  have h3 := Measure.map_prod_map (Measure.pi fun _ : Fin m => (ν : Measure (I))) (ρ : Measure R) h2
    (measurable_id : Measurable (id : R → R))
  rw [Measure.map_id] at h3
  have h4 := Measure.le_map_apply (h2.prodMap measurable_id).aemeasurable
    (μ := (Measure.pi fun _ : Fin m => (ν : Measure (I))).prod (ρ : Measure R))
    {t : (Fin m → X × Y) × R | b + ENNReal.ofReal ε < listError (mkLaw S f ν) (A ε δ m t.1 t.2)}
  rw [← h3, ← h1] at h4
  exact h4

theorem listError_eq {X Y : Type*} {ℓ : ℕ} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y)
    (ν : ProbabilityMeasure (I)) (μ : ListPredictor X Y ℓ) :
    listError (mkLaw S f ν) μ = (ν : Measure (I)) {a | f a ∉ (μ (S a)).1} := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  unfold listError
  show (Measure.map (pt S f) (ν : Measure (I))) _ = _
  rw [Measure.map_apply hmeas (MeasurableSpace.measurableSet_top)]
  rfl

theorem hypError_eq {X Y : Type*} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y)
    (ν : ProbabilityMeasure (I)) (h : X → Y) :
    hypothesisError (mkLaw S f ν) h = (ν : Measure (I)) {a | h (S a) ≠ f a} := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  unfold hypothesisError
  show (Measure.map (pt S f) (ν : Measure (I))) _ = _
  rw [Measure.map_apply hmeas (MeasurableSpace.measurableSet_top)]
  rfl

theorem bestError_le {X Y : Type*} {I : Type*} [Finite I] [MeasurableSpace I] [DiscreteMeasurableSpace I] (S : I → X) (f : I → Y)
    (ν : ProbabilityMeasure (I)) (H : Set (X → Y)) (h : X → Y) (hH : h ∈ H) :
    bestError (mkLaw S f ν) H ≤ (ν : Measure (I)) {a | h (S a) ≠ f a} := by
  rw [← hypError_eq]
  exact iInf_le (fun h : H => hypothesisError (mkLaw S f ν) h.1) ⟨h, hH⟩

noncomputable def unif (M : ℕ) [NeZero M] : ProbabilityMeasure (Fin M) :=
  ⟨(PMF.uniformOfFintype (Fin M)).toMeasure, inferInstance⟩

theorem unif_filter (M : ℕ) [NeZero M] (P : Fin M → Prop) [DecidablePred P] :
    (unif M : Measure (Fin M)) {a | P a} =
      ENNReal.ofReal (((Finset.univ.filter P).card : ℝ) / M) := by
  show (PMF.uniformOfFintype (Fin M)).toMeasure _ = _
  rw [PMF.toMeasure_apply_fintype _ _]
  have h1 : ∀ x : Fin M, {a | P a}.indicator (⇑(PMF.uniformOfFintype (Fin M))) x =
      if P x then ((M : ℝ≥0∞))⁻¹ else 0 := by
    intro x
    by_cases hx : P x <;> simp [Set.indicator, PMF.uniformOfFintype_apply, hx]
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  rw [ENNReal.ofReal_div_of_pos hM, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]



section Assemble1

variable {ℓ : ℕ}

def yθ (hℓ : 1 ≤ ℓ) (θ : Bool) : Fin (2 * ℓ) :=
  if θ then ⟨ℓ, by omega⟩ else ⟨0, by omega⟩

theorem side_yθ (hℓ : 1 ≤ ℓ) (θ : Bool) : side ℓ (yθ hℓ θ) = θ := by
  cases θ <;> simp [yθ, side]; omega

def hθF (hℓ : 1 ≤ ℓ) {M : ℕ} (θ : Bool) (F : Fin M → Fin (2 * ℓ)) (n : ℕ) : Fin (2 * ℓ) :=
  if hn : n < M then (if side ℓ (F ⟨n, hn⟩) = θ then F ⟨n, hn⟩ else yθ hℓ θ) else yθ hℓ θ

def H1 (ℓ : ℕ) : Set (ℕ → Fin (2 * ℓ)) :=
  {h | (∀ x, side ℓ (h x) = false) ∨ (∀ x, side ℓ (h x) = true)}

theorem hθF_mem (hℓ : 1 ≤ ℓ) {M : ℕ} (θ : Bool) (F : Fin M → Fin (2 * ℓ)) :
    hθF hℓ θ F ∈ H1 ℓ := by
  have : ∀ n, side ℓ (hθF hℓ θ F n) = θ := by
    intro n
    unfold hθF
    split_ifs with h1 h2
    · exact h2
    · exact side_yθ hℓ θ
    · exact side_yθ hℓ θ
  cases θ
  · exact Or.inl this
  · exact Or.inr this

theorem event_of (hℓ : 1 ≤ ℓ) (M : ℕ) [NeZero M] (θ : Bool) (F : Fin M → Fin (2 * ℓ))
    (μ : ListPredictor ℕ (Fin (2 * ℓ)) ℓ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ε * M < bestc θ F - covc (fun a : Fin M => (μ a.val).1) F) :
    (unif M : Measure (Fin M)) {a | hθF hℓ θ F a.val ≠ F a} + ENNReal.ofReal ε <
      listError (mkLaw (fun a : Fin M => a.val) F (unif M)) μ := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  rw [listError_eq, unif_filter, unif_filter, ← ENNReal.ofReal_add (by positivity) hε]
  have e1 : (Finset.univ.filter (fun a : Fin M => hθF hℓ θ F a.val ≠ F a)) =
      Finset.univ.filter (fun a : Fin M => ¬ side ℓ (F a) = θ) := by
    apply Finset.filter_congr
    intro a _
    unfold hθF
    rw [dif_pos a.2]
    have : (⟨a.val, a.2⟩ : Fin M) = a := Fin.ext rfl
    rw [this]
    by_cases hs : side ℓ (F a) = θ
    · simp [hs]
    · simp only [hs, if_false, ne_eq, not_false_eq_true, iff_true]
      intro h2
      apply hs
      rw [← h2]; exact side_yθ hℓ θ
  have c1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M)))
    (fun a => side ℓ (F a) = θ)
  have c2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M)))
    (fun a => F a ∈ (μ a.val).1)
  simp only [Finset.card_univ, Fintype.card_fin] at c1 c2
  have r1 : ((Finset.univ.filter (fun a : Fin M => hθF hℓ θ F a.val ≠ F a)).card : ℝ) = M - bestc θ F := by
    rw [e1]; unfold bestc
    have : ((Finset.univ.filter (fun a : Fin M => ¬ side ℓ (F a) = θ)).card : ℝ) +
        ((Finset.univ.filter (fun a : Fin M => side ℓ (F a) = θ)).card : ℝ) = M := by exact_mod_cast (by omega)
    linarith
  have r2 : ((Finset.univ.filter (fun a : Fin M => F a ∉ (μ a.val).1)).card : ℝ) = M - covc (fun a : Fin M => (μ a.val).1) F := by
    unfold covc
    have : ((Finset.univ.filter (fun a : Fin M => ¬ F a ∈ (μ a.val).1)).card : ℝ) +
        ((Finset.univ.filter (fun a : Fin M => F a ∈ (μ a.val).1)).card : ℝ) = M := by exact_mod_cast (by omega)
    linarith
  have hlt : (((Finset.univ.filter (fun a : Fin M => hθF hℓ θ F a.val ≠ F a)).card : ℝ) / M + ε) <
      ((Finset.univ.filter (fun a : Fin M => F a ∉ (μ a.val).1)).card : ℝ) / M := by
    rw [r1, r2, ← sub_pos]
    have : ((M : ℝ) - covc (fun a : Fin M => (μ a.val).1) F) / M - (((M : ℝ) - bestc θ F) / M + ε) =
        ((bestc θ F - covc (fun a : Fin M => (μ a.val).1) F) - ε * M) / M := by
      field_simp
      ring
    rw [this]
    apply div_pos (by linarith) hM
  have hq : 0 < ((Finset.univ.filter (fun a : Fin M => F a ∉ (μ a.val).1)).card : ℝ) / M := by
    refine lt_of_le_of_lt ?_ hlt
    positivity
  exact (ENNReal.ofReal_lt_ofReal_iff hq).mpr hlt

end Assemble1


theorem const_bound {ε δ : ℝ} {m : ℕ} (hε0 : 0 < ε) (hε1 : ε < 1 / 8) (hδ0 : 0 < δ)
    (hm : (m : ℝ) ≤ Real.log (1 / (8 * δ)) / (64 * ε ^ 2)) :
    δ < 3 / 16 * (1 - 16 * ε ^ 2) ^ m := by
  set t : ℝ := 16 * ε ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 4 := by nlinarith
  have h1 : Real.exp (-(4 * t)) ≤ 1 - t := by
    have h2 := Real.add_one_le_exp (4 * t)
    have h3 : Real.exp (-(4 * t)) = 1 / Real.exp (4 * t) := by rw [Real.exp_neg, one_div]
    rw [h3]
    have h4 : 1 / Real.exp (4 * t) ≤ 1 / (1 + 4 * t) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    refine h4.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 : Real.exp ((m : ℝ) * (-(4 * t))) ≤ (1 - t) ^ m := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 m
  have h6 : (m : ℝ) * (64 * ε ^ 2) ≤ Real.log (1 / (8 * δ)) := by
    rwa [le_div_iff₀ (by positivity)] at hm
  have h7 : 8 * δ ≤ Real.exp ((m : ℝ) * (-(4 * t))) := by
    have : (m : ℝ) * (-(4 * t)) = -((m : ℝ) * (64 * ε ^ 2)) := by rw [ht]; ring
    rw [this]
    have h8 : Real.exp (-Real.log (1 / (8 * δ))) ≤ Real.exp (-((m : ℝ) * (64 * ε ^ 2))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h9 : Real.exp (-Real.log (1 / (8 * δ))) = 8 * δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    linarith
  nlinarith


theorem clause1_prob {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {R : Type*} [MeasurableSpace R] (ρ : ProbabilityMeasure R)
    (A : ListLearner ℕ (Fin (2 * ℓ)) R ℓ) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 8)
    (hδ0 : 0 < δ) (m : ℕ) (hm : (m : ℝ) ≤ Real.log (1 / (8 * δ)) / (64 * ε ^ 2)) :
    ∃ D : DataLaw (ℕ × Fin (2 * ℓ)), D.1 = ⊤ ∧
      ENNReal.ofReal δ < failureProbability D ρ A ε δ m (bestError D (H1 ℓ)) := by
  classical
  set M : ℕ := ⌈16 / ε ^ 2⌉₊ + ⌈8 * (m : ℝ) / ε⌉₊ + 1 with hMdef
  haveI : NeZero M := ⟨by omega⟩
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM1 : 16 / ε ^ 2 ≤ M := by
    have := Nat.le_ceil (16 / ε ^ 2)
    have h2' : ⌈16 / ε ^ 2⌉₊ ≤ M := by omega
    have h2 : ((⌈16 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast h2'
    linarith
  have hM2 : 8 * m / ε ≤ M := by
    have := Nat.le_ceil (8 * (m : ℝ) / ε)
    have h2' : ⌈8 * (m : ℝ) / ε⌉₊ ≤ M := by omega
    have h2 : ((⌈8 * (m : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast h2'
    linarith
  set ν : ProbabilityMeasure (Fin M) := unif M with hν
  set S : Fin M → ℕ := fun a => a.val with hS
  set P : Measure ((Fin m → Fin M) × R) :=
    (Measure.pi (fun _ : Fin m => (ν : Measure (Fin M)))).prod (ρ : Measure R) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set w : Bool × (Fin M → Fin (2 * ℓ)) → ℝ≥0∞ := fun f => ENNReal.ofReal (1 / 2 * ∏ x, pd ℓ ε f.1 (f.2 x)) with hw
  set E : Bool × (Fin M → Fin (2 * ℓ)) → Set ((Fin m → Fin M) × R) := fun f =>
    {x | (ν : Measure (Fin M)) {a | hθF hℓ f.1 f.2 (S a) ≠ f.2 a} + ENNReal.ofReal ε <
      listError (mkLaw S f.2 ν) (A ε δ m (fun j => pt S f.2 (x.1 j)) x.2)} with hE
  have hε2 : ε ≤ 1 / 4 := by linarith
  have hsum : ∑ f ∈ (Finset.univ : Finset (Bool × (Fin M → Fin (2 * ℓ)))), w f = 1 := by
    simp only [hw]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun f _ => mul_nonneg (by norm_num)
      (Finset.prod_nonneg (fun x _ => pd_nonneg hℓ hε0.le hε2 _ _))), Fintype.sum_prod_type,
      Fintype.sum_bool]
    have : ∀ θ : Bool, ∑ F : Fin M → Fin (2 * ℓ), 1 / 2 * ∏ x, pd ℓ ε θ (F x) = 1 / 2 := by
      intro θ
      rw [← Finset.mul_sum, sum_prod_one (fun (_ : Fin M) y => pd ℓ ε θ y) (fun _ => pd_sum hℓ ε θ), mul_one]
    rw [this, this]
    norm_num
  have hpoint : ∀ x : (Fin m → Fin M) × R, ENNReal.ofReal (3 / 16 * (1 - 16 * ε ^ 2) ^ m) ≤
      ∑ f ∈ (Finset.univ : Finset (Bool × (Fin M → Fin (2 * ℓ)))), w f * (E f).indicator 1 x := by
    intro x
    let O : Finset (Fin M) := Finset.univ.image x.1
    let Pred : (Fin M → Fin (2 * ℓ)) → Fin M → Finset (Fin (2 * ℓ)) := fun F a =>
      ((A ε δ m (fun j => pt S F (x.1 j)) x.2) (S a)).1
    have hO : (Finset.univ.filter (fun a => a ∈ O)).card ≤ m := by
      have : Finset.univ.filter (fun a => a ∈ O) = O := by ext a; simp
      rw [this]
      exact (Finset.card_image_le).trans (by simp)
    have hc : ∀ F a, (Pred F a).card ≤ ℓ := fun F a => ((A ε δ m (fun j => pt S F (x.1 j)) x.2) (S a)).2
    have hdep : ∀ F F' : Fin M → Fin (2 * ℓ), (∀ a, a ∈ O → F a = F' a) → Pred F = Pred F' := by
      intro F F' h
      have : (fun j => pt S F (x.1 j)) = (fun j => pt S F' (x.1 j)) := by
        funext j
        simp only [pt]
        rw [h (x.1 j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))]
      simp only [Pred]
      rw [this]
    have hmain := point_main hℓ hε0 hε1 M m hM1 hM2 hM0 (fun a => a ∈ O) hO Pred hc hdep
    have hnn : ∀ f : Bool × (Fin M → Fin (2 * ℓ)), 0 ≤ 1 / 2 * ∏ x, pd ℓ ε f.1 (f.2 x) :=
      fun f => mul_nonneg (by norm_num) (Finset.prod_nonneg (fun x _ => pd_nonneg hℓ hε0.le hε2 _ _))
    have hrew : ∑ θ : Bool, 1 / 2 * ∑ F : Fin M → Fin (2 * ℓ), (∏ x, pd ℓ ε θ (F x)) *
        (if ε * M < bestc θ F - covc (Pred F) F then 1 else 0) =
        ∑ f : Bool × (Fin M → Fin (2 * ℓ)), (1 / 2 * ∏ x, pd ℓ ε f.1 (f.2 x)) *
          (if ε * M < bestc f.1 f.2 - covc (Pred f.2) f.2 then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun θ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun F _ => ?_)
      ring
    calc ENNReal.ofReal (3 / 16 * (1 - 16 * ε ^ 2) ^ m)
        ≤ ENNReal.ofReal (∑ f : Bool × (Fin M → Fin (2 * ℓ)), (1 / 2 * ∏ x, pd ℓ ε f.1 (f.2 x)) *
          (if ε * M < bestc f.1 f.2 - covc (Pred f.2) f.2 then 1 else 0)) :=
          ENNReal.ofReal_le_ofReal (hrew ▸ hmain)
      _ = ∑ f : Bool × (Fin M → Fin (2 * ℓ)), ENNReal.ofReal ((1 / 2 * ∏ x, pd ℓ ε f.1 (f.2 x)) *
          (if ε * M < bestc f.1 f.2 - covc (Pred f.2) f.2 then 1 else 0)) :=
          ENNReal.ofReal_sum_of_nonneg (fun f _ => mul_nonneg (hnn f) (by split_ifs <;> norm_num))
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro f _
          by_cases hcond : ε * M < bestc f.1 f.2 - covc (Pred f.2) f.2
          · have hx : x ∈ E f := event_of hℓ M f.1 f.2 (A ε δ m (fun j => pt S f.2 (x.1 j)) x.2) ε hε0.le hcond
            rw [Set.indicator_of_mem hx]
            simp only [hcond, if_true, mul_one, Pi.one_apply]
            exact le_rfl
          · simp [hcond]
  obtain ⟨f, -, hf⟩ := avg_exists_w P Finset.univ w (fun f => ENNReal.ofReal_ne_top) E _ hsum hpoint
  refine ⟨mkLaw S f.2 ν, rfl, ?_⟩
  have hcb := const_bound hε0 hε1 hδ0 hm
  calc ENNReal.ofReal δ < ENNReal.ofReal (3 / 16 * (1 - 16 * ε ^ 2) ^ m) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hcb
    _ ≤ P (E f) := hf
    _ ≤ P {x | bestError (mkLaw S f.2 ν) (H1 ℓ) + ENNReal.ofReal ε <
          listError (mkLaw S f.2 ν) (A ε δ m (fun j => pt S f.2 (x.1 j)) x.2)} := by
        apply measure_mono
        intro x hx
        have hb := bestError_le S f.2 ν (H1 ℓ) (hθF hℓ f.1 f.2) (hθF_mem hℓ f.1 f.2)
        exact lt_of_le_of_lt (add_le_add_left hb _) hx
    _ ≤ _ := failure_ge S f.2 ν ρ A ε δ m _


section Dim1

variable {ℓ : ℕ}

theorem proj_side {d : ℕ} (S : Fin d → ℕ) (w : Fin d → Fin (2 * ℓ))
    (hw : w ∈ MulticlassDS.Compress.proj (H1 ℓ) S) (i j : Fin d) : side ℓ (w i) = side ℓ (w j) := by
  obtain ⟨h, hh, rfl⟩ := hw
  rcases hh with hh | hh
  · simp [hh]
  · simp [hh]

theorem both_sides (hℓ : 1 ≤ ℓ) (A : Finset (Fin (2 * ℓ))) (hA : A.card = ℓ + 1) (θ : Bool) :
    ∃ a ∈ A, side ℓ a = θ := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : A ⊆ Finset.univ.filter (fun y : Fin (2 * ℓ) => side ℓ y = !θ) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hcon a ha
    cases θ <;> cases h : side ℓ a <;> simp_all
  have := Finset.card_le_card hsub
  rw [card_side] at this
  omega

theorem nat_not_shatter (hℓ : 1 ≤ ℓ) {d : ℕ} (hd : 2 ≤ d) (S : Fin d → ℕ) :
    ¬ ListNatShatters ℓ (H1 ℓ) S := by
  classical
  rintro ⟨A, hA, hproj⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  obtain ⟨a, ha, hsa⟩ := both_sides hℓ (A i0) (hA i0) false
  obtain ⟨b, hb, hsb⟩ := both_sides hℓ (A i1) (hA i1) true
  have hne : ∀ i, (A i).Nonempty := fun i => by
    rw [← Finset.card_pos, hA i]; omega
  let w : Fin d → Fin (2 * ℓ) := fun i =>
    if i = i0 then a else if i = i1 then b else (hne i).choose
  have hw : ∀ i, w i ∈ A i := by
    intro i
    by_cases h0 : i = i0
    · subst h0; simpa [w] using ha
    · by_cases h1 : i = i1
      · subst h1; simpa [w, h0] using hb
      · simpa [w, h0, h1] using (hne i).choose_spec
  have := proj_side S w (hproj w hw) i0 i1
  simp [w, h01, hsa, hsb] at this

theorem natDim_H1 (hℓ : 1 ≤ ℓ) : listNatDim ℓ (H1 ℓ) = 1 := by
  classical
  apply le_antisymm
  · apply iSup₂_le
    intro d S
    apply iSup_le
    intro hS
    have : d ≤ 1 := by
      by_contra h
      exact nat_not_shatter hℓ (by omega) S hS
    exact_mod_cast this
  · obtain ⟨A0, -, hA0⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * ℓ))))
      (n := ℓ + 1) (by simp; omega)
    refine le_iSup_of_le 1 (le_iSup_of_le (fun _ => (0 : ℕ)) (le_iSup_of_le ?_ (by simp)))
    refine ⟨fun _ => A0, fun _ => hA0, ?_⟩
    intro w _
    refine ⟨fun _ => w 0, Or.elim (Classical.em (side ℓ (w 0) = false)) (fun h => Or.inl (fun _ => h))
      (fun h => Or.inr (fun _ => by simpa using h)), ?_⟩
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this; rfl

theorem ds_not_shatter (hℓ : 1 ≤ ℓ) {d : ℕ} (hd : 2 ≤ d) (S : Fin d → ℕ) :
    ¬ ListDSShatters ℓ (H1 ℓ) S := by
  classical
  rintro ⟨F, hFsub, hne, hline⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  obtain ⟨f, hf⟩ := hne
  have hl := hline f hf i0
  set N := F.filter (fun g => DirectionalNeighbor i0 f g) with hN
  set T := (Finset.univ.filter (fun y : Fin (2 * ℓ) => side ℓ y = side ℓ (f i0))).erase (f i0) with hT
  have hTcard : T.card = ℓ - 1 := by
    rw [hT, Finset.card_erase_of_mem (by simp), card_side]
  have hcard : N.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun g => g i0)
    · intro g hg
      have hg' := Finset.mem_filter.mp (show g ∈ N from hg)
      obtain ⟨hgF, hgd⟩ := hg'
      simp only [hT, Finset.coe_erase, Finset.coe_filter, Set.mem_diff, Set.mem_setOf_eq,
        Finset.mem_univ, true_and, Set.mem_singleton_iff]
      refine ⟨?_, fun h => hgd.1 h.symm⟩
      have e1 := proj_side S g (hFsub hgF) i0 i1
      have e2 := proj_side S f (hFsub hf) i0 i1
      rw [e1, e2, hgd.2 i1 h01]
    · intro g hg g' hg' hgg
      have hg1 := (Finset.mem_filter.mp (show g ∈ N from hg)).2
      have hg2 := (Finset.mem_filter.mp (show g' ∈ N from hg')).2
      funext j
      by_cases hj : j = i0
      · subst hj; exact hgg
      · rw [← hg1.2 j hj, ← hg2.2 j hj]
  omega

theorem dsDim_H1 (hℓ : 1 ≤ ℓ) : listDSDim ℓ (H1 ℓ) = 1 := by
  classical
  apply le_antisymm
  · apply iSup₂_le
    intro d S
    apply iSup_le
    intro hS
    have : d ≤ 1 := by
      by_contra h
      exact ds_not_shatter hℓ (by omega) S hS
    exact_mod_cast this
  · refine le_iSup_of_le 1 (le_iSup_of_le (fun _ => (0 : ℕ)) (le_iSup_of_le ?_ (by simp)))
    refine ⟨Finset.univ, ?_, ?_, ?_⟩
    · intro w _
      refine ⟨fun _ => w 0, Or.elim (Classical.em (side ℓ (w 0) = false)) (fun h => Or.inl (fun _ => h))
        (fun h => Or.inr (fun _ => by simpa using h)), ?_⟩
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this; rfl
    · exact ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
    · intro f _ i
      have hi : i = 0 := Subsingleton.elim _ _
      have : ℓ ≤ (Finset.univ.erase (f i)).card := by
        rw [Finset.card_erase_of_mem (by simp)]
        simp; omega
      refine this.trans ?_
      apply Finset.card_le_card_of_injOn (fun y => fun _ : Fin 1 => y)
      · intro y hy
        simp only [Finset.coe_erase, Set.mem_diff, Finset.coe_univ, Set.mem_univ, Set.mem_singleton_iff,
          true_and] at hy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        refine ⟨?_, fun j hj => ?_⟩
        · subst hi
          intro h
          apply hy
          simpa using h.symm
        · exact absurd (Subsingleton.elim j i) hj
      · intro y _ y' _ h
        simpa using congrFun h 0

end Dim1


section Dim2

variable {ℓ d : ℕ}

def H2 (d ℓ : ℕ) : Set ((Fin d × ℕ) → Fin ℓ × Bool) :=
  {h | ∀ b t t', (h (b, t)).1 = (h (b, t')).1 → (h (b, t)).2 = (h (b, t')).2}

theorem proj_cons {d' : ℕ} (S : Fin d' → Fin d × ℕ) (w : Fin d' → Fin ℓ × Bool)
    (hw : w ∈ MulticlassDS.Compress.proj (H2 d ℓ) S) (i i' : Fin d') (hS : (S i).1 = (S i').1)
    (h1 : (w i).1 = (w i').1) : (w i).2 = (w i').2 := by
  obtain ⟨h, hh, rfl⟩ := hw
  have e1 : S i = ((S i).1, (S i).2) := rfl
  have e2 : S i' = ((S i').1, (S i').2) := rfl
  simp only [Function.comp] at h1 ⊢
  rw [e1] at h1 ⊢
  rw [e2] at h1 ⊢
  rw [← hS] at h1 ⊢
  exact hh _ _ _ h1

def opp (y : Fin ℓ × Bool) : Fin ℓ × Bool := (y.1, !y.2)

theorem opp_opp (y : Fin ℓ × Bool) : opp (opp y) = y := by simp [opp]

theorem exists_opp (A B : Finset (Fin ℓ × Bool)) (hA : A.card = ℓ + 1) (hB : B.card = ℓ + 1) :
    ∃ a ∈ A, opp a ∈ B := by
  classical
  have hinj : Function.Injective (opp (ℓ := ℓ)) := by
    intro a b h
    have := congrArg opp h
    simpa [opp_opp] using this
  have hc : (A.image opp).card = ℓ + 1 := by rw [Finset.card_image_of_injective _ hinj, hA]
  have h1 := Finset.card_union_add_card_inter (A.image opp) B
  have h2 : (A.image opp ∪ B).card ≤ 2 * ℓ := by
    calc _ ≤ (Finset.univ : Finset (Fin ℓ × Bool)).card := Finset.card_le_univ _
      _ = 2 * ℓ := by simp [Fintype.card_prod]; ring
  have h3 : 0 < (A.image opp ∩ B).card := by omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp h3
  rw [Finset.mem_inter, Finset.mem_image] at hy
  obtain ⟨⟨a, ha, rfl⟩, hyB⟩ := hy
  exact ⟨a, ha, hyB⟩

theorem nat_le (hℓ : 1 ≤ ℓ) {d' : ℕ} (S : Fin d' → Fin d × ℕ)
    (hS : ListNatShatters ℓ (H2 d ℓ) S) : d' ≤ d := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA, hproj⟩ := hS
  obtain ⟨i, i', hne, hSeq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => (S i).1)
    (by simpa using hlt)
  obtain ⟨a, ha, hb⟩ := exists_opp (A i) (A i') (hA i) (hA i')
  have hne' : ∀ k, (A k).Nonempty := fun k => by
    rw [← Finset.card_pos, hA k]; omega
  let w : Fin d' → Fin ℓ × Bool := fun k =>
    if k = i then a else if k = i' then opp a else (hne' k).choose
  have hw : ∀ k, w k ∈ A k := by
    intro k
    by_cases h0 : k = i
    · subst h0; simpa [w] using ha
    · by_cases h1 : k = i'
      · subst h1; simpa [w, h0] using hb
      · simpa [w, h0, h1] using (hne' k).choose_spec
  have hne2 : i' ≠ i := hne.symm
  have := proj_cons S w (hproj w hw) i i' hSeq (by simp [w, hne2, opp])
  simp [w, hne2, opp] at this

theorem nat_ge (hℓ : 1 ≤ ℓ) : ListNatShatters ℓ (H2 d ℓ) (fun i : Fin d => (i, 0)) := by
  classical
  let A : Fin d → Finset (Fin ℓ × Bool) := fun _ =>
    insert (⟨0, by omega⟩, false) (Finset.univ.image (fun j : Fin ℓ => (j, true)))
  refine ⟨A, ?_, ?_⟩
  · intro i
    simp only [A]
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    · simp
    · simp
  · intro w _
    refine ⟨fun x => w x.1, ?_, rfl⟩
    intro b t t' h
    rfl

theorem natDim_H2 (hℓ : 1 ≤ ℓ) : listNatDim ℓ (H2 d ℓ) = d := by
  classical
  apply le_antisymm
  · apply iSup₂_le
    intro d' S
    apply iSup_le
    intro hS
    exact_mod_cast nat_le hℓ S hS
  · exact le_iSup_of_le d (le_iSup_of_le (fun i : Fin d => (i, 0)) (le_iSup_of_le (nat_ge hℓ) le_rfl))

end Dim2


section Model2

variable {ℓ : ℕ}

def sgn2 (θ : Fin ℓ → Bool) (y : Fin ℓ × Bool) : ℝ := if y.2 = θ y.1 then 1 else -1

noncomputable def pq (γ : ℝ) (θ : Fin ℓ → Bool) (y : Fin ℓ × Bool) : ℝ :=
  (1 + γ * sgn2 θ y) / (2 * ℓ)

theorem sgn2_sq (θ : Fin ℓ → Bool) (y : Fin ℓ × Bool) : sgn2 θ y * sgn2 θ y = 1 := by
  unfold sgn2; split_ifs <;> norm_num

theorem sgn2_abs (θ : Fin ℓ → Bool) (y : Fin ℓ × Bool) : |sgn2 θ y| ≤ 1 := by
  unfold sgn2; split_ifs <;> norm_num

theorem sum_sgn2 (θ : Fin ℓ → Bool) : ∑ y : Fin ℓ × Bool, sgn2 θ y = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero; intro j _
  rw [Fintype.sum_bool]
  unfold sgn2
  cases θ j <;> simp

theorem pq_nonneg (hℓ : 1 ≤ ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1) (θ : Fin ℓ → Bool)
    (y : Fin ℓ × Bool) : 0 ≤ pq γ θ y := by
  unfold pq
  have h2 : 0 < (2 * (ℓ : ℝ)) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  apply div_nonneg _ h2.le
  rcases abs_le.mp (sgn2_abs θ y) with ⟨a, b⟩
  nlinarith

theorem pq_sum (hℓ : 1 ≤ ℓ) (γ : ℝ) (θ : Fin ℓ → Bool) : ∑ y : Fin ℓ × Bool, pq γ θ y = 1 := by
  unfold pq
  have h2 : (2 * (ℓ : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sgn2]
  simp [Fintype.card_prod]
  field_simp

theorem pq_list (γ : ℝ) (θ : Fin ℓ → Bool) (L : Finset (Fin ℓ × Bool)) :
    ∑ y ∈ L, pq γ θ y = ((L.card : ℝ) + γ * ∑ y ∈ L, sgn2 θ y) / (2 * ℓ) := by
  unfold pq
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem pq_half (hℓ : 1 ≤ ℓ) (γ : ℝ) (θ : Fin ℓ → Bool) :
    ∑ y : Fin ℓ × Bool, pq γ θ y * (if y.2 = θ y.1 then 1 else 0) = (1 + γ) / 2 := by
  classical
  have h2 : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  rw [Fintype.sum_prod_type]
  have : ∀ j : Fin ℓ, ∑ s : Bool, pq γ θ (j, s) * (if s = θ j then (1 : ℝ) else 0) = (1 + γ) / (2 * ℓ) := by
    intro j
    rw [Fintype.sum_bool]
    unfold pq sgn2
    cases θ j <;> simp
  simp_rw [this]
  simp
  field_simp

end Model2


section Alg2

variable {ℓ d M : ℕ}

def zeta2 (Θ : Fin d → Fin ℓ → Bool) (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (x : Fin d × Fin M)
    (y : Fin ℓ × Bool) : ℝ :=
  (if y.2 = Θ x.1 y.1 then (1 : ℝ) else 0) - (if y ∈ L x then 1 else 0)

def dl2 (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (j : Fin ℓ) (x : Fin d × Fin M) : ℝ :=
  (if (j, true) ∈ L x then (1 : ℝ) else 0) - (if (j, false) ∈ L x then 1 else 0)

noncomputable def Dsum2 (p : Fin d × Fin M → Prop) [DecidablePred p] (L : Fin d × Fin M → Finset (Fin ℓ × Bool))
    (b : Fin d) (j : Fin ℓ) : ℝ :=
  ∑ t : Fin M, if p (b, t) then 0 else dl2 L j (b, t)

noncomputable def est2 (p : Fin d × Fin M → Prop) [DecidablePred p] (L : Fin d × Fin M → Finset (Fin ℓ × Bool))
    (b : Fin d) (j : Fin ℓ) : Bool := decide (0 < Dsum2 p L b j)

noncomputable def Ham2 (p : Fin d × Fin M → Prop) [DecidablePred p] (L : Fin d × Fin M → Finset (Fin ℓ × Bool))
    (Θ : Fin d → Fin ℓ → Bool) : ℝ :=
  ((Finset.univ.filter (fun i : Fin d × Fin ℓ => est2 p L i.1 i.2 ≠ Θ i.1 i.2)).card : ℝ)

theorem per_x (hℓ : 1 ≤ ℓ) (γ : ℝ) (hγ0 : 0 ≤ γ) (θ : Fin ℓ → Bool) (L : Finset (Fin ℓ × Bool))
    (hL : L.card ≤ ℓ) :
    γ / 2 - γ / (2 * ℓ) * ∑ y ∈ L, sgn2 θ y ≤
      ∑ y : Fin ℓ × Bool, pq γ θ y *
        ((if y.2 = θ y.1 then (1 : ℝ) else 0) - (if y ∈ L then 1 else 0)) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have e : ∑ y : Fin ℓ × Bool, pq γ θ y *
        ((if y.2 = θ y.1 then (1 : ℝ) else 0) - (if y ∈ L then 1 else 0)) =
      (1 + γ) / 2 - ∑ y ∈ L, pq γ θ y := by
    simp only [mul_sub, Finset.sum_sub_distrib, pq_half hℓ]
    congr 1
    simp [Finset.sum_ite_mem]
  rw [e, pq_list]
  have hc : (L.card : ℝ) ≤ ℓ := by exact_mod_cast hL
  have : ((L.card : ℝ) + γ * ∑ y ∈ L, sgn2 θ y) / (2 * ℓ) ≤
      (ℓ + γ * ∑ y ∈ L, sgn2 θ y) / (2 * ℓ) := by
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have e2 : (ℓ + γ * ∑ y ∈ L, sgn2 θ y) / (2 * ℓ) =
      1 / 2 + γ / (2 * ℓ) * ∑ y ∈ L, sgn2 θ y := by
    field_simp
  linarith

theorem sgn_sum_eq (θ : Fin ℓ → Bool) (L : Finset (Fin ℓ × Bool)) :
    ∑ y ∈ L, sgn2 θ y = ∑ j : Fin ℓ, (if θ j then (1 : ℝ) else -1) *
      ((if (j, true) ∈ L then (1 : ℝ) else 0) - (if (j, false) ∈ L then 1 else 0)) := by
  classical
  have h1 : ∑ y ∈ L, sgn2 θ y = ∑ y : Fin ℓ × Bool, if y ∈ L then sgn2 θ y else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext y; simp
  rw [h1, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.sum_bool]
  unfold sgn2
  cases θ j <;> by_cases h1 : (j, true) ∈ L <;> by_cases h2 : (j, false) ∈ L <;> simp [h1, h2]

theorem term_bound (p : Fin d × Fin M → Prop) [DecidablePred p]
    (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (Θ : Fin d → Fin ℓ → Bool) (b : Fin d) (j : Fin ℓ) :
    (if Θ b j then (1 : ℝ) else -1) * Dsum2 p L b j ≤ if est2 p L b j = Θ b j then (M : ℝ) else 0 := by
  classical
  have hb : |Dsum2 p L b j| ≤ M := by
    unfold Dsum2
    calc |∑ t : Fin M, (if p (b, t) then (0 : ℝ) else dl2 L j (b, t))|
        ≤ ∑ t : Fin M, |(if p (b, t) then (0 : ℝ) else dl2 L j (b, t))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin M, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro t _
          unfold dl2
          split_ifs <;> norm_num
      _ = M := by simp
  have hl := abs_le.mp hb
  by_cases h : est2 p L b j = Θ b j
  · rw [if_pos h]
    cases hΘ : Θ b j <;> simp <;> linarith [hl.1, hl.2]
  · rw [if_neg h]
    unfold est2 at h
    cases hΘ : Θ b j
    · rw [hΘ] at h
      have : 0 < Dsum2 p L b j := by
        by_contra hc
        apply h
        simp [hc]
      simp; linarith
    · rw [hΘ] at h
      have : Dsum2 p L b j ≤ 0 := by
        by_contra hc
        push Not at hc
        apply h
        simp [hc]
      simp; linarith

theorem alg2 (hℓ : 1 ≤ ℓ) (γ : ℝ) (hγ0 : 0 ≤ γ) (p : Fin d × Fin M → Prop) [DecidablePred p]
    (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (hL : ∀ x, (L x).card ≤ ℓ)
    (Θ : Fin d → Fin ℓ → Bool) :
    γ / 2 * ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) -
        γ / (2 * ℓ) * (M * ((d : ℝ) * ℓ - Ham2 p L Θ)) ≤
      ∑ x : Fin d × Fin M, if p x then 0 else ∑ y, pq γ (Θ x.1) y * zeta2 Θ L x y := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  set Sx : Fin d × Fin M → ℝ := fun x => ∑ y ∈ L x, sgn2 (Θ x.1) y with hSx
  have step1 : ∑ x : Fin d × Fin M, (if p x then (0 : ℝ) else (γ / 2 - γ / (2 * ℓ) * Sx x)) ≤
      ∑ x : Fin d × Fin M, if p x then 0 else ∑ y, pq γ (Θ x.1) y * zeta2 Θ L x y := by
    apply Finset.sum_le_sum; intro x _
    by_cases hx : p x
    · simp [hx]
    · simp only [hx, if_false]
      exact per_x hℓ γ hγ0 (Θ x.1) (L x) (hL x)
  have step1' : ∑ x : Fin d × Fin M, (if p x then (0 : ℝ) else (γ / 2 - γ / (2 * ℓ) * Sx x)) =
      γ / 2 * ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) -
        γ / (2 * ℓ) * ∑ x : Fin d × Fin M, if p x then 0 else Sx x := by
    have : ∀ x : Fin d × Fin M, (if p x then (0 : ℝ) else (γ / 2 - γ / (2 * ℓ) * Sx x)) =
        (if p x then 0 else γ / 2) - γ / (2 * ℓ) * (if p x then 0 else Sx x) := by
      intro x; by_cases hx : p x <;> simp [hx]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    have h2 : ∀ x : Fin d × Fin M, (if p x then (0 : ℝ) else γ / 2) = if ¬ p x then γ / 2 else 0 := by
      intro x; by_cases hx : p x <;> simp [hx]
    simp_rw [h2]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have step2 : ∑ x : Fin d × Fin M, (if p x then (0 : ℝ) else Sx x) =
      ∑ b : Fin d, ∑ j : Fin ℓ, (if Θ b j then (1 : ℝ) else -1) * Dsum2 p L b j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have : ∀ t : Fin M, (if p (b, t) then (0 : ℝ) else Sx (b, t)) =
        ∑ j : Fin ℓ, (if Θ b j then (1 : ℝ) else -1) * (if p (b, t) then 0 else dl2 L j (b, t)) := by
      intro t
      by_cases hx : p (b, t)
      · simp [hx]
      · simp only [hx, if_false, hSx]
        rw [sgn_sum_eq]
        rfl
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum]
    rfl
  have step3 : ∑ b : Fin d, ∑ j : Fin ℓ, (if Θ b j then (1 : ℝ) else -1) * Dsum2 p L b j ≤
      M * ((d : ℝ) * ℓ - Ham2 p L Θ) := by
    calc _ ≤ ∑ b : Fin d, ∑ j : Fin ℓ, (if est2 p L b j = Θ b j then (M : ℝ) else 0) :=
          Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun j _ => term_bound p L Θ b j))
      _ = ∑ i : Fin d × Fin ℓ, (if est2 p L i.1 i.2 = Θ i.1 i.2 then (M : ℝ) else 0) := by
          rw [Fintype.sum_prod_type]
      _ = M * ((d : ℝ) * ℓ - Ham2 p L Θ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          congr 1
          have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d × Fin ℓ)))
            (fun i : Fin d × Fin ℓ => est2 p L i.1 i.2 = Θ i.1 i.2)
          simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
          unfold Ham2
          have h3 : ((Finset.univ.filter (fun i : Fin d × Fin ℓ => est2 p L i.1 i.2 = Θ i.1 i.2)).card : ℝ) +
              ((Finset.univ.filter (fun i : Fin d × Fin ℓ => ¬ est2 p L i.1 i.2 = Θ i.1 i.2)).card : ℝ) =
              (d : ℝ) * ℓ := by exact_mod_cast this
          have h4 : (Finset.univ.filter (fun i : Fin d × Fin ℓ => est2 p L i.1 i.2 ≠ Θ i.1 i.2)) =
              Finset.univ.filter (fun i : Fin d × Fin ℓ => ¬ est2 p L i.1 i.2 = Θ i.1 i.2) := rfl
          rw [h4]; linarith
  have hnn : 0 ≤ γ / (2 * ℓ) := by positivity
  nlinarith [step1, step1', step2, step3, mul_le_mul_of_nonneg_left (step2 ▸ step3) hnn]

end Alg2


section Good3

variable {ℓ d M : ℕ}

open Classical in
noncomputable def bestc2 (Θ : Fin d → Fin ℓ → Bool) (F : Fin d × Fin M → Fin ℓ × Bool) : ℝ :=
  ((Finset.univ.filter (fun x : Fin d × Fin M => (F x).2 = Θ x.1 (F x).1)).card : ℝ)

open Classical in
noncomputable def covc2 (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (F : Fin d × Fin M → Fin ℓ × Bool) : ℝ :=
  ((Finset.univ.filter (fun x : Fin d × Fin M => F x ∈ L x)).card : ℝ)

open Classical in
theorem diff_lower2 (p : Fin d × Fin M → Prop) [DecidablePred p] (Θ : Fin d → Fin ℓ → Bool)
    (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (T : {x // p x} → Fin ℓ × Bool)
    (V : {x // ¬ p x} → Fin ℓ × Bool) :
    -((Finset.univ.filter p).card : ℝ) + ∑ x : {x // ¬ p x}, zeta2 Θ L x.1 (V x)
      ≤ bestc2 Θ (merge p T V) - covc2 L (merge p T V) := by
  set F := merge p T V with hF
  have e1 : bestc2 Θ F - covc2 L F = ∑ x : Fin d × Fin M,
      ((if (F x).2 = Θ x.1 (F x).1 then (1 : ℝ) else 0) - (if F x ∈ L x then 1 else 0)) := by
    unfold bestc2 covc2
    rw [Finset.sum_sub_distrib, Finset.card_filter, Finset.card_filter]
    push_cast; rfl
  rw [e1, ← Fintype.sum_subtype_add_sum_subtype p]
  have h2 : ∀ x : {x // ¬ p x}, F x.1 = V x := by
    intro x; simp [hF, merge, x.2]
  have h3 : -((Finset.univ.filter p).card : ℝ) ≤ ∑ x : {x // p x},
      ((if (F x.1).2 = Θ x.1.1 (F x.1).1 then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) := by
    have : ∀ x : {x // p x}, (-1 : ℝ) ≤
      ((if (F x.1).2 = Θ x.1.1 (F x.1).1 then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) := by
      intro x; split_ifs <;> norm_num
    calc -((Finset.univ.filter p).card : ℝ) = ∑ _x : {x // p x}, (-1 : ℝ) := by
          simp [Fintype.card_subtype]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => this x)
  have h4 : ∑ x : {x // ¬ p x},
      ((if (F x.1).2 = Θ x.1.1 (F x.1).1 then (1 : ℝ) else 0) - (if F x.1 ∈ L x.1 then 1 else 0)) =
      ∑ x : {x // ¬ p x}, zeta2 Θ L x.1 (V x) := by
    apply Finset.sum_congr rfl; intro x _; rw [h2]; rfl
  linarith

end Good3


theorem numeric2 (ε ℓ d M m u h : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 64) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d)
    (hM : 0 < M) (hm0 : 0 ≤ m) (hu : d * M - m ≤ u) (hh : 3 * d * ℓ / 32 ≤ h)
    (hM2 : 100 * m / ε ≤ M) :
    ε * (d * M) < -m + ((32 * ε / 2 * u - 32 * ε / (2 * ℓ) * (M * (d * ℓ - h))) - 3 / 10 * ε * d * M) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hm : 100 * m ≤ ε * M := by
    rw [div_le_iff₀ hε0] at hM2; linarith
  have hk : 32 * ε / (2 * ℓ) * ℓ = 16 * ε := by field_simp; ring
  have hk0 : 0 ≤ 32 * ε / (2 * ℓ) := by positivity
  set k := 32 * ε / (2 * ℓ) with hkdef
  have e1 : k * (M * (d * ℓ - h)) = M * d * (16 * ε) - k * M * h := by
    rw [← hk]; ring
  have e2 : k * M * h ≥ k * M * (3 * d * ℓ / 32) := by
    apply mul_le_mul_of_nonneg_left hh (by positivity)
  have e3 : k * M * (3 * d * ℓ / 32) = M * d * (16 * ε) * (3 / 32) := by
    rw [← hk]; ring
  have e4 : 32 * ε / 2 * u ≥ 32 * ε / 2 * (d * M - m) := by
    apply mul_le_mul_of_nonneg_left hu (by positivity)
  have hdM : 0 < d * M := by positivity
  nlinarith [mul_pos hε0 hdM, mul_nonneg hε0.le hm0]


section Good4

variable {ℓ d M : ℕ}

theorem good_case2 (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 64) (hd : 1 ≤ d) (m : ℕ)
    (hM1 : 112 / ε ^ 2 ≤ M) (hM2 : 100 * m / ε ≤ M) (hM0 : 0 < M)
    (p : Fin d × Fin M → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).card ≤ m)
    (Θ : Fin d → Fin ℓ → Bool) (L : Fin d × Fin M → Finset (Fin ℓ × Bool))
    (hL : ∀ x, (L x).card ≤ ℓ) (hH : 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p L Θ)
    (T : {x // p x} → Fin ℓ × Bool) :
    9 / 10 ≤ ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ x : {x // ¬ p x}, pq (32 * ε) (Θ x.1.1) (V x)) *
      (if ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 L (merge p T V) then 1 else 0) := by
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hγ0 : (0 : ℝ) ≤ 32 * ε := by positivity
  have hγ1 : 32 * ε ≤ 1 := by linarith
  set ζ : {x // ¬ p x} → Fin ℓ × Bool → ℝ := fun x y => zeta2 Θ L x.1 y with hζ
  have hζb : ∀ x y, |ζ x y| ≤ 1 := by
    intro x y; simp only [hζ, zeta2]; split_ifs <;> norm_num
  have hw0 : ∀ (x : {x // ¬ p x}) (y : Fin ℓ × Bool), 0 ≤ pq (32 * ε) (Θ x.1.1) y :=
    fun x y => pq_nonneg hℓ hγ0 hγ1 _ y
  have hw1 : ∀ x : {x // ¬ p x}, ∑ y, pq (32 * ε) (Θ x.1.1) y = 1 := fun x => pq_sum hℓ _ _
  have hEconv : ∑ x : {x // ¬ p x}, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y =
      ∑ x : Fin d × Fin M, if p x then 0 else ∑ y, pq (32 * ε) (Θ x.1) y * zeta2 Θ L x y := by
    have h := Finset.sum_subtype (p := fun x => ¬ p x) (F := Subtype.fintype _)
      (Finset.univ.filter (fun x => ¬ p x)) (fun x => by simp)
      (fun x : Fin d × Fin M => ∑ y, pq (32 * ε) (Θ x.1) y * zeta2 Θ L x y)
    calc ∑ x : {x // ¬ p x}, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y
        = ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), ∑ y, pq (32 * ε) (Θ x.1) y * zeta2 Θ L x y := h.symm
      _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : p x <;> simp [hx]
  have halg := alg2 hℓ (32 * ε) hγ0 p L hL Θ
  have hcnt : ((Finset.univ.filter p).card : ℝ) + ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) = d * M := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d × Fin M))) p
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this
  have hpR : ((Finset.univ.filter p).card : ℝ) ≤ m := by exact_mod_cast hp
  have hnum := numeric2 ε ℓ d M m ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) (Ham2 p L Θ) hε0 hε
    (by exact_mod_cast hℓ) hdR hMR (Nat.cast_nonneg _) (by linarith) hH hM2
  have ht : 0 < 3 / 10 * ε * d * M := by positivity
  have hch := cheb (fun (x : {x // ¬ p x}) y => pq (32 * ε) (Θ x.1.1) y) hw0 hw1 ζ hζb (3 / 10 * ε * d * M) ht
  have hcard : (Fintype.card {x // ¬ p x} : ℝ) ≤ d * M := by
    have : Fintype.card {x // ¬ p x} ≤ d * M := by
      calc _ ≤ Fintype.card (Fin d × Fin M) := Fintype.card_subtype_le _
        _ = d * M := by simp
    exact_mod_cast this
  have hbound : (Fintype.card {x // ¬ p x} : ℝ) / (3 / 10 * ε * d * M) ^ 2 ≤ 1 / 10 := by
    rw [div_le_iff₀ (by positivity)]
    have h112 : 112 ≤ ε ^ 2 * M := by
      rw [div_le_iff₀ (by positivity)] at hM1; linarith
    have hdM : (1 : ℝ) ≤ d * M := by nlinarith
    have : (3 / 10 * ε * d * M) ^ 2 = 9 / 100 * (ε ^ 2 * M) * (d * (d * M)) := by ring
    rw [this]
    have h2 : (d : ℝ) * M ≤ d * (d * M) := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ε ^ 2 * M - 112) (by positivity : (0:ℝ) ≤ d * M)]
  have hcl := (hEconv ▸ halg)
  have hpt : ∀ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) -
      (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y) - 3 / 10 * ε * d * M
        then ∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k) else 0)
      ≤ (∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) *
        (if ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 L (merge p T V) then 1 else 0) := by
    intro V
    have hW : 0 ≤ (∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) :=
      Finset.prod_nonneg (fun k _ => hw0 k _)
    by_cases hc : ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y) - 3 / 10 * ε * d * M
    · rw [if_pos hc, sub_self]
      exact mul_nonneg hW (by split_ifs <;> norm_num)
    · rw [if_neg hc]
      push Not at hc
      have hd := diff_lower2 p Θ L T V
      have : ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 L (merge p T V) := by
        have h5 : ∑ x : {x // ¬ p x}, zeta2 Θ L x.1 (V x) = ∑ x, ζ x (V x) := rfl
        rw [h5] at hd
        linarith
      rw [if_pos this]; simp
  have hsumW : ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) = 1 :=
    sum_prod_one (fun (x : {x // ¬ p x}) y => pq (32 * ε) (Θ x.1.1) y) hw1
  calc (9 : ℝ) / 10 ≤ ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) -
        ∑ V : {x // ¬ p x} → Fin ℓ × Bool,
          (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y) - 3 / 10 * ε * d * M
            then ∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k) else 0) := by
        rw [hsumW]; linarith
    _ = ∑ V : {x // ¬ p x} → Fin ℓ × Bool, ((∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k)) -
          (if ∑ x, ζ x (V x) ≤ (∑ x, ∑ y, pq (32 * ε) (Θ x.1.1) y * ζ x y) - 3 / 10 * ε * d * M
            then ∏ k : {x // ¬ p x}, pq (32 * ε) (Θ k.1.1) (V k) else 0)) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun V _ => hpt V)

end Good4


section Assouad

variable {ℓ : ℕ}

theorem pq_pair_sum (hℓ : 1 ≤ ℓ) (γ : ℝ) (θ : Fin ℓ → Bool) (j : Fin ℓ) :
    ∑ s : Bool, pq γ θ (j, s) = 1 / ℓ := by
  have h2 : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  rw [Fintype.sum_bool]
  unfold pq sgn2
  cases θ j <;> simp <;> field_simp <;> ring

theorem sqrt_ge_self {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : u ≤ Real.sqrt u := by
  have := Real.abs_le_sqrt (x := u) (y := u) (by nlinarith)
  exact (le_abs_self u).trans this

theorem aff_bound (hℓ : 1 ≤ ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (θ : Fin ℓ → Bool) (j : Fin ℓ) :
    1 - γ ^ 2 / ℓ ≤ ∑ y : Fin ℓ × Bool,
      Real.sqrt (pq γ θ y * pq γ (Function.update θ j (!θ j)) y) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  set θ' := Function.update θ j (!θ j) with hθ'
  have hterm : ∀ y : Fin ℓ × Bool,
      (if y.1 = j then (1 - γ ^ 2) / (2 * ℓ) else pq γ θ y) ≤ Real.sqrt (pq γ θ y * pq γ θ' y) := by
    intro y
    by_cases hy : y.1 = j
    · rw [if_pos hy]
      have hs : sgn2 θ' y = - sgn2 θ y := by
        unfold sgn2
        rw [hy, hθ']
        simp only [Function.update_self]
        cases hh : θ j <;> cases y.2 <;> simp
      have hprod : pq γ θ y * pq γ θ' y = (1 - γ ^ 2) / (2 * ℓ) ^ 2 := by
        unfold pq
        rw [hs]
        have := sgn2_sq θ y
        field_simp
        nlinarith [this]
      rw [hprod, Real.sqrt_div (by nlinarith), Real.sqrt_sq (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact sqrt_ge_self (by nlinarith) (by nlinarith)
    · rw [if_neg hy]
      have hs : sgn2 θ' y = sgn2 θ y := by
        unfold sgn2
        rw [hθ', Function.update_of_ne hy]
      have : pq γ θ' y = pq γ θ y := by unfold pq; rw [hs]
      rw [this, Real.sqrt_mul_self (pq_nonneg hℓ hγ0 hγ1 θ y)]
  refine le_trans ?_ (Finset.sum_le_sum (fun y _ => hterm y))
  rw [Fintype.sum_prod_type]
  have : ∀ j' : Fin ℓ, ∑ s : Bool, (if (j', s).1 = j then (1 - γ ^ 2) / (2 * ℓ) else pq γ θ (j', s)) =
      if j' = j then (1 - γ ^ 2) / (ℓ : ℝ) else (1 : ℝ) / ℓ := by
    intro j'
    by_cases h : j' = j
    · simp [h]; field_simp
    · simp only [h, if_false]
      exact pq_pair_sum hℓ γ θ j'
  simp_rw [this]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton, one_smul]
  have hc : (Finset.univ.filter (fun j' : Fin ℓ => ¬ j' = j)).card = ℓ - 1 := by
    rw [Finset.filter_not, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.card_sdiff]
    simp
  rw [hc, nsmul_eq_mul]
  have : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub hℓ]; simp
  rw [this]
  field_simp
  linarith


variable {d M : ℕ}

def flipb (b : Fin d) (j : Fin ℓ) (Θ : Fin d → Fin ℓ → Bool) : Fin d → Fin ℓ → Bool :=
  Function.update Θ b (Function.update (Θ b) j (!Θ b j))

theorem flipb_flipb (b : Fin d) (j : Fin ℓ) (Θ : Fin d → Fin ℓ → Bool) :
    flipb b j (flipb b j Θ) = Θ := by
  funext b' j'
  unfold flipb
  by_cases hb : b' = b
  · subst hb
    simp only [Function.update_self]
    by_cases hj : j' = j
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · simp [Function.update_of_ne hb]

theorem flipb_self (b : Fin d) (j : Fin ℓ) (Θ : Fin d → Fin ℓ → Bool) :
    flipb b j Θ b j = !Θ b j := by simp [flipb]

theorem factor_bound (hℓ : 1 ≤ ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (b : Fin d) (j : Fin ℓ)
    (Θ : Fin d → Fin ℓ → Bool) (b' : Fin d) :
    (if b' = b then 1 - γ ^ 2 / ℓ else 1) ≤
      ∑ y : Fin ℓ × Bool, Real.sqrt (pq γ (Θ b') y * pq γ (flipb b j Θ b') y) := by
  by_cases h : b' = b
  · subst h
    rw [if_pos rfl]
    have := aff_bound hℓ hγ0 hγ1 (Θ b') j
    simpa [flipb] using this
  · rw [if_neg h]
    have : flipb b j Θ b' = Θ b' := by simp [flipb, Function.update_of_ne h]
    rw [this]
    have h2 : ∀ y, Real.sqrt (pq γ (Θ b') y * pq γ (Θ b') y) = pq γ (Θ b') y :=
      fun y => Real.sqrt_mul_self (pq_nonneg hℓ hγ0 hγ1 _ y)
    simp_rw [h2]
    rw [pq_sum hℓ]


theorem pair_bound (hℓ : 1 ≤ ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (p : Fin d × Fin M → Prop) [DecidablePred p]
    (g : ({x // p x} → Fin ℓ × Bool) → Bool) (b : Fin d) (j : Fin ℓ) (Θ : Fin d → Fin ℓ → Bool) :
    1 / 2 * (1 - γ ^ 2 / ℓ) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) ≤
      (∑ T : {x // p x} → Fin ℓ × Bool, (∏ x : {x // p x}, pq γ (Θ x.1.1) (T x)) *
          (if g T ≠ Θ b j then 1 else 0)) +
      ∑ T : {x // p x} → Fin ℓ × Bool, (∏ x : {x // p x}, pq γ (flipb b j Θ x.1.1) (T x)) *
          (if g T ≠ flipb b j Θ b j then 1 else 0) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  set a0 : ℝ := 1 - γ ^ 2 / ℓ with ha0
  have ha0n : 0 ≤ a0 := by
    rw [ha0, sub_nonneg, div_le_iff₀ hℓR]
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith
  have hw : ∀ (Φ : Fin d → Fin ℓ → Bool) (x : {x // p x}) (y : Fin ℓ × Bool), 0 ≤ pq γ (Φ x.1.1) y :=
    fun Φ x y => pq_nonneg hℓ hγ0 hγ1 _ y
  have hs : ∀ (Φ : Fin d → Fin ℓ → Bool) (x : {x // p x}), ∑ y, pq γ (Φ x.1.1) y = 1 :=
    fun Φ x => pq_sum hℓ _ _
  have htb := test_bound (fun (x : {x // p x}) y => pq γ (Θ x.1.1) y)
    (fun (x : {x // p x}) y => pq γ (flipb b j Θ x.1.1) y) (hw Θ) (hw _) (hs Θ) (hs _)
    (fun T => decide (g T ≠ Θ b j))
  have hsum : (∑ T : {x // p x} → Fin ℓ × Bool, (∏ x : {x // p x}, pq γ (Θ x.1.1) (T x)) *
          (if g T ≠ Θ b j then 1 else 0)) +
      ∑ T : {x // p x} → Fin ℓ × Bool, (∏ x : {x // p x}, pq γ (flipb b j Θ x.1.1) (T x)) *
          (if g T ≠ flipb b j Θ b j then 1 else 0) =
      ∑ T : {x // p x} → Fin ℓ × Bool, (if decide (g T ≠ Θ b j) = true then
        ∏ x : {x // p x}, pq γ (Θ x.1.1) (T x) else ∏ x : {x // p x}, pq γ (flipb b j Θ x.1.1) (T x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [flipb_self]
    cases h : g T <;> cases h2 : Θ b j <;> simp
  rw [hsum]
  have hBC : a0 ^ (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card ≤
      ∏ x : {x // p x}, ∑ y : Fin ℓ × Bool, Real.sqrt (pq γ (Θ x.1.1) y * pq γ (flipb b j Θ x.1.1) y) := by
    have h1 : ∏ x : {x // p x}, (if x.1.1 = b then a0 else 1) =
        a0 ^ (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [← h1]
    exact Finset.prod_le_prod (fun x _ => by split_ifs <;> [exact ha0n; exact zero_le_one])
      (fun x _ => factor_bound hℓ hγ0 hγ1 b j Θ x.1.1)
  have hpow : 0 ≤ a0 ^ (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card := pow_nonneg ha0n _
  have hsq : (a0 ^ (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) ^ 2 ≤
      (∏ x : {x // p x}, ∑ y : Fin ℓ × Bool, Real.sqrt (pq γ (Θ x.1.1) y * pq γ (flipb b j Θ x.1.1) y)) ^ 2 :=
    pow_le_pow_left₀ hpow hBC 2
  have : a0 ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) =
      (a0 ^ (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [this]
  linarith


theorem bit_lower (hℓ : 1 ≤ ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (p : Fin d × Fin M → Prop) [DecidablePred p]
    (g : ({x // p x} → Fin ℓ × Bool) → Bool) (b : Fin d) (j : Fin ℓ) :
    1 / 4 * (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) *
      (1 - γ ^ 2 / ℓ) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) ≤
    ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq γ (Θ x.1.1) (T x)) * (if g T ≠ Θ b j then 1 else 0) := by
  classical
  set f : (Fin d → Fin ℓ → Bool) → ℝ := fun Θ => ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq γ (Θ x.1.1) (T x)) * (if g T ≠ Θ b j then 1 else 0) with hf
  let e : (Fin d → Fin ℓ → Bool) ≃ (Fin d → Fin ℓ → Bool) :=
    Function.Involutive.toPerm (flipb b j) (flipb_flipb b j)
  have h1 : ∑ Θ, f (flipb b j Θ) = ∑ Θ, f Θ := Equiv.sum_comp e f
  have h2 : ∀ Θ, 1 / 2 * (1 - γ ^ 2 / ℓ) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card)
      ≤ f Θ + f (flipb b j Θ) := fun Θ => pair_bound hℓ hγ0 hγ1 p g b j Θ
  have h3 : ∑ Θ : Fin d → Fin ℓ → Bool,
      1 / 2 * (1 - γ ^ 2 / ℓ) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card)
      ≤ ∑ Θ, (f Θ + f (flipb b j Θ)) := Finset.sum_le_sum (fun Θ _ => h2 Θ)
  rw [Finset.sum_add_distrib, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
  show _ ≤ ∑ Θ, f Θ
  nlinarith [h3]


theorem sum_nb (p : Fin d × Fin M → Prop) [DecidablePred p] :
    ∑ b : Fin d, ((Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card : ℝ) =
      ((Finset.univ.filter p).card : ℝ) := by
  classical
  have h1 : ∑ b : Fin d, (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card =
      (Finset.univ : Finset {x // p x}).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : {x // p x} => x.1.1) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
  rw [Finset.card_univ, Fintype.card_subtype] at h1
  exact_mod_cast h1

theorem claimA (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 64) (hd : 1 ≤ d) (m : ℕ)
    (hm : (m : ℝ) ≤ (ℓ : ℝ) * d / (32768 * ε ^ 2))
    (p : Fin d × Fin M → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).card ≤ m)
    (G : Fin d → Fin ℓ → ({x // p x} → Fin ℓ × Bool) → Bool) :
    15 / 64 * (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) * ((d : ℝ) * ℓ) ≤
    ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        (∑ i : Fin d × Fin ℓ, if G i.1 i.2 T ≠ Θ i.1 i.2 then (1 : ℝ) else 0) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hγ0 : (0 : ℝ) ≤ 32 * ε := by positivity
  have hγ1 : 32 * ε ≤ 1 := by linarith
  set K : ℝ := (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have h1 : ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        (∑ i : Fin d × Fin ℓ, if G i.1 i.2 T ≠ Θ i.1 i.2 then (1 : ℝ) else 0) =
      ∑ i : Fin d × Fin ℓ, ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * (if G i.1 i.2 T ≠ Θ i.1 i.2 then 1 else 0) := by
    calc _ = ∑ Θ : Fin d → Fin ℓ → Bool, ∑ i : Fin d × Fin ℓ, ∑ T : {x // p x} → Fin ℓ × Bool,
          (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * (if G i.1 i.2 T ≠ Θ i.1 i.2 then 1 else 0) := by
          refine Finset.sum_congr rfl (fun Θ _ => ?_)
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [h1]
  set s : ℝ := (32 * ε) ^ 2 / ℓ with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hℓR]
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith
  have hbern : ∀ n : ℕ, 1 - (2 * n) * s ≤ (1 - s) ^ (2 * n) := by
    intro n
    have e : (1 - s) = 1 + (-s) := by ring
    rw [e]
    have := one_add_mul_le_pow (a := -s) (by linarith) (2 * n)
    push_cast at this
    linarith
  have h2 : ∀ i : Fin d × Fin ℓ,
      1 / 4 * K * (1 - s) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = i.1)).card) ≤
      ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * (if G i.1 i.2 T ≠ Θ i.1 i.2 then 1 else 0) :=
    fun i => bit_lower hℓ hγ0 hγ1 p (G i.1 i.2) i.1 i.2
  refine le_trans ?_ (Finset.sum_le_sum (fun i _ => h2 i))
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : ∀ b : Fin d, (1 / 4 : ℝ) * K * (1 - (2 * ((Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card : ℝ)) * s)
      ≤ 1 / 4 * K * (1 - s) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) := by
    intro b
    apply mul_le_mul_of_nonneg_left (hbern _) (by positivity)
  have h4 := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin d))) => h3 b)
  have h5 : ∑ b : Fin d, (1 / 4 : ℝ) * K * (1 - (2 * ((Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card : ℝ)) * s)
      = 1 / 4 * K * ((d : ℝ) - 2 * s * ∑ b : Fin d, ((Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card : ℝ)) := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [mul_comm, mul_assoc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    ring
  rw [sum_nb] at h5
  have hmR : ((Finset.univ.filter p).card : ℝ) ≤ m := by exact_mod_cast hp
  have h6 : 2 * s * (m : ℝ) ≤ d / 16 := by
    have hm' : (m : ℝ) * (32768 * ε ^ 2) ≤ ℓ * d := by
      rwa [le_div_iff₀ (by positivity)] at hm
    rw [hs]
    have : 2 * ((32 * ε) ^ 2 / ℓ) * m = 2048 * ε ^ 2 * m / ℓ := by field_simp; ring
    rw [this, div_le_iff₀ hℓR]
    nlinarith
  have h7 : 2 * s * ((Finset.univ.filter p).card : ℝ) ≤ d / 16 := by
    have := mul_le_mul_of_nonneg_left hmR (by positivity : (0 : ℝ) ≤ 2 * s)
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h8 : 1 / 4 * K * ((d : ℝ) - 2 * s * ((Finset.univ.filter p).card : ℝ)) ≥ 1 / 4 * K * (15 / 16 * d) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [← Finset.mul_sum]
  have h9 : 1 / 4 * K * (15 / 16 * (d : ℝ)) ≤
      ∑ b : Fin d, 1 / 4 * K * (1 - s) ^ (2 * (Finset.univ.filter (fun x : {x // p x} => x.1.1 = b)).card) := by
    linarith
  have h10 := mul_le_mul_of_nonneg_left h9 hℓR.le
  nlinarith [h10]

end Assouad


section Point2

variable {ℓ d M : ℕ}

theorem ham2_eq (p : Fin d × Fin M → Prop) [DecidablePred p]
    (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (Θ : Fin d → Fin ℓ → Bool) :
    Ham2 p L Θ = ∑ i : Fin d × Fin ℓ, if est2 p L i.1 i.2 ≠ Θ i.1 i.2 then (1 : ℝ) else 0 := by
  unfold Ham2
  rw [Finset.card_filter]
  push_cast
  rfl

theorem ham2_le (p : Fin d × Fin M → Prop) [DecidablePred p]
    (L : Fin d × Fin M → Finset (Fin ℓ × Bool)) (Θ : Fin d → Fin ℓ → Bool) :
    Ham2 p L Θ ≤ (d : ℝ) * ℓ := by
  unfold Ham2
  have : (Finset.univ.filter (fun i : Fin d × Fin ℓ => est2 p L i.1 i.2 ≠ Θ i.1 i.2)).card ≤ d * ℓ := by
    calc _ ≤ (Finset.univ : Finset (Fin d × Fin ℓ)).card := Finset.card_filter_le _ _
      _ = d * ℓ := by simp
  exact_mod_cast this

theorem point_main2 (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 64) (hd : 1 ≤ d) (m : ℕ)
    (hm : (m : ℝ) ≤ (ℓ : ℝ) * d / (32768 * ε ^ 2))
    (hM1 : 112 / ε ^ 2 ≤ M) (hM2 : 100 * m / ε ≤ M) (hM0 : 0 < M)
    (p : Fin d × Fin M → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).card ≤ m)
    (Pred : (Fin d × Fin M → Fin ℓ × Bool) → Fin d × Fin M → Finset (Fin ℓ × Bool))
    (hc : ∀ F x, (Pred F x).card ≤ ℓ)
    (hdep : ∀ F F' : Fin d × Fin M → Fin ℓ × Bool, (∀ x, p x → F x = F' x) → Pred F = Pred F') :
    81 / 640 * (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) ≤
      ∑ Θ : Fin d → Fin ℓ → Bool, ∑ F : Fin d × Fin M → Fin ℓ × Bool,
        (∏ x, pq (32 * ε) (Θ x.1) (F x)) *
          (if ε * ((d : ℝ) * M) < bestc2 Θ F - covc2 (Pred F) F then 1 else 0) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hγ0 : (0 : ℝ) ≤ 32 * ε := by positivity
  have hγ1 : 32 * ε ≤ 1 := by linarith
  have hℓ0 : 0 < ℓ := hℓ
  let y0 : Fin ℓ × Bool := (⟨0, hℓ0⟩, true)
  let V0 : {x // ¬ p x} → Fin ℓ × Bool := fun _ => y0
  let PT : ({x // p x} → Fin ℓ × Bool) → Fin d × Fin M → Finset (Fin ℓ × Bool) :=
    fun T => Pred (merge p T V0)
  have hmerge : ∀ T V, Pred (merge p T V) = PT T := by
    intro T V
    apply hdep
    intro x hx
    simp [merge, hx]
  set K : ℝ := (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) with hK
  have hsplit : ∀ Θ : Fin d → Fin ℓ → Bool, ∑ F : Fin d × Fin M → Fin ℓ × Bool,
      (∏ x, pq (32 * ε) (Θ x.1) (F x)) *
        (if ε * ((d : ℝ) * M) < bestc2 Θ F - covc2 (Pred F) F then 1 else 0) =
      ∑ T : {x // p x} → Fin ℓ × Bool, (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ x : {x // ¬ p x}, pq (32 * ε) (Θ x.1.1) (V x)) *
          (if ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 (PT T) (merge p T V) then 1 else 0) := by
    intro Θ
    rw [split_sum p (fun x y => pq (32 * ε) (Θ x.1) y)
      (fun F => (if ε * ((d : ℝ) * M) < bestc2 Θ F - covc2 (Pred F) F then 1 else 0))]
    refine Finset.sum_congr (by ext; simp) (fun T _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr (by ext; simp) (fun V _ => ?_)
    rw [hmerge T V, mul_assoc]
  have hq0 : ∀ (Θ : Fin d → Fin ℓ → Bool) (T : {x // p x} → Fin ℓ × Bool),
      0 ≤ ∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x) :=
    fun Θ T => Finset.prod_nonneg (fun x _ => pq_nonneg hℓ hγ0 hγ1 _ _)
  have hgood : ∀ (Θ : Fin d → Fin ℓ → Bool) (T : {x // p x} → Fin ℓ × Bool),
      (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then (9 : ℝ) / 10 else 0) ≤
      ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ x : {x // ¬ p x}, pq (32 * ε) (Θ x.1.1) (V x)) *
          (if ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 (PT T) (merge p T V) then 1 else 0) := by
    intro Θ T
    by_cases hH : 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ
    · rw [if_pos hH]
      exact good_case2 hℓ hε0 hε hd m hM1 hM2 hM0 p hp Θ (PT T) (fun x => hc _ x) hH T
    · rw [if_neg hH]
      apply Finset.sum_nonneg; intro V _
      apply mul_nonneg
      · exact Finset.prod_nonneg (fun x _ => pq_nonneg hℓ hγ0 hγ1 _ _)
      · split_ifs <;> norm_num
  have hA := claimA hℓ hε0 hε hd m hm p hp (fun b j T => est2 p (PT T) b j)
  have hw1 : ∀ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      ∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x) = 1 :=
    fun Θ => sum_prod_one (fun (x : {x // p x}) y => pq (32 * ε) (Θ x.1.1) y) (fun x => pq_sum hℓ _ _)
  -- reverse Markov
  have hRM : 9 / 64 * K ≤ ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then 1 else 0) := by
    set N : ℝ := (d : ℝ) * ℓ with hN
    have hN0 : 0 < N := by positivity
    have hpt : ∀ (Θ : Fin d → Fin ℓ → Bool) (T : {x // p x} → Fin ℓ × Bool),
        (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * Ham2 p (PT T) Θ ≤
        3 * N / 32 * (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) +
          N * ((∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
            (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then 1 else 0)) := by
      intro Θ T
      have h0 := hq0 Θ T
      have hle := ham2_le p (PT T) Θ
      by_cases hH : 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ
      · rw [if_pos hH]
        have : Ham2 p (PT T) Θ ≤ N := hle
        nlinarith [mul_le_mul_of_nonneg_left this h0]
      · rw [if_neg hH]
        push Not at hH
        have : Ham2 p (PT T) Θ ≤ 3 * N / 32 := by rw [hN]; linarith
        nlinarith [mul_le_mul_of_nonneg_left this h0]
    have hsumH : ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
        (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * Ham2 p (PT T) Θ ≤
        3 * N / 32 * K + N * ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
          (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
            (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then 1 else 0) := by
      calc _ ≤ ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
            (3 * N / 32 * (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) +
              N * ((∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
                (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then 1 else 0))) :=
            Finset.sum_le_sum (fun Θ _ => Finset.sum_le_sum (fun T _ => hpt Θ T))
        _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1]
            simp [hK]
    have hA' : 15 / 64 * K * N ≤ ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
        (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) * Ham2 p (PT T) Θ := by
      refine hA.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun Θ _ => Finset.sum_congr rfl (fun T _ => ?_))
      rw [ham2_eq]
    have hK0 : 0 ≤ K := Nat.cast_nonneg _
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hN0]
  calc 81 / 640 * K ≤ 9 / 10 * (9 / 64 * K) := by nlinarith
    _ ≤ 9 / 10 * ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then 1 else 0) := by gcongr
    _ = ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        (if 3 * (d : ℝ) * ℓ / 32 ≤ Ham2 p (PT T) Θ then (9 : ℝ) / 10 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Θ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ Θ : Fin d → Fin ℓ → Bool, ∑ T : {x // p x} → Fin ℓ × Bool,
      (∏ x : {x // p x}, pq (32 * ε) (Θ x.1.1) (T x)) *
        ∑ V : {x // ¬ p x} → Fin ℓ × Bool, (∏ x : {x // ¬ p x}, pq (32 * ε) (Θ x.1.1) (V x)) *
          (if ε * ((d : ℝ) * M) < bestc2 Θ (merge p T V) - covc2 (PT T) (merge p T V) then 1 else 0) := by
        apply Finset.sum_le_sum; intro Θ _
        apply Finset.sum_le_sum; intro T _
        exact mul_le_mul_of_nonneg_left (hgood Θ T) (hq0 Θ T)
    _ = _ := by
        refine Finset.sum_congr rfl (fun Θ _ => ?_)
        rw [hsplit Θ]

end Point2


noncomputable def unifI (I : Type) [Fintype I] [Nonempty I] [MeasurableSpace I]
    [MeasurableSingletonClass I] : ProbabilityMeasure I :=
  ⟨(PMF.uniformOfFintype I).toMeasure, inferInstance⟩

theorem unifI_filter (I : Type) [Fintype I] [Nonempty I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (P : I → Prop) [DecidablePred P] :
    (unifI I : Measure I) {a | P a} =
      ENNReal.ofReal (((Finset.univ.filter P).card : ℝ) / Fintype.card I) := by
  show (PMF.uniformOfFintype I).toMeasure _ = _
  rw [PMF.toMeasure_apply_fintype _ _]
  have h1 : ∀ x : I, {a | P a}.indicator (⇑(PMF.uniformOfFintype I)) x =
      if P x then ((Fintype.card I : ℝ≥0∞))⁻¹ else 0 := by
    intro x
    by_cases hx : P x <;> simp [Set.indicator, PMF.uniformOfFintype_apply, hx]
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hM : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hM, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]

section Assemble2

variable {ℓ d M : ℕ}

def y0b (hℓ : 1 ≤ ℓ) (Θ : Fin d → Fin ℓ → Bool) (b : Fin d) : Fin ℓ × Bool :=
  (⟨0, by omega⟩, Θ b ⟨0, by omega⟩)

def hΘF2 (hℓ : 1 ≤ ℓ) (Θ : Fin d → Fin ℓ → Bool) (F : Fin d × Fin M → Fin ℓ × Bool) :
    Fin d × ℕ → Fin ℓ × Bool := fun x =>
  if hn : x.2 < M then
    (if (F (x.1, ⟨x.2, hn⟩)).2 = Θ x.1 (F (x.1, ⟨x.2, hn⟩)).1 then F (x.1, ⟨x.2, hn⟩) else y0b hℓ Θ x.1)
  else y0b hℓ Θ x.1

theorem hΘF2_mem (hℓ : 1 ≤ ℓ) (Θ : Fin d → Fin ℓ → Bool) (F : Fin d × Fin M → Fin ℓ × Bool) :
    hΘF2 hℓ Θ F ∈ H2 d ℓ := by
  have key : ∀ x : Fin d × ℕ, (hΘF2 hℓ Θ F x).2 = Θ x.1 (hΘF2 hℓ Θ F x).1 := by
    intro x
    unfold hΘF2
    split_ifs with h1 h2
    · exact h2
    · rfl
    · rfl
  intro b t t' h
  rw [key (b, t), key (b, t'), h]

theorem event_of2 (hℓ : 1 ≤ ℓ) [NeZero M] [NeZero d] (Θ : Fin d → Fin ℓ → Bool)
    (F : Fin d × Fin M → Fin ℓ × Bool)
    (μ : ListPredictor (Fin d × ℕ) (Fin ℓ × Bool) ℓ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ε * ((d : ℝ) * M) < bestc2 Θ F - covc2 (fun a : Fin d × Fin M => (μ (a.1, a.2.val)).1) F) :
    (unifI (Fin d × Fin M) : Measure (Fin d × Fin M)) {a | hΘF2 hℓ Θ F (a.1, a.2.val) ≠ F a} +
        ENNReal.ofReal ε <
      listError (mkLaw (fun a : Fin d × Fin M => (a.1, a.2.val)) F (unifI (Fin d × Fin M))) μ := by
  classical
  have hM : (0 : ℝ) < (Fintype.card (Fin d × Fin M) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (Fin d × Fin M) : ℝ) = (d : ℝ) * M := by simp
  rw [listError_eq, unifI_filter, unifI_filter, ← ENNReal.ofReal_add (by positivity) hε]
  have e1 : (Finset.univ.filter (fun a : Fin d × Fin M => hΘF2 hℓ Θ F (a.1, a.2.val) ≠ F a)) =
      Finset.univ.filter (fun a : Fin d × Fin M => ¬ (F a).2 = Θ a.1 (F a).1) := by
    apply Finset.filter_congr
    intro a _
    unfold hΘF2
    simp only [a.2.2, dif_pos]
    have : (⟨a.2.val, a.2.2⟩ : Fin M) = a.2 := Fin.ext rfl
    simp only [this, Prod.mk.eta]
    by_cases hs : (F a).2 = Θ a.1 (F a).1
    · simp [hs]
    · simp only [hs, if_false, ne_eq, not_false_eq_true, iff_true]
      intro h2
      apply hs
      rw [← h2]
      simp [y0b]
  have c1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d × Fin M)))
    (fun a => (F a).2 = Θ a.1 (F a).1)
  have c2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d × Fin M)))
    (fun a => F a ∈ (μ (a.1, a.2.val)).1)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at c1 c2
  have r1 : ((Finset.univ.filter (fun a : Fin d × Fin M => hΘF2 hℓ Θ F (a.1, a.2.val) ≠ F a)).card : ℝ)
      = (d : ℝ) * M - bestc2 Θ F := by
    rw [e1]; unfold bestc2
    have : ((Finset.univ.filter (fun a : Fin d × Fin M => ¬ (F a).2 = Θ a.1 (F a).1)).card : ℝ) +
        ((Finset.univ.filter (fun a : Fin d × Fin M => (F a).2 = Θ a.1 (F a).1)).card : ℝ) = (d : ℝ) * M := by
      exact_mod_cast (by omega)
    linarith
  have r2 : ((Finset.univ.filter (fun a : Fin d × Fin M => F a ∉ (μ (a.1, a.2.val)).1)).card : ℝ)
      = (d : ℝ) * M - covc2 (fun a : Fin d × Fin M => (μ (a.1, a.2.val)).1) F := by
    unfold covc2
    have : ((Finset.univ.filter (fun a : Fin d × Fin M => ¬ F a ∈ (μ (a.1, a.2.val)).1)).card : ℝ) +
        ((Finset.univ.filter (fun a : Fin d × Fin M => F a ∈ (μ (a.1, a.2.val)).1)).card : ℝ) = (d : ℝ) * M := by
      exact_mod_cast (by omega)
    linarith
  rw [hcard] at hM ⊢
  have hlt : (((Finset.univ.filter (fun a : Fin d × Fin M => hΘF2 hℓ Θ F (a.1, a.2.val) ≠ F a)).card : ℝ) /
        ((d : ℝ) * M) + ε) <
      ((Finset.univ.filter (fun a : Fin d × Fin M => F a ∉ (μ (a.1, a.2.val)).1)).card : ℝ) / ((d : ℝ) * M) := by
    rw [r1, r2, ← sub_pos]
    have : ((d : ℝ) * M - covc2 (fun a : Fin d × Fin M => (μ (a.1, a.2.val)).1) F) / ((d : ℝ) * M) -
        (((d : ℝ) * M - bestc2 Θ F) / ((d : ℝ) * M) + ε) =
        ((bestc2 Θ F - covc2 (fun a : Fin d × Fin M => (μ (a.1, a.2.val)).1) F) - ε * ((d : ℝ) * M)) /
          ((d : ℝ) * M) := by
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      field_simp
      ring
    rw [this]
    apply div_pos (by linarith) hM
  have hq : 0 < ((Finset.univ.filter (fun a : Fin d × Fin M => F a ∉ (μ (a.1, a.2.val)).1)).card : ℝ) /
      ((d : ℝ) * M) := by
    refine lt_of_le_of_lt ?_ hlt
    positivity
  exact (ENNReal.ofReal_lt_ofReal_iff hq).mpr hlt

end Assemble2


theorem clause2_prob {ℓ d : ℕ} (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) {R : Type*} [MeasurableSpace R]
    (ρ : ProbabilityMeasure R) (A : ListLearner (Fin d × ℕ) (Fin ℓ × Bool) R ℓ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 64) (m : ℕ) (hm : (m : ℝ) ≤ (ℓ : ℝ) * d / (32768 * ε ^ 2)) :
    ∃ D : DataLaw ((Fin d × ℕ) × (Fin ℓ × Bool)), D.1 = ⊤ ∧
      ENNReal.ofReal (1 / 10 : ℝ) < failureProbability D ρ A ε (1 / 10) m (bestError D (H2 d ℓ)) := by
  classical
  set M : ℕ := ⌈112 / ε ^ 2⌉₊ + ⌈100 * (m : ℝ) / ε⌉₊ + 1 with hMdef
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero d := ⟨by omega⟩
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM1 : 112 / ε ^ 2 ≤ M := by
    have := Nat.le_ceil (112 / ε ^ 2)
    have h2' : ⌈112 / ε ^ 2⌉₊ ≤ M := by omega
    have h2 : ((⌈112 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast h2'
    linarith
  have hM2 : 100 * m / ε ≤ M := by
    have := Nat.le_ceil (100 * (m : ℝ) / ε)
    have h2' : ⌈100 * (m : ℝ) / ε⌉₊ ≤ M := by omega
    have h2 : ((⌈100 * (m : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast h2'
    linarith
  set ν : ProbabilityMeasure (Fin d × Fin M) := unifI (Fin d × Fin M) with hν
  set S : Fin d × Fin M → Fin d × ℕ := fun a => (a.1, a.2.val) with hS
  set P : Measure ((Fin m → Fin d × Fin M) × R) :=
    (Measure.pi (fun _ : Fin m => (ν : Measure (Fin d × Fin M)))).prod (ρ : Measure R) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set K : ℝ := (Fintype.card (Fin d → Fin ℓ → Bool) : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
  have hγ0 : (0 : ℝ) ≤ 32 * ε := by positivity
  have hγ1 : 32 * ε ≤ 1 := by linarith
  set w : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x)) with hw
  set E : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool) → Set ((Fin m → Fin d × Fin M) × R) :=
    fun f => {x | (ν : Measure (Fin d × Fin M)) {a | hΘF2 hℓ f.1 f.2 (S a) ≠ f.2 a} + ENNReal.ofReal ε <
      listError (mkLaw S f.2 ν) (A ε (1 / 10) m (fun j => pt S f.2 (x.1 j)) x.2)} with hE
  have hnn : ∀ f : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool),
      0 ≤ 1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x) :=
    fun f => mul_nonneg (by positivity) (Finset.prod_nonneg (fun x _ => pq_nonneg hℓ hγ0 hγ1 _ _))
  have hsum : ∑ f ∈ (Finset.univ : Finset ((Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool))), w f = 1 := by
    simp only [hw]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun f _ => hnn f), Fintype.sum_prod_type]
    have : ∀ Θ : Fin d → Fin ℓ → Bool, ∑ F : Fin d × Fin M → Fin ℓ × Bool,
        1 / K * ∏ x, pq (32 * ε) (Θ x.1) (F x) = 1 / K := by
      intro Θ
      have h1 : ∑ F : Fin d × Fin M → Fin ℓ × Bool, ∏ x, pq (32 * ε) (Θ x.1) (F x) = 1 :=
        sum_prod_one (fun (x : Fin d × Fin M) y => pq (32 * ε) (Θ x.1) y) (fun _ => pq_sum hℓ _ _)
      rw [← Finset.mul_sum, h1, mul_one]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hK, ENNReal.ofReal_eq_one]
    field_simp
  have hpoint : ∀ x : (Fin m → Fin d × Fin M) × R, ENNReal.ofReal (81 / 640) ≤
      ∑ f ∈ (Finset.univ : Finset ((Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool))),
        w f * (E f).indicator 1 x := by
    intro x
    let O : Finset (Fin d × Fin M) := Finset.univ.image x.1
    let Pred : (Fin d × Fin M → Fin ℓ × Bool) → Fin d × Fin M → Finset (Fin ℓ × Bool) := fun F a =>
      ((A ε (1 / 10) m (fun j => pt S F (x.1 j)) x.2) (S a)).1
    have hO : (Finset.univ.filter (fun a => a ∈ O)).card ≤ m := by
      have : Finset.univ.filter (fun a => a ∈ O) = O := by ext a; simp
      rw [this]
      exact (Finset.card_image_le).trans (by simp)
    have hc : ∀ F a, (Pred F a).card ≤ ℓ := fun F a => ((A ε (1 / 10) m (fun j => pt S F (x.1 j)) x.2) (S a)).2
    have hdep : ∀ F F' : Fin d × Fin M → Fin ℓ × Bool, (∀ a, a ∈ O → F a = F' a) → Pred F = Pred F' := by
      intro F F' h
      have : (fun j => pt S F (x.1 j)) = (fun j => pt S F' (x.1 j)) := by
        funext j
        simp only [pt]
        rw [h (x.1 j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))]
      simp only [Pred]
      rw [this]
    have hmain := point_main2 hℓ hε0 hε1 hd m hm hM1 hM2 hM0 (fun a => a ∈ O) hO Pred hc hdep
    have hrew : 81 / 640 ≤ ∑ f : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool),
        (1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x)) *
          (if ε * ((d : ℝ) * M) < bestc2 f.1 f.2 - covc2 (Pred f.2) f.2 then 1 else 0) := by
      have e : ∑ f : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool),
          (1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x)) *
          (if ε * ((d : ℝ) * M) < bestc2 f.1 f.2 - covc2 (Pred f.2) f.2 then 1 else 0) =
          1 / K * ∑ Θ : Fin d → Fin ℓ → Bool, ∑ F : Fin d × Fin M → Fin ℓ × Bool,
            (∏ x, pq (32 * ε) (Θ x.1) (F x)) *
              (if ε * ((d : ℝ) * M) < bestc2 Θ F - covc2 (Pred F) F then 1 else 0) := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Θ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun F _ => ?_)
        ring
      rw [e, one_div, ← div_eq_inv_mul, le_div_iff₀ hKpos]
      linarith
    calc ENNReal.ofReal (81 / 640)
        ≤ ENNReal.ofReal (∑ f : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool),
          (1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x)) *
          (if ε * ((d : ℝ) * M) < bestc2 f.1 f.2 - covc2 (Pred f.2) f.2 then 1 else 0)) :=
          ENNReal.ofReal_le_ofReal hrew
      _ = ∑ f : (Fin d → Fin ℓ → Bool) × (Fin d × Fin M → Fin ℓ × Bool), ENNReal.ofReal
          ((1 / K * ∏ x, pq (32 * ε) (f.1 x.1) (f.2 x)) *
          (if ε * ((d : ℝ) * M) < bestc2 f.1 f.2 - covc2 (Pred f.2) f.2 then 1 else 0)) :=
          ENNReal.ofReal_sum_of_nonneg (fun f _ => mul_nonneg (hnn f) (by split_ifs <;> norm_num))
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro f _
          by_cases hcond : ε * ((d : ℝ) * M) < bestc2 f.1 f.2 - covc2 (Pred f.2) f.2
          · have hx : x ∈ E f := event_of2 hℓ f.1 f.2 (A ε (1 / 10) m (fun j => pt S f.2 (x.1 j)) x.2) ε hε0.le hcond
            rw [Set.indicator_of_mem hx]
            simp only [hcond, if_true, mul_one, Pi.one_apply]
            exact le_rfl
          · simp [hcond]
  obtain ⟨f, -, hf⟩ := avg_exists_w P Finset.univ w (fun f => ENNReal.ofReal_ne_top) E _ hsum hpoint
  refine ⟨mkLaw S f.2 ν, rfl, ?_⟩
  calc ENNReal.ofReal (1 / 10 : ℝ) < ENNReal.ofReal (81 / 640) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    _ ≤ P (E f) := hf
    _ ≤ P {x | bestError (mkLaw S f.2 ν) (H2 d ℓ) + ENNReal.ofReal ε <
          listError (mkLaw S f.2 ν) (A ε (1 / 10) m (fun j => pt S f.2 (x.1 j)) x.2)} := by
        apply measure_mono
        intro x hx
        have hb := bestError_le S f.2 ν (H2 d ℓ) (hΘF2 hℓ f.1 f.2) (hΘF2_mem hℓ f.1 f.2)
        exact lt_of_le_of_lt (add_le_add_left hb _) hx
    _ ≤ _ := failure_ge S f.2 ν ρ A ε (1 / 10) m _

end DSDensity1246.Dev.LBAgn

open DSDensity1246.Main DSDensity1246.Main.Supplement

namespace DSDensity1246.Main.Supplement

theorem chk_agnostic_list_lower_bound :
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∃ H : Set (ℕ → Fin (2 * ℓ)),
      listNatDim ℓ H = 1 ∧ listDSDim ℓ H = 1 ∧
      ∀ (R : Type*) [MeasurableSpace R] (ρ : ProbabilityMeasure R)
        (A : ListLearner ℕ (Fin (2 * ℓ)) R ℓ),
        ∀ ε δ : ℝ, 0 < ε → ε < 1 / 8 → 0 < δ → δ < 1 / 8 →
          ∀ m : ℕ, (m : ℝ) ≤ Real.log (1 / (8 * δ)) / (64 * ε ^ 2) →
            ∃ D : DataLaw (ℕ × Fin (2 * ℓ)), D.1 = ⊤ ∧
              ENNReal.ofReal δ < failureProbability D ρ A ε δ m (bestError D H)) ∧
    (∀ ℓ d : ℕ, 1 ≤ ℓ → 1 ≤ d →
      ∃ H : Set ((Fin d × ℕ) → (Fin ℓ × Bool)), listNatDim ℓ H = d ∧
      ∀ (R : Type*) [MeasurableSpace R] (ρ : ProbabilityMeasure R)
        (A : ListLearner (Fin d × ℕ) (Fin ℓ × Bool) R ℓ),
        ∀ ε : ℝ, 0 < ε → ε < 1 / 64 →
          ∀ m : ℕ, (m : ℝ) ≤ (ℓ : ℝ) * d / (32768 * ε ^ 2) →
            ∃ D : DataLaw ((Fin d × ℕ) × (Fin ℓ × Bool)), D.1 = ⊤ ∧
              ENNReal.ofReal (1 / 10 : ℝ) <
                failureProbability D ρ A ε (1 / 10) m (bestError D H)) := by
  refine ⟨?_, ?_⟩
  · intro ℓ hℓ
    refine ⟨DSDensity1246.Dev.LBAgn.H1 ℓ, DSDensity1246.Dev.LBAgn.natDim_H1 hℓ,
      DSDensity1246.Dev.LBAgn.dsDim_H1 hℓ, ?_⟩
    intro R _ ρ A ε δ hε0 hε1 hδ0 _ m hm
    exact DSDensity1246.Dev.LBAgn.clause1_prob hℓ ρ A ε δ hε0 hε1 hδ0 m hm
  · intro ℓ d hℓ hd
    refine ⟨DSDensity1246.Dev.LBAgn.H2 d ℓ, DSDensity1246.Dev.LBAgn.natDim_H2 hℓ, ?_⟩
    intro R _ ρ A ε hε0 hε1 m hm
    exact DSDensity1246.Dev.LBAgn.clause2_prob hℓ hd ρ A ε hε0 hε1 m hm

end DSDensity1246.Main.Supplement
end

theorem solution : type_of% @DSDensity1246.Main.Supplement.chk_agnostic_list_lower_bound := @DSDensity1246.Main.Supplement.chk_agnostic_list_lower_bound
