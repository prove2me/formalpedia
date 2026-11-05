-- Prove2me | solution 1 for BanKeskin.KnownSparsity.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:34:04.099861+00:00
-- url     : https://prove2.me/submissions/557f5e42-2a7e-435b-924a-98b7eb7b0f04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model
import Theorems.Thm_BanKeskin_KnownSparsity_lemma_1
import Theorems.Thm_BanKeskin_KnownSparsity_eq_15

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))}

noncomputable def aco (θ : Parameter d S) (x : ↥S → ℝ) : ℝ := ∑ i, θ (0, i) * x i
noncomputable def bco (θ : Parameter d S) (x : ↥S → ℝ) : ℝ := ∑ i, θ (1, i) * x i

lemma dot_regressor (θ : Parameter d S) (p : ℝ) (x : ↥S → ℝ) :
    dot θ (regressor p x) = aco θ x + p * bco θ x := by
  simp only [dot, regressor, aco, bco, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_mul, one_ne_zero, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

lemma phi_eq (θ : Parameter d S) (x : ↥S → ℝ) : phi θ x = -(aco θ x) / (2 * bco θ x) := rfl

lemma aco_eq (θ : Parameter d S) (x : ↥S → ℝ) (hb : bco θ x < 0) :
    aco θ x = -2 * bco θ x * phi θ x := by
  rw [phi_eq]; field_simp; rw [mul_div_assoc, div_self hb.ne, mul_one]

lemma revenue_gap (θ : Parameter d S) (p : ℝ) (x : ↥S → ℝ) (hb : bco θ x < 0) :
    phi θ x * dot θ (regressor (phi θ x) x) - p * dot θ (regressor p x)
      = -bco θ x * (p - phi θ x) ^ 2 := by
  rw [dot_regressor, dot_regressor, aco_eq θ x hb]; ring

lemma aco_update0 (θ : Parameter d S) (x : ↥S → ℝ) (i0 : ↥S) (v : ℝ) :
    aco (Function.update θ (0, i0) v) x = aco θ x + (v - θ (0, i0)) * x i0 := by
  unfold aco
  have : ∀ i, Function.update θ (0, i0) v (0, i) * x i
      = θ (0, i) * x i + if i0 = i then (v - θ (0, i0)) * x i0 else 0 := by
    intro i
    by_cases h : i = i0
    · subst h; simp; ring
    · have : ((0 : Fin 2), i) ≠ (0, i0) := by simp [h]
      simp [Function.update_of_ne this, Ne.symm h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma bco_update0 (θ : Parameter d S) (x : ↥S → ℝ) (i0 : ↥S) (v : ℝ) :
    bco (Function.update θ (0, i0) v) x = bco θ x := by
  unfold bco
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((1 : Fin 2), i) ≠ (0, i0) := by simp
  rw [Function.update_of_ne this]

lemma bco_update1 (θ : Parameter d S) (x : ↥S → ℝ) (i0 : ↥S) (v : ℝ) :
    bco (Function.update θ (1, i0) v) x = bco θ x + (v - θ (1, i0)) * x i0 := by
  unfold bco
  have : ∀ i, Function.update θ (1, i0) v (1, i) * x i
      = θ (1, i) * x i + if i0 = i then (v - θ (1, i0)) * x i0 else 0 := by
    intro i
    by_cases h : i = i0
    · subst h; simp; ring
    · have : ((1 : Fin 2), i) ≠ (1, i0) := by simp [h]
      simp [Function.update_of_ne this, Ne.symm h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma aco_update1 (θ : Parameter d S) (x : ↥S → ℝ) (i0 : ↥S) (v : ℝ) :
    aco (Function.update θ (1, i0) v) x = aco θ x := by
  unfold aco
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((0 : Fin 2), i) ≠ (1, i0) := by simp
  rw [Function.update_of_ne this]

lemma update_mem {lo hi θ : Parameter d S} (h : θ ∈ Set.Icc lo hi) (j : Fin 2 × ↥S) (v : ℝ)
    (hv : v ∈ Set.Icc (lo j) (hi j)) : Function.update θ j v ∈ Set.Icc lo hi := by
  constructor
  · intro k
    by_cases hk : k = j
    · subst hk; simp [hv.1]
    · rw [Function.update_of_ne hk]; exact h.1 k
  · intro k
    by_cases hk : k = j
    · subst hk; simp [hv.2]
    · rw [Function.update_of_ne hk]; exact h.2 k

/-- Hypotheses on the cone: for every box point, negative slope and interior optimum. -/
structure Cone (lo hi : Parameter d S) (L U : ℝ) (x : ↥S → ℝ) : Prop where
  neg : ∀ θ ∈ Set.Icc lo hi, bco θ x < 0
  int : ∀ θ ∈ Set.Icc lo hi, phi θ x ∈ Set.Ioo L U

noncomputable def Dw (lo hi : Parameter d S) (j : Fin 2 × ↥S) : ℝ :=
  if lo j < hi j then 1 / (hi j - lo j) else 0

lemma width_bound0 {lo hi : Parameter d S} {L U : ℝ} {x : ↥S → ℝ} (hL : 0 < L)
    (hC : Cone lo hi L U x) {θ : Parameter d S} (hθ : θ ∈ Set.Icc lo hi)
    (i : ↥S) (hj : lo (0, i) < hi (0, i)) :
    |x i| * (hi (0, i) - lo (0, i)) ≤ (2 * (U - L) + U / L) * -bco θ x := by
  have hb := hC.neg θ hθ
  have hφθ := hC.int θ hθ
  have hLU : L < U := hφθ.1.trans hφθ.2
  set θm := Function.update θ (0, i) (lo (0, i))
  set θp := Function.update θ (0, i) (hi (0, i))
  have hm : θm ∈ Set.Icc lo hi := update_mem hθ _ _ ⟨le_rfl, hj.le⟩
  have hp : θp ∈ Set.Icc lo hi := update_mem hθ _ _ ⟨hj.le, le_rfl⟩
  have bm : bco θm x = bco θ x := bco_update0 _ _ _ _
  have bp : bco θp x = bco θ x := bco_update0 _ _ _ _
  have am := aco_eq θm x (hC.neg θm hm)
  have ap := aco_eq θp x (hC.neg θp hp)
  rw [aco_update0, bm] at am
  rw [aco_update0, bp] at ap
  have h1 := hC.int θm hm
  have h2 := hC.int θp hp
  have hdiff : (hi (0, i) - lo (0, i)) * x i = -2 * bco θ x * (phi θp x - phi θm x) := by
    linear_combination ap - am
  have hpos : 0 < hi (0, i) - lo (0, i) := by linarith
  have e : |x i| * (hi (0, i) - lo (0, i)) = (-2 * bco θ x) * |phi θp x - phi θm x| := by
    rw [mul_comm, ← abs_of_pos hpos, ← abs_mul, hdiff, abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < -2 * bco θ x)]
  rw [e]
  have : |phi θp x - phi θm x| ≤ U - L := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hUL : 0 ≤ U / L := div_nonneg (by linarith) hL.le
  nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ -2 * bco θ x)]

lemma width_bound1 {lo hi : Parameter d S} {L U : ℝ} {x : ↥S → ℝ} (hL : 0 < L)
    (hC : Cone lo hi L U x) {θ : Parameter d S} (hθ : θ ∈ Set.Icc lo hi)
    (i : ↥S) (hj : lo (1, i) < hi (1, i)) :
    |x i| * (hi (1, i) - lo (1, i)) ≤ (2 * (U - L) + U / L) * -bco θ x := by
  have hb := hC.neg θ hθ
  have hφθ := hC.int θ hθ
  have hLU : L < U := hφθ.1.trans hφθ.2
  set θm := Function.update θ (1, i) (lo (1, i))
  set θp := Function.update θ (1, i) (hi (1, i))
  have hm : θm ∈ Set.Icc lo hi := update_mem hθ _ _ ⟨le_rfl, hj.le⟩
  have hp : θp ∈ Set.Icc lo hi := update_mem hθ _ _ ⟨hj.le, le_rfl⟩
  have am : aco θm x = aco θ x := aco_update1 _ _ _ _
  have ap : aco θp x = aco θ x := aco_update1 _ _ _ _
  have bm := bco_update1 θ x i (lo (1, i))
  have bp := bco_update1 θ x i (hi (1, i))
  have em := aco_eq θm x (hC.neg θm hm)
  have ep := aco_eq θp x (hC.neg θp hp)
  have e0 := aco_eq θ x hb
  rw [am] at em; rw [ap] at ep
  have h1 := hC.int θm hm
  have h2 := hC.int θp hp
  have nbm := hC.neg θm hm
  have nbp := hC.neg θp hp
  have hpos : 0 < hi (1, i) - lo (1, i) := by linarith
  have ha_lt : aco θ x < 2 * U * -bco θ x := by rw [e0]; nlinarith [hφθ.2]
  have hm' : -bco θm x * (2 * L) < aco θ x := by rw [em]; nlinarith [h1.1]
  have hp' : -bco θp x * (2 * L) < aco θ x := by rw [ep]; nlinarith [h2.1]
  have hdiff : (hi (1, i) - lo (1, i)) * x i = bco θp x - bco θm x := by
    rw [bp, bm]; ring
  have e : |x i| * (hi (1, i) - lo (1, i)) = |bco θp x - bco θm x| := by
    rw [mul_comm, ← abs_of_pos hpos, ← abs_mul, hdiff]
  rw [e]
  have h1' : |bco θp x - bco θm x| * (2 * L) < aco θ x := by
    rcases abs_cases (bco θp x - bco θm x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  have h2' : |bco θp x - bco θm x| * L ≤ U * -bco θ x := by nlinarith
  have h3 : |bco θp x - bco θm x| ≤ U / L * -bco θ x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]; linarith
  nlinarith

lemma term_bound {lo hi : Parameter d S} {θ θ' : Parameter d S}
    (hθ : θ ∈ Set.Icc lo hi) (hθ' : θ' ∈ Set.Icc lo hi) (j : Fin 2 × ↥S) (xi c : ℝ)
    (hw : lo j < hi j → |xi| * (hi j - lo j) ≤ c) (hc : 0 ≤ c) :
    |(θ' j - θ j) * xi| ≤ c * (Dw lo hi j * |θ' j - θ j|) := by
  unfold Dw
  split_ifs with h
  · have hpos : 0 < hi j - lo j := by linarith
    have hx : |xi| ≤ c / (hi j - lo j) := by rw [le_div_iff₀ hpos]; exact hw h
    rw [abs_mul]
    calc |θ' j - θ j| * |xi| ≤ |θ' j - θ j| * (c / (hi j - lo j)) :=
          mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = _ := by field_simp
  · have : θ' j = θ j := by
      have := hθ.1 j; have := hθ.2 j; have := hθ'.1 j; have := hθ'.2 j
      push_neg at h; linarith
    simp [this]

lemma phi_gap {lo hi : Parameter d S} {L U : ℝ} {x : ↥S → ℝ} (hL : 0 < L)
    (hC : Cone lo hi L U x) {θ θ' : Parameter d S} (hθ : θ ∈ Set.Icc lo hi)
    (hθ' : θ' ∈ Set.Icc lo hi) :
    -bco θ x * (phi θ' x - phi θ x) ^ 2 ≤
      -bco θ x * (((2 * (U - L) + U / L) * (1 + 2 * U) / 2) ^ 2 *
        ((∑ j, Dw lo hi j ^ 2) * sqNorm (θ' - θ))) := by
  have hb := hC.neg θ hθ
  have hb' := hC.neg θ' hθ'
  have hφ := hC.int θ hθ
  have hφ' := hC.int θ' hθ'
  have hLU : L < U := hφ.1.trans hφ.2
  set C1 := 2 * (U - L) + U / L with hC1
  have hC1 : 0 ≤ C1 := by have := div_nonneg (by linarith : (0:ℝ) ≤ U) hL.le; linarith
  set Δ := θ' - θ with hΔ
  set Q := ∑ j, Dw lo hi j * |Δ j| with hQ
  have hDw : ∀ j, 0 ≤ Dw lo hi j := fun j => by
    unfold Dw; split_ifs with h
    · exact div_nonneg zero_le_one (by linarith)
    · exact le_rfl
  have hQsplit : Q = (∑ i, Dw lo hi (0, i) * |Δ (0, i)|) + ∑ i, Dw lo hi (1, i) * |Δ (1, i)| := by
    rw [hQ, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hQ0 : 0 ≤ ∑ i, Dw lo hi (0, i) * |Δ (0, i)| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hDw _) (abs_nonneg _)
  have hQ1 : 0 ≤ ∑ i, Dw lo hi (1, i) * |Δ (1, i)| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hDw _) (abs_nonneg _)
  have hcb : 0 ≤ C1 * -bco θ x := mul_nonneg hC1 (by linarith)
  -- Δa
  have hΔa : |aco θ' x - aco θ x| ≤ C1 * -bco θ x * Q := by
    have e : aco θ' x - aco θ x = ∑ i, (θ' (0, i) - θ (0, i)) * x i := by
      unfold aco; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc |∑ i, (θ' (0, i) - θ (0, i)) * x i| ≤ ∑ i, |(θ' (0, i) - θ (0, i)) * x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C1 * -bco θ x * (Dw lo hi (0, i) * |θ' (0, i) - θ (0, i)|) :=
          Finset.sum_le_sum fun i _ => term_bound hθ hθ' (0, i) (x i) _
            (fun h => width_bound0 hL hC hθ i h) hcb
      _ = C1 * -bco θ x * ∑ i, Dw lo hi (0, i) * |Δ (0, i)| := by
          rw [Finset.mul_sum]; rfl
      _ ≤ C1 * -bco θ x * Q := mul_le_mul_of_nonneg_left (by linarith) hcb
  have hΔb : |bco θ' x - bco θ x| ≤ C1 * -bco θ x * Q := by
    have e : bco θ' x - bco θ x = ∑ i, (θ' (1, i) - θ (1, i)) * x i := by
      unfold bco; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc |∑ i, (θ' (1, i) - θ (1, i)) * x i| ≤ ∑ i, |(θ' (1, i) - θ (1, i)) * x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C1 * -bco θ x * (Dw lo hi (1, i) * |θ' (1, i) - θ (1, i)|) :=
          Finset.sum_le_sum fun i _ => term_bound hθ hθ' (1, i) (x i) _
            (fun h => width_bound1 hL hC hθ i h) hcb
      _ = C1 * -bco θ x * ∑ i, Dw lo hi (1, i) * |Δ (1, i)| := by
          rw [Finset.mul_sum]; rfl
      _ ≤ C1 * -bco θ x * Q := mul_le_mul_of_nonneg_left (by linarith) hcb
  have hQnn : 0 ≤ Q := by rw [hQsplit]; linarith
  have ea := aco_eq θ x hb
  have ea' := aco_eq θ' x hb'
  have key : -2 * bco θ x * (phi θ' x - phi θ x) =
      (aco θ' x - aco θ x) + 2 * (bco θ' x - bco θ x) * phi θ' x := by
    rw [ea, ea']; ring
  have habs : (-2 * bco θ x) * |phi θ' x - phi θ x| ≤ C1 * -bco θ x * Q * (1 + 2 * U) := by
    have h0 : (-2 * bco θ x) * |phi θ' x - phi θ x| = |(aco θ' x - aco θ x) + 2 * (bco θ' x - bco θ x) * phi θ' x| := by
      rw [← key, abs_mul, abs_of_pos (by linarith : (0:ℝ) < -2 * bco θ x)]
    rw [h0]
    have hp' : |phi θ' x| ≤ U := by rw [abs_le]; constructor <;> linarith [hφ'.1, hφ'.2]
    calc _ ≤ |aco θ' x - aco θ x| + |2 * (bco θ' x - bco θ x) * phi θ' x| := abs_add_le _ _
      _ = |aco θ' x - aco θ x| + 2 * |bco θ' x - bco θ x| * |phi θ' x| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ C1 * -bco θ x * Q + 2 * (C1 * -bco θ x * Q) * U := by
          gcongr
      _ = _ := by ring
  have hgap : |phi θ' x - phi θ x| ≤ C1 * (1 + 2 * U) / 2 * Q := by
    have hnb : 0 < -bco θ x := by linarith
    have : (-bco θ x) * (2 * |phi θ' x - phi θ x|) ≤ (-bco θ x) * (C1 * Q * (1 + 2 * U)) := by
      nlinarith
    have := le_of_mul_le_mul_left this hnb
    linarith
  have hQ2 : Q ^ 2 ≤ (∑ j, Dw lo hi j ^ 2) * sqNorm Δ := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Dw lo hi j) (fun j => |Δ j|)
    simp only [sq_abs] at this
    unfold sqNorm dot
    calc Q ^ 2 ≤ _ := this
      _ = _ := by congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  have hsq : (phi θ' x - phi θ x) ^ 2 ≤ (C1 * (1 + 2 * U) / 2) ^ 2 * Q ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hgap 2
  have hnb : 0 ≤ -bco θ x := by linarith
  apply mul_le_mul_of_nonneg_left _ hnb
  calc _ ≤ (C1 * (1 + 2 * U) / 2) ^ 2 * Q ^ 2 := hsq
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ2 (sq_nonneg _)

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma xS_bound (M : Model d S Ω P) {t : ℕ} (ht : 1 ≤ t) (ω : Ω) (i : ↥S) :
    |restrictX S (M.X t ω) i| ≤ 1 + M.zmax := by
  unfold restrictX Model.X
  have hz := M.zmax_pos
  rcases Fin.eq_zero_or_eq_succ i.1 with h | ⟨j, h⟩
  · rw [h]; simp; linarith
  · rw [h, Fin.cons_succ]
    have hb := M.bounded_Z t ω ht
    have : |M.Z t ω j| ≤ Real.sqrt (sqNorm (M.Z t ω)) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      unfold sqNorm dot
      have := Finset.single_le_sum (f := fun k => M.Z t ω k * M.Z t ω k)
        (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
      simpa [sq] using this
    linarith

lemma cone_of (M : Model d S Ω P) (I : InteriorConditions M) {t : ℕ} (ht : 1 ≤ t) (ω : Ω) :
    Cone M.lo M.hi M.lower M.upper (restrictX S (M.X t ω)) where
  neg θ hθ := I.negative_slope θ hθ t ω ht
  int θ hθ := I.optimum_interior θ hθ t ω ht

noncomputable def Bb (M : Model d S Ω P) : ℝ := (1 + M.zmax) * ∑ j, (|M.lo j| + |M.hi j|)

lemma neg_bco_le (M : Model d S Ω P) {t : ℕ} (ht : 1 ≤ t) (ω : Ω) {θ : Parameter d S}
    (hθ : θ ∈ M.Theta) : -bco θ (restrictX S (M.X t ω)) ≤ Bb M := by
  unfold bco Bb
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  calc ∑ i, -(θ (1, i) * restrictX S (M.X t ω) i)
      ≤ ∑ i, (1 + M.zmax) * (|M.lo (1, i)| + |M.hi (1, i)|) := by
        apply Finset.sum_le_sum; intro i _
        have h1 := xS_bound M ht ω i
        have h2 : |θ (1, i)| ≤ |M.lo (1, i)| + |M.hi (1, i)| := by
          have := hθ.1 (1, i); have := hθ.2 (1, i)
          rw [abs_le]; constructor <;>
            linarith [neg_abs_le (M.lo (1, i)), le_abs_self (M.hi (1, i)), abs_nonneg (M.lo (1, i)),
              abs_nonneg (M.hi (1, i)), le_abs_self (M.lo (1, i)), neg_abs_le (M.hi (1, i))]
        calc -(θ (1, i) * restrictX S (M.X t ω) i) ≤ |θ (1, i) * restrictX S (M.X t ω) i| :=
              neg_le_abs _
          _ = |θ (1, i)| * |restrictX S (M.X t ω) i| := abs_mul _ _
          _ ≤ (|M.lo (1, i)| + |M.hi (1, i)|) * (1 + M.zmax) :=
              mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
          _ = _ := by ring
    _ ≤ ∑ j, (1 + M.zmax) * (|M.lo j| + |M.hi j|) := by
        rw [Fintype.sum_prod_type, Fin.sum_univ_two]
        have : 0 ≤ ∑ i, (1 + M.zmax) * (|M.lo (0, i)| + |M.hi (0, i)|) :=
          Finset.sum_nonneg fun i _ => by have := M.zmax_pos; positivity
        linarith

lemma Bb_nonneg (M : Model d S Ω P) : 0 ≤ Bb M := by
  unfold Bb; have := M.zmax_pos
  exact mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => by positivity)

noncomputable def Kc (M : Model d S Ω P) : ℝ :=
  Bb M * ((((2 * (M.upper - M.lower) + M.upper / M.lower) * (1 + 2 * M.upper) / 2) ^ 2 *
    (∑ j, Dw M.lo M.hi j ^ 2)))

noncomputable def Cmax (M : Model d S Ω P) : ℝ := Bb M * (M.upper - M.lower) ^ 2

lemma gap_eq (M : Model d S Ω P) (I : InteriorConditions M) {t : ℕ} (ht : 1 ≤ t) (ω : Ω)
    {θ : Parameter d S} (hθ : θ ∈ M.Theta) (p : ℝ) :
    M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) - M.revenue θ p (M.X t ω) =
      -bco θ (restrictX S (M.X t ω)) * (p - phi θ (restrictX S (M.X t ω))) ^ 2 :=
  revenue_gap θ p _ (I.negative_slope θ hθ t ω ht)

lemma gap_le_Cmax (M : Model d S Ω P) (I : InteriorConditions M) {t : ℕ} (ht : 1 ≤ t) (ω : Ω)
    {θ : Parameter d S} (hθ : θ ∈ M.Theta) {p : ℝ} (hp : p ∈ Set.Icc M.lower M.upper) :
    M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) - M.revenue θ p (M.X t ω) ≤ Cmax M := by
  rw [gap_eq M I ht ω hθ]
  have hφ := I.optimum_interior θ hθ t ω ht
  have hb := I.negative_slope θ hθ t ω ht
  have h1 : (p - phi θ (restrictX S (M.X t ω))) ^ 2 ≤ (M.upper - M.lower) ^ 2 := by
    apply sq_le_sq'
    · linarith [hp.1, hp.2, hφ.1, hφ.2]
    · linarith [hp.1, hp.2, hφ.1, hφ.2]
  have h2 := neg_bco_le M ht ω hθ
  unfold Cmax
  have : 0 ≤ -bco θ (restrictX S (M.X t ω)) := by unfold bco; linarith
  calc _ ≤ -bco θ (restrictX S (M.X t ω)) * (M.upper - M.lower) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 this
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

lemma gap_le_K (M : Model d S Ω P) (I : InteriorConditions M) {t : ℕ} (ht : 1 ≤ t) (ω : Ω)
    {θ θ' : Parameter d S} (hθ : θ ∈ M.Theta) (hθ' : θ' ∈ M.Theta) :
    M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) -
      M.revenue θ (phi θ' (restrictX S (M.X t ω))) (M.X t ω) ≤ Kc M * sqNorm (θ' - θ) := by
  rw [gap_eq M I ht ω hθ]
  have h := phi_gap M.lower_pos (cone_of M I ht ω) hθ hθ'
  have h2 := neg_bco_le M ht ω hθ
  have hnn : 0 ≤ ((2 * (M.upper - M.lower) + M.upper / M.lower) * (1 + 2 * M.upper) / 2) ^ 2 *
      ((∑ j, Dw M.lo M.hi j ^ 2) * sqNorm (θ' - θ)) := by
    apply mul_nonneg (sq_nonneg _)
    apply mul_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
    unfold sqNorm dot; exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  calc _ ≤ _ := h
    _ ≤ Bb M * (((2 * (M.upper - M.lower) + M.upper / M.lower) * (1 + 2 * M.upper) / 2) ^ 2 *
      ((∑ j, Dw M.lo M.hi j ^ 2) * sqNorm (θ' - θ))) := mul_le_mul_of_nonneg_right h2 hnn
    _ = _ := by unfold Kc; ring

lemma clamp_mem (M : Model d S Ω P) (v : Parameter d S) : clamp M.lo M.hi v ∈ M.Theta := by
  constructor
  · intro j; exact le_max_left _ _
  · intro j; exact max_le (M.box_nonempty j) (min_le_right _ _)

lemma clamp_sq (M : Model d S Ω P) (v : Parameter d S) {θ : Parameter d S} (hθ : θ ∈ M.Theta) :
    sqNorm (clamp M.lo M.hi v - θ) ≤ sqNorm (v - θ) := by
  unfold sqNorm dot
  apply Finset.sum_le_sum; intro j _
  have h1 := hθ.1 j; have h2 := hθ.2 j
  simp only [Pi.sub_apply, clamp]
  rcases le_total (v j) (M.hi j) with h | h
  · rw [min_eq_left h]
    rcases le_total (M.lo j) (v j) with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h']; nlinarith
  · rw [min_eq_right h, max_eq_right (M.box_nonempty j)]; nlinarith

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma sum_fin_shift (n : ℕ) (f : ℕ → ℝ) :
    ∑ k : Fin n, f (k.1 + 1) = ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, Finset.sum_Icc_succ_top (by omega)]

noncomputable def rr (M : Model d S Ω P) (k : ℕ) (ω : Ω) : Parameter d S :=
  regressor (M.experimentPrice k) (restrictX S (M.X k ω))

lemma dot_add_left {ι : Type*} [Fintype ι] (u v w : ι → ℝ) : dot (u + v) w = dot u w + dot v w := by
  unfold dot; simp [add_mul, Finset.sum_add_distrib]

lemma dot_comm' {ι : Type*} [Fintype ι] (u v : ι → ℝ) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma rayleigh_eq (M : Model d S Ω P) (t : ℕ) (ω : Ω) (v : Parameter d S) :
    dot v (Matrix.mulVec (M.Jtilde t ω) v) = ∑ k ∈ Finset.Icc 1 t, chi k * (dot v (rr M k ω)) ^ 2 := by
  unfold Model.Jtilde rr
  rw [Matrix.sum_mulVec]
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum, op_smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

lemma mvec_dot (M : Model d S Ω P) (t : ℕ) (ω : Ω) (v : Parameter d S) :
    dot v (M.Mvec t ω) = ∑ k ∈ Finset.Icc 1 t, chi k * M.eps k ω * dot v (rr M k ω) := by
  unfold Model.Mvec rr dot
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

lemma chi_cases (k : ℕ) : (inM1 k ∨ inM2 k) ∧ chi k = 1 ∨ ¬(inM1 k ∨ inM2 k) ∧ chi k = 0 := by
  unfold chi
  by_cases h : inM1 k ∨ inM2 k
  · left; exact ⟨h, by simp [h]⟩
  · right; exact ⟨h, by simp [h]⟩

lemma loss_diff (M : Model d S Ω P) (θ w : Parameter d S) (n : ℕ) (ω : Ω) :
    M.loss n (M.history θ n ω) (θ + w) - M.loss n (M.history θ n ω) θ =
      ∑ k ∈ Finset.Icc 1 n, chi k * ((dot w (rr M k ω)) ^ 2 - 2 * M.eps k ω * dot w (rr M k ω)) := by
  unfold Model.loss
  rw [← Finset.sum_sub_distrib]
  rw [← sum_fin_shift n (fun k => chi k * ((dot w (rr M k ω)) ^ 2 - 2 * M.eps k ω * dot w (rr M k ω)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Model.history, dot_add_left]
  rcases chi_cases (k.1 + 1) with ⟨h, hc⟩ | ⟨h, hc⟩
  · rw [if_pos h, hc]; unfold rr; ring
  · rw [hc]; ring

lemma est_quad (M : Model d S Ω P) (hest : M.IsEstimator) (θ : Parameter d S) {n : ℕ} (hn : 2 ≤ n)
    (ω : Ω) :
    dot (M.est n (M.history θ n ω) - θ) (Matrix.mulVec (M.Jtilde n ω) (M.est n (M.history θ n ω) - θ))
      ≤ 2 * dot (M.est n (M.history θ n ω) - θ) (M.Mvec n ω) := by
  set w := M.est n (M.history θ n ω) - θ
  have hmin := hest n hn (M.history θ n ω) θ
  have he : M.est n (M.history θ n ω) = θ + w := by simp [w]
  rw [he] at hmin
  have hd := loss_diff M θ w n ω
  rw [rayleigh_eq, mvec_dot, Finset.mul_sum]
  have : ∑ k ∈ Finset.Icc 1 n, chi k * ((dot w (rr M k ω)) ^ 2 - 2 * M.eps k ω * dot w (rr M k ω)) ≤ 0 := by
    linarith
  rw [← sub_nonpos, ← Finset.sum_sub_distrib]
  calc _ = ∑ k ∈ Finset.Icc 1 n, chi k * ((dot w (rr M k ω)) ^ 2 - 2 * M.eps k ω * dot w (rr M k ω)) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 0 := this

lemma dot_sq_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) : (dot u v) ^ 2 ≤ sqNorm u * sqNorm v := by
  unfold sqNorm dot
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simpa [sq] using this

lemma sqNorm_nonneg' {ι : Type*} [Fintype ι] (u : ι → ℝ) : 0 ≤ sqNorm u := by
  unfold sqNorm dot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma est_sq_bound (M : Model d S Ω P) (hest : M.IsEstimator) (θ : Parameter d S) {n : ℕ}
    (hn : 2 ≤ n) (ω : Ω) {c : ℝ} (hc : 0 < c)
    (hR : ∀ v : Parameter d S, c * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde n ω) v)) :
    sqNorm (M.est n (M.history θ n ω) - θ) ≤ 4 * sqNorm (M.Mvec n ω) / c ^ 2 := by
  set w := M.est n (M.history θ n ω) - θ
  have h1 := hR w
  have h2 := est_quad M hest θ hn ω
  have h3 := dot_sq_le w (M.Mvec n ω)
  have hw := sqNorm_nonneg' w
  have hm := sqNorm_nonneg' (M.Mvec n ω)
  rw [le_div_iff₀ (by positivity)]
  -- c * |w|^2 ≤ 2 dot w m
  have h4 : c * sqNorm w ≤ 2 * dot w (M.Mvec n ω) := le_trans h1 h2
  have h5 : (c * sqNorm w) ^ 2 ≤ 4 * (sqNorm w * sqNorm (M.Mvec n ω)) := by
    have : 0 ≤ c * sqNorm w := by positivity
    nlinarith
  rcases hw.eq_or_lt with h | h
  · rw [← h]; nlinarith
  · have : sqNorm w * (sqNorm w * c ^ 2) ≤ sqNorm w * (4 * sqNorm (M.Mvec n ω)) := by nlinarith
    nlinarith [le_of_mul_le_mul_left this h]

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma measurable_X (M : Model d S Ω P) {k : ℕ} (hk : 1 ≤ k) : Measurable (M.X k) := by
  unfold Model.X
  have hZ := M.measurable_Z k hk
  refine measurable_pi_lambda _ (fun j => ?_)
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp hZ

lemma regMap_measurable (p : ℝ) :
    Measurable (fun x : Fin (d + 1) → ℝ => (regressor p (restrictX S x) : Parameter d S)) := by
  refine measurable_pi_lambda _ (fun ji => ?_)
  unfold regressor restrictX
  exact measurable_const.mul (measurable_pi_apply _)

lemma regF_meas {m : MeasurableSpace Ω} (p : ℝ) (f : Ω → Fin (d + 1) → ℝ)
    (h : Measurable[m] f) : Measurable[m] (fun ω => (regressor p (restrictX S (f ω)) : Parameter d S)) :=
  fun _ hs => h (regMap_measurable p hs)

lemma rr_measurable_of (M : Model d S Ω P) {m : MeasurableSpace Ω} {k : ℕ}
    (h : @Measurable Ω _ m _ (@Model.X d S Ω mΩ P M k)) :
    @Measurable Ω _ m _ (fun ω => @rr d S Ω mΩ P M k ω) :=
  regF_meas (m := m) _ _ h

lemma past_le (M : Model d S Ω P) (t : ℕ) : M.past t ≤ mΩ := by
  unfold Model.past
  refine sup_le (iSup₂_le fun k hk => ?_) (iSup₂_le fun k hk => ?_)
  · exact (measurable_X M (Finset.mem_Icc.1 hk).1).comap_le
  · exact (M.measurable_eps k (Finset.mem_Icc.1 hk).1).comap_le

lemma G_le (M : Model d S Ω P) (t : ℕ) : M.G t ≤ mΩ :=
  sup_le (past_le M t) (measurable_X M (by omega : 1 ≤ t + 1)).comap_le

lemma X_meas_G (M : Model d S Ω P) {k t : ℕ} (hk : k ∈ Finset.Icc 1 t) :
    Measurable[M.G t] (M.X k) := by
  have h : MeasurableSpace.comap (M.X k) inferInstance ≤ M.G t := by
    unfold Model.G Model.past
    exact le_sup_left.trans' (le_sup_left.trans'
      (le_iSup₂ (f := fun k (_ : k ∈ Finset.Icc 1 t) =>
        MeasurableSpace.comap (M.X k) inferInstance) k hk))
  exact (comap_measurable (M.X k)).mono h le_rfl

lemma eps_meas_G (M : Model d S Ω P) {k t : ℕ} (hk : k ∈ Finset.Icc 1 t) :
    Measurable[M.G t] (M.eps k) := by
  have h : MeasurableSpace.comap (M.eps k) inferInstance ≤ M.G t := by
    unfold Model.G Model.past
    exact le_sup_left.trans' (le_sup_right.trans'
      (le_iSup₂ (f := fun k (_ : k ∈ Finset.Icc 1 t) =>
        MeasurableSpace.comap (M.eps k) inferInstance) k hk))
  exact (comap_measurable (M.eps k)).mono h le_rfl

lemma Xnext_meas_G (M : Model d S Ω P) (t : ℕ) : Measurable[M.G t] (M.X (t + 1)) := by
  have h : MeasurableSpace.comap (M.X (t + 1)) inferInstance ≤ M.G t := by
    unfold Model.G; exact le_sup_right
  exact (comap_measurable _).mono h le_rfl

lemma Mvec_meas_G (M : Model d S Ω P) (t : ℕ) : Measurable[M.G t] (fun ω => M.Mvec t ω) := by
  unfold Model.Mvec
  exact Finset.measurable_sum _ fun k hk =>
    (measurable_const.mul (eps_meas_G M hk)).smul (rr_measurable_of M (X_meas_G M hk))

lemma Mvec_meas (M : Model d S Ω P) (t : ℕ) : Measurable (fun ω => M.Mvec t ω) :=
  (Mvec_meas_G M t).mono (G_le M t) le_rfl

lemma dot_meas {ι : Type*} [Fintype ι] {m : MeasurableSpace Ω} {u v : Ω → ι → ℝ}
    (hu : Measurable[m] u) (hv : Measurable[m] v) : Measurable[m] (fun ω => dot (u ω) (v ω)) := by
  unfold dot
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hu).mul ((measurable_pi_apply i).comp hv)

lemma mvec_succ (M : Model d S Ω P) (t : ℕ) (ω : Ω) :
    M.Mvec (t + 1) ω = M.Mvec t ω + (chi (t + 1) * M.eps (t + 1) ω) • rr M (t + 1) ω := by
  unfold Model.Mvec rr; rw [Finset.sum_Icc_succ_top (by omega)]

lemma sqNorm_add_smul {ι : Type*} [Fintype ι] (u r : ι → ℝ) (c : ℝ) :
    sqNorm (u + c • r) = sqNorm u + 2 * c * dot u r + c ^ 2 * sqNorm r := by
  unfold sqNorm dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma chi_nonneg (k : ℕ) : 0 ≤ chi k := by
  rcases chi_cases k with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num

lemma chi_sq (k : ℕ) : chi k ^ 2 = chi k := by
  rcases chi_cases k with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num

lemma chi_le_one (k : ℕ) : chi k ≤ 1 := by
  rcases chi_cases k with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num

variable [IsProbabilityMeasure P]

lemma eps_sq (M : Model d S Ω P) (N : NoiseConditions P M) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun ω => M.eps k ω ^ 2) P ∧ ∫ ω, M.eps k ω ^ 2 ∂P ≤ M.sigma0 ^ 2 := by
  have hm := G_le M (k - 1)
  have hl : ∫⁻ ω, ENNReal.ofReal (M.eps k ω ^ 2) ∂P ≤ ENNReal.ofReal (M.sigma0 ^ 2) := by
    rw [← lintegral_condLExp hm P]
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (M.sigma0 ^ 2) ∂P := lintegral_mono_ae (N.second_moment k hk)
      _ = _ := by simp
  have hmeas : Measurable (fun ω => M.eps k ω ^ 2) := (M.measurable_eps k hk).pow_const 2
  have hnn : 0 ≤ᵐ[P] (fun ω => M.eps k ω ^ 2) := Filter.Eventually.of_forall fun ω => sq_nonneg _
  refine ⟨⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
    (hl.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hl

lemma mvec_sm (M : Model d S Ω P) (N : NoiseConditions P M) (B : ℝ)
    (hB : ∀ k ω, 1 ≤ k → sqNorm (rr M k ω) ≤ B) (t : ℕ) :
    Integrable (fun ω => sqNorm (M.Mvec t ω)) P ∧
      ∫ ω, sqNorm (M.Mvec t ω) ∂P ≤ M.sigma0 ^ 2 * B * ∑ k ∈ Finset.Icc 1 t, chi k := by
  have hB0 : 0 ≤ B := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact (sqNorm_nonneg' _).trans (hB 1 ω le_rfl)
  induction t with
  | zero =>
    have : ∀ ω, M.Mvec 0 ω = 0 := fun ω => by unfold Model.Mvec; simp
    simp [this, sqNorm, dot]
  | succ t ih =>
    obtain ⟨i1, h1⟩ := ih
    obtain ⟨hε, hεint⟩ := eps_sq M N (by omega : 1 ≤ t + 1)
    set u := fun ω => M.Mvec t ω
    set r := fun ω => rr M (t + 1) ω
    have hu : Measurable u := Mvec_meas M t
    have hr : Measurable r := rr_measurable_of M (measurable_X M (k := t + 1) (by omega))
    have he : Measurable (M.eps (t + 1)) := M.measurable_eps _ (by omega)
    have hdot : Measurable (fun ω => dot (u ω) (r ω)) := dot_meas hu hr
    have hsr : Measurable (fun ω => sqNorm (r ω)) := dot_meas hr hr
    have hsu : Measurable (fun ω => sqNorm (u ω)) := dot_meas hu hu
    have hexp : ∀ ω, sqNorm (M.Mvec (t + 1) ω) =
        sqNorm (u ω) + 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω) +
          (chi (t + 1) * M.eps (t + 1) ω) ^ 2 * sqNorm (r ω) := fun ω => by
      rw [mvec_succ, sqNorm_add_smul]
    have hc0 := chi_nonneg (t + 1)
    have hc1 := chi_le_one (t + 1)
    -- integrability of cross term
    have i2 : Integrable (fun ω => 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω)) P := by
      refine Integrable.mono' (hε.add (i1.const_mul B)) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((measurable_const.mul (measurable_const.mul he)).mul hdot)).aestronglyMeasurable
      · have hd2 := dot_sq_le (u ω) (r ω)
        have hrB := hB (t + 1) ω (by omega)
        have hsu0 := sqNorm_nonneg' (u ω)
        have : (dot (u ω) (r ω)) ^ 2 ≤ B * sqNorm (u ω) := by
          calc _ ≤ sqNorm (u ω) * sqNorm (r ω) := hd2
            _ ≤ sqNorm (u ω) * B := mul_le_mul_of_nonneg_left hrB hsu0
            _ = _ := by ring
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_le]
        have hc2 : (chi (t + 1) * M.eps (t + 1) ω) ^ 2 ≤ M.eps (t + 1) ω ^ 2 := by
          rw [mul_pow, chi_sq]; nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sq_nonneg (M.eps (t + 1) ω))]
        set c := chi (t + 1) * M.eps (t + 1) ω
        set D := dot (u ω) (r ω)
        have key1 : -(c ^ 2 + D ^ 2) ≤ 2 * c * D := by nlinarith [sq_nonneg (c + D)]
        have key2 : 2 * c * D ≤ c ^ 2 + D ^ 2 := by nlinarith [sq_nonneg (c - D)]
        constructor <;> linarith
    have i3 : Integrable (fun ω => (chi (t + 1) * M.eps (t + 1) ω) ^ 2 * sqNorm (r ω)) P := by
      refine Integrable.mono' (hε.const_mul B) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((measurable_const.mul he).pow_const 2).mul hsr).aestronglyMeasurable
      · have hrB := hB (t + 1) ω (by omega)
        have hs0 := sqNorm_nonneg' (r ω)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have hc2 : (chi (t + 1) * M.eps (t + 1) ω) ^ 2 ≤ M.eps (t + 1) ω ^ 2 := by
          rw [mul_pow, chi_sq]; nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sq_nonneg (M.eps (t + 1) ω))]
        calc _ ≤ M.eps (t + 1) ω ^ 2 * B :=
              mul_le_mul hc2 hrB hs0 (sq_nonneg _)
          _ = _ := by ring
    have hfun : (fun ω => sqNorm (M.Mvec (t + 1) ω)) = fun ω =>
        sqNorm (u ω) + 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω) +
          (chi (t + 1) * M.eps (t + 1) ω) ^ 2 * sqNorm (r ω) := funext hexp
    refine ⟨by rw [hfun]; exact (i1.add i2).add i3, ?_⟩
    rw [hfun, integral_add (f := fun ω => sqNorm (u ω) + 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω))
      (i1.add i2) i3, integral_add (f := fun ω => sqNorm (u ω)) i1 i2]
    -- cross term vanishes
    have hcross : ∫ ω, 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω) ∂P = 0 := by
      have hm := G_le M t
      set Y := fun ω => 2 * chi (t + 1) * dot (u ω) (r ω)
      have hY : Measurable[M.G t] Y := by
        have : Measurable[M.G t] (fun ω => dot (u ω) (r ω)) :=
          dot_meas (Mvec_meas_G M t) (rr_measurable_of M (Xnext_meas_G M t))
        exact measurable_const.mul this
      have hfeq : (fun ω => 2 * (chi (t + 1) * M.eps (t + 1) ω) * dot (u ω) (r ω)) =
          Y * M.eps (t + 1) := by
        funext ω; simp only [Pi.mul_apply, Y]; ring
      have hint : Integrable (Y * M.eps (t + 1)) P := hfeq ▸ i2
      have hεi : Integrable (M.eps (t + 1)) P := M.integrable_eps _ (by omega)
      rw [hfeq, ← integral_condExp hm]
      have h1 := condExp_mul_of_stronglyMeasurable_left hY.stronglyMeasurable hint hεi
      have h2 := N.mean_zero (t + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h2
      rw [integral_congr_ae h1]
      have h3 : (Y * P[M.eps (t + 1)|M.G t]) =ᵐ[P] fun _ => (0 : ℝ) := by
        filter_upwards [h2] with ω hω
        simp [hω]
      rw [integral_congr_ae h3]; simp
    rw [hcross, add_zero]
    have hdiag : ∫ ω, (chi (t + 1) * M.eps (t + 1) ω) ^ 2 * sqNorm (r ω) ∂P ≤
        chi (t + 1) * B * M.sigma0 ^ 2 := by
      calc _ ≤ ∫ ω, chi (t + 1) * B * M.eps (t + 1) ω ^ 2 ∂P := by
            refine integral_mono i3 (hε.const_mul _) fun ω => ?_
            have hrB := hB (t + 1) ω (by omega)
            simp only
            rw [mul_pow, chi_sq]
            have := sq_nonneg (M.eps (t + 1) ω)
            calc chi (t + 1) * M.eps (t + 1) ω ^ 2 * sqNorm (r ω)
                ≤ chi (t + 1) * M.eps (t + 1) ω ^ 2 * B :=
                  mul_le_mul_of_nonneg_left hrB (by positivity)
              _ = _ := by ring
        _ = chi (t + 1) * B * ∫ ω, M.eps (t + 1) ω ^ 2 ∂P := integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hεint (by positivity)
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

lemma chi_sum_le (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, chi k ≤ 2 * Real.sqrt n := by
  classical
  set A := (Finset.Icc 1 (Nat.sqrt n)).image (fun L => L ^ 2)
  set B := (Finset.Icc 1 (Nat.sqrt n)).image (fun L => L ^ 2 + 1)
  have h1 : ∑ k ∈ Finset.Icc 1 n, chi k ≤ ∑ k ∈ Finset.Icc 1 n, (if k ∈ A ∪ B then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum; intro k hk
    rcases chi_cases k with ⟨h, hc⟩ | ⟨_, hc⟩
    · rw [hc, if_pos]
      have hkn := (Finset.mem_Icc.1 hk).2
      rcases h with ⟨L, hL, rfl⟩ | ⟨L, hL, rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨L, Finset.mem_Icc.2 ⟨hL,
          Nat.le_sqrt'.2 hkn⟩, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨L, Finset.mem_Icc.2 ⟨hL,
          Nat.le_sqrt'.2 (by omega)⟩, rfl⟩)
    · rw [hc]; split_ifs <;> norm_num
  rw [Finset.sum_boole] at h1
  have h2 : ((Finset.Icc 1 n).filter (fun k => k ∈ A ∪ B)).card ≤ 2 * Nat.sqrt n := by
    calc _ ≤ (A ∪ B).card := Finset.card_le_card (fun k hk => (Finset.mem_filter.1 hk).2)
      _ ≤ A.card + B.card := Finset.card_union_le _ _
      _ ≤ (Finset.Icc 1 (Nat.sqrt n)).card + (Finset.Icc 1 (Nat.sqrt n)).card :=
          add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * Nat.sqrt n := by simp; ring
  have h3 : ((2 * Nat.sqrt n : ℕ) : ℝ) ≤ 2 * Real.sqrt n := by
    push_cast; linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
  calc _ ≤ _ := h1
    _ ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h2
    _ ≤ _ := h3

lemma inv_sqrt_sum_le (T : ℕ) : ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : 0 < Real.sqrt ((T + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha2 : Real.sqrt ((T + 1 : ℕ) : ℝ) ^ 2 = T + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hb2 : Real.sqrt (T : ℝ) ^ 2 = T := Real.sq_sqrt (by positivity)
    have hb : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
    have hab : Real.sqrt (T : ℝ) ≤ Real.sqrt ((T + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have : 1 / Real.sqrt ((T + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((T + 1 : ℕ) : ℝ) - 2 * Real.sqrt (T : ℝ) := by
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (Real.sqrt ((T + 1 : ℕ) : ℝ) - Real.sqrt (T : ℝ))]
    linarith

lemma small_sum_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (if t ≤ 6 then (1 : ℝ) else 0) ≤ 6 := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : ((Finset.Icc 1 T).filter (fun t => t ≤ 6)).card ≤ 6 := by
    calc _ ≤ (Finset.Icc 1 6).card := Finset.card_le_card (fun t ht => by
          simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢; omega)
      _ = 6 := by simp
  exact_mod_cast this

lemma one_le_ofReal_add (x : ℝ) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal x + ENNReal.ofReal (1 - x) := by
  rcases le_total x 0 with h0 | h0
  · calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (1 - x) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := le_add_self
  rcases le_total x 1 with h | h
  · rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal h
      _ ≤ _ := le_self_add

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

noncomputable def Br (M : Model d S Ω P) : ℝ :=
  ∑ _j : Fin 2 × ↥S, (1 + M.upper ^ 2) * (1 + M.zmax) ^ 2

lemma rr_bound (M : Model d S Ω P) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) : sqNorm (rr M k ω) ≤ Br M := by
  unfold sqNorm dot Br rr regressor
  apply Finset.sum_le_sum; intro j _
  have hx := abs_le.1 (xS_bound M hk ω j.2)
  have hL := M.lower_pos
  have hp : |M.experimentPrice k| ≤ M.upper := by
    unfold Model.experimentPrice
    split_ifs
    · rw [abs_of_pos (by linarith [M.m1_mem.1])]; exact M.m1_mem.2
    · rw [abs_of_pos (by linarith [M.m2_mem.1])]; exact M.m2_mem.2
  have hc : (if j.1 = 0 then (1 : ℝ) else M.experimentPrice k) ^ 2 ≤ 1 + M.upper ^ 2 := by
    split_ifs
    · nlinarith [sq_nonneg M.upper]
    · have := abs_le.1 hp
      nlinarith [sq_le_sq' this.1 this.2]
  have hx2 : restrictX S (M.X k ω) j.2 ^ 2 ≤ (1 + M.zmax) ^ 2 := sq_le_sq' hx.1 hx.2
  calc _ = (if j.1 = 0 then (1 : ℝ) else M.experimentPrice k) ^ 2 *
        restrictX S (M.X k ω) j.2 ^ 2 := by ring
    _ ≤ _ := mul_le_mul hc hx2 (sq_nonneg _) (by positivity)

lemma Br_nonneg (M : Model d S Ω P) : 0 ≤ Br M := by
  unfold Br; exact Finset.sum_nonneg fun _ _ => by positivity

lemma price_mem (M : Model d S Ω P) (I : InteriorConditions M) (θ : Parameter d S) {t : ℕ}
    (ht : 1 ≤ t) (ω : Ω) : M.price θ t ω ∈ Set.Icc M.lower M.upper := by
  unfold Model.price
  split_ifs
  · exact M.m1_mem
  · exact M.m2_mem
  · exact Set.Ioo_subset_Icc_self (I.optimum_interior _ (clamp_mem M _) t ω ht)

lemma price_nonexp (M : Model d S Ω P) (θ : Parameter d S) {t : ℕ} (h : ¬(inM1 t ∨ inM2 t))
    (ω : Ω) : M.price θ t ω = phi (clamp M.lo M.hi (M.est (t - 1) (M.history θ (t - 1) ω)))
      (restrictX S (M.X t ω)) := by
  unfold Model.price
  rw [not_or] at h
  rw [if_neg h.1, if_neg h.2]

lemma Gset_meas (M : Model d S Ω P) (n : ℕ) (c : ℝ) :
    MeasurableSet {ω | ∀ v : Parameter d S, c * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde n ω) v)} := by
  set Φ : Ω → (Fin 2 × ↥S) → (Fin 2 × ↥S) → ℝ := fun ω i j => M.Jtilde n ω i j
  have hΦ : Measurable Φ := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have : (fun ω => M.Jtilde n ω i j) =
        fun ω => ∑ k ∈ Finset.Icc 1 n, chi k * (rr M k ω i * rr M k ω j) := by
      funext ω; simp [Model.Jtilde, Matrix.sum_apply, Matrix.vecMulVec_apply, rr]
    show Measurable (fun ω => M.Jtilde n ω i j)
    rw [this]
    exact Finset.measurable_sum _ fun k hk =>
      have hr := rr_measurable_of M (measurable_X M (Finset.mem_Icc.1 hk).1)
      measurable_const.mul (((measurable_pi_apply i).comp hr).mul ((measurable_pi_apply j).comp hr))
  have hC : IsClosed {A : (Fin 2 × ↥S) → (Fin 2 × ↥S) → ℝ |
      ∀ v : Parameter d S, c * sqNorm v ≤ ∑ i, v i * ∑ j, A i j * v j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop)
  have : {ω | ∀ v : Parameter d S, c * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde n ω) v)} =
      Φ ⁻¹' {A | ∀ v : Parameter d S, c * sqNorm v ≤ ∑ i, v i * ∑ j, A i j * v j} := by
    ext ω; simp [Φ, dot, Matrix.mulVec, dotProduct]
  rw [this]; exact hΦ hC.measurableSet

/-- The real-number bookkeeping for a late, non-experimental period. -/
lemma late_real (Kc0 Cm σ2 Br0 γ κ ρ g8 s Nn J : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hK : 0 ≤ Kc0) (hCm : 0 ≤ Cm) (hσ : 0 ≤ σ2) (hB : 0 ≤ Br0) (hγ : 0 < γ) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hg : 0 < g8) (hs : 1 ≤ s) (hN : Nn ≤ 2 * Real.sqrt n)
    (hJ : g8 * Real.sqrt n ≤ J) :
    Kc0 * 4 / (γ * J) ^ 2 * (σ2 * Br0 * Nn) + Cm * (κ * s * Real.exp (-ρ * J)) ≤
      2 * (8 * Kc0 * σ2 * Br0 / (γ ^ 2 * g8 ^ 2) + Cm * κ / (ρ * g8)) * s /
        Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  set q := Real.sqrt n with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hJ0 : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hN0 : 0 ≤ Nn ∨ Nn < 0 := le_or_gt 0 Nn
  have T1 : Kc0 * 4 / (γ * J) ^ 2 * (σ2 * Br0 * Nn) ≤ 8 * Kc0 * σ2 * Br0 / (γ ^ 2 * g8 ^ 2) / q := by
    rcases hN0 with hN0 | hN0
    · calc Kc0 * 4 / (γ * J) ^ 2 * (σ2 * Br0 * Nn)
          ≤ Kc0 * 4 / (γ * (g8 * q)) ^ 2 * (σ2 * Br0 * (2 * q)) := by gcongr
        _ = _ := by field_simp; ring
    · have : Kc0 * 4 / (γ * J) ^ 2 * (σ2 * Br0 * Nn) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hN0.le
      exact this.trans (by positivity)
  have hexp : Real.exp (-ρ * J) ≤ 1 / (ρ * J) := by
    have h1 := Real.add_one_le_exp (ρ * J)
    rw [neg_mul, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have T2 : Cm * (κ * s * Real.exp (-ρ * J)) ≤ Cm * κ / (ρ * g8) * s / q := by
    calc Cm * (κ * s * Real.exp (-ρ * J)) ≤ Cm * (κ * s * (1 / (ρ * J))) := by gcongr
      _ ≤ Cm * (κ * s * (1 / (ρ * (g8 * q)))) := by gcongr
      _ = _ := by field_simp
  have hsq : q ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hsq2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * q := by
    rw [hq, show (2 : ℝ) * Real.sqrt n = Real.sqrt (4 * n) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    apply Real.sqrt_le_sqrt; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set A0 := 8 * Kc0 * σ2 * Br0 / (γ ^ 2 * g8 ^ 2)
  set A0' := Cm * κ / (ρ * g8)
  have hA0 : 0 ≤ A0 := by positivity
  have hA0' : 0 ≤ A0' := by positivity
  have hsqt : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hq0 hsq
  calc _ ≤ A0 / q + A0' * s / q := add_le_add T1 T2
    _ ≤ (A0 + A0') * s / q := by
        rw [← add_div]; gcongr; nlinarith
    _ ≤ (A0 + A0') * s / (Real.sqrt ((n + 1 : ℕ) : ℝ) / 2) := by
        gcongr
        linarith
    _ = _ := by field_simp

end BK2A

open MeasureTheory
open scoped ENNReal

namespace BK2A

open BanKeskin.KnownSparsity

variable {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma Cmax_nonneg (M : Model d S Ω P) : 0 ≤ Cmax M := mul_nonneg (Bb_nonneg M) (sq_nonneg _)

lemma Kc_nonneg (M : Model d S Ω P) : 0 ≤ Kc M :=
  mul_nonneg (Bb_nonneg M) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

noncomputable def A1 (M : Model d S Ω P) (γ κ ρ : ℝ) : ℝ :=
  2 * (8 * Kc M * M.sigma0 ^ 2 * Br M / (γ ^ 2 * ((M.m1 - M.m2) ^ 2 / 8) ^ 2) +
    Cmax M * κ / (ρ * ((M.m1 - M.m2) ^ 2 / 8)))

noncomputable def At (M : Model d S Ω P) (γ κ ρ : ℝ) (t : ℕ) : ℝ :=
  Cmax M * (if t ≤ 6 then 1 else 0) + Cmax M * chi t +
    A1 M γ κ ρ * (S.card : ℝ) * (1 / Real.sqrt t)

lemma A1_nonneg (M : Model d S Ω P) {γ κ ρ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hρ : 0 < ρ) :
    0 ≤ A1 M γ κ ρ := by
  have hm : 0 < (M.m1 - M.m2) ^ 2 / 8 := by
    have := sub_ne_zero.2 M.m_ne; positivity
  have := Kc_nonneg M; have := Cmax_nonneg M; have := Br_nonneg M
  unfold A1; positivity

lemma At_nonneg (M : Model d S Ω P) {γ κ ρ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hρ : 0 < ρ) (t : ℕ) :
    0 ≤ At M γ κ ρ t := by
  have := Cmax_nonneg M; have := A1_nonneg M hγ hκ hρ; have := chi_nonneg t
  unfold At
  have : (0 : ℝ) ≤ if t ≤ 6 then 1 else 0 := by split_ifs <;> norm_num
  positivity

variable [IsProbabilityMeasure P]

lemma per_t (M : Model d S Ω P) (N : NoiseConditions P M) (I : InteriorConditions M)
    (hest : M.IsEstimator) {γ κ ρ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hL1 : ∀ θ ∈ M.Theta, ∀ t : ℕ, 2 ≤ t →
        ENNReal.ofReal (1 - κ * (S.card : ℝ) * Real.exp (-ρ * M.J t)) ≤
          P {ω | ∀ v : Parameter d S,
            γ * M.J t * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde t ω) v)})
    (hJ : ∀ t : ℕ, 5 ≤ t → (1 / 8 : ℝ) * (M.m1 - M.m2) ^ 2 * Real.sqrt (t : ℝ) ≤ M.J t)
    {θ : Parameter d S} (hθ : θ ∈ M.Theta) (t : ℕ) :
    ∃ g : Ω → ℝ≥0∞, Measurable g ∧
      (1 ≤ t → ∀ ω, ENNReal.ofReal (M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) -
        M.revenue θ (M.price θ t ω) (M.X t ω)) ≤ g ω) ∧
      ∫⁻ ω, g ω ∂P ≤ ENNReal.ofReal (At M γ κ ρ t) := by
  have hCm := Cmax_nonneg M
  have hA1 := A1_nonneg M hγ hκ hρ
  have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast M.support_nonempty
  by_cases h0 : t = 0
  · refine ⟨fun _ => 0, measurable_const, fun h => by omega, by simp⟩
  by_cases hbad : t ≤ 6 ∨ (inM1 t ∨ inM2 t)
  · refine ⟨fun _ => ENNReal.ofReal (Cmax M), measurable_const, fun ht ω => ?_, ?_⟩
    · exact ENNReal.ofReal_le_ofReal (gap_le_Cmax M I ht ω hθ (price_mem M I θ ht ω))
    · simp only [lintegral_const, measure_univ, mul_one]
      apply ENNReal.ofReal_le_ofReal
      unfold At
      have hc := chi_nonneg t
      have : 0 ≤ A1 M γ κ ρ * (S.card : ℝ) * (1 / Real.sqrt t) := by positivity
      rcases hbad with h | h
      · rw [if_pos h]; nlinarith
      · rcases chi_cases t with ⟨_, hc1⟩ | ⟨h', _⟩
        · rw [hc1]; have : (0 : ℝ) ≤ if t ≤ 6 then 1 else 0 := by split_ifs <;> norm_num
          nlinarith
        · exact absurd h h'
  push_neg at hbad
  obtain ⟨ht7, hne'⟩ := hbad
  have hne : ¬(inM1 t ∨ inM2 t) := by rw [not_or]; exact hne'
  set n := t - 1 with hn
  have hn6 : 6 ≤ n := by omega
  have htn : n + 1 = t := by omega
  have hchi : chi t = 0 := by
    rcases chi_cases t with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h hne
    · exact h
  set G := {ω | ∀ v : Parameter d S, γ * M.J n * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde n ω) v)}
  have hGm : MeasurableSet G := Gset_meas M n (γ * M.J n)
  have hJn := hJ n (by omega)
  have hg8 : 0 < (M.m1 - M.m2) ^ 2 / 8 := by have := sub_ne_zero.2 M.m_ne; positivity
  have hJpos : 0 < M.J n := by
    have : 0 < (1 / 8 : ℝ) * (M.m1 - M.m2) ^ 2 * Real.sqrt (n : ℝ) := by
      have := Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast (by omega : 0 < n))
      have := sub_ne_zero.2 M.m_ne; positivity
    linarith
  have hc : 0 < γ * M.J n := mul_pos hγ hJpos
  set a := Kc M * 4 / (γ * M.J n) ^ 2 with ha
  have ha0 : 0 ≤ a := by have := Kc_nonneg M; positivity
  have hm1 : Measurable (fun ω => ENNReal.ofReal (a * sqNorm (M.Mvec n ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (dot_meas (Mvec_meas M n) (Mvec_meas M n)))
  refine ⟨fun ω => ENNReal.ofReal (a * sqNorm (M.Mvec n ω)) +
      Gᶜ.indicator (fun _ => ENNReal.ofReal (Cmax M)) ω,
    hm1.add (measurable_const.indicator hGm.compl), fun ht ω => ?_, ?_⟩
  · by_cases hω : ω ∈ G
    · refine le_trans ?_ le_self_add
      apply ENNReal.ofReal_le_ofReal
      rw [price_nonexp M θ hne ω]
      have h1 := gap_le_K M I ht ω hθ (clamp_mem M (M.est (t - 1) (M.history θ (t - 1) ω)))
      have h2 := clamp_sq M (M.est (t - 1) (M.history θ (t - 1) ω)) hθ
      have h3 := est_sq_bound M hest θ (n := n) (by omega) ω hc hω
      have hK := Kc_nonneg M
      calc _ ≤ _ := h1
        _ ≤ Kc M * sqNorm (M.est n (M.history θ n ω) - θ) := mul_le_mul_of_nonneg_left h2 hK
        _ ≤ Kc M * (4 * sqNorm (M.Mvec n ω) / (γ * M.J n) ^ 2) := mul_le_mul_of_nonneg_left h3 hK
        _ = _ := by rw [ha]; ring
    · refine le_trans ?_ le_add_self
      rw [Set.indicator_of_mem (Set.mem_compl hω)]
      exact ENNReal.ofReal_le_ofReal (gap_le_Cmax M I ht ω hθ (price_mem M I θ ht ω))
  · rw [lintegral_add_left hm1, lintegral_indicator_const hGm.compl]
    have hB := fun k ω hk => rr_bound M (k := k) hk ω
    obtain ⟨hint, hbound⟩ := mvec_sm M N (Br M) hB n
    have e1 : ∫⁻ ω, ENNReal.ofReal (a * sqNorm (M.Mvec n ω)) ∂P =
        ENNReal.ofReal a * ENNReal.ofReal (∫ ω, sqNorm (M.Mvec n ω) ∂P) := by
      simp_rw [ENNReal.ofReal_mul ha0]
      rw [lintegral_const_mul _ (show Measurable (fun ω => ENNReal.ofReal (sqNorm (M.Mvec n ω))) from
        (dot_meas (Mvec_meas M n) (Mvec_meas M n)).ennreal_ofReal)]
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω => sqNorm_nonneg' _)]
    have e2 : P Gᶜ ≤ ENNReal.ofReal (κ * (S.card : ℝ) * Real.exp (-ρ * M.J n)) := by
      rw [prob_compl_eq_one_sub hGm, tsub_le_iff_right]
      exact (one_le_ofReal_add (κ * (S.card : ℝ) * Real.exp (-ρ * M.J n))).trans
        (add_le_add_right (hL1 θ hθ n (by omega)) _)
    rw [e1]
    calc _ ≤ ENNReal.ofReal a * ENNReal.ofReal (M.sigma0 ^ 2 * Br M * ∑ k ∈ Finset.Icc 1 n, chi k) +
          ENNReal.ofReal (Cmax M) * ENNReal.ofReal (κ * (S.card : ℝ) * Real.exp (-ρ * M.J n)) := by
          gcongr
      _ = ENNReal.ofReal (a * (M.sigma0 ^ 2 * Br M * ∑ k ∈ Finset.Icc 1 n, chi k) +
            Cmax M * (κ * (S.card : ℝ) * Real.exp (-ρ * M.J n))) := by
          rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hCm, ← ENNReal.ofReal_add]
          · have := Br_nonneg M
            have := Finset.sum_nonneg fun k (_ : k ∈ Finset.Icc 1 n) => chi_nonneg k
            positivity
          · positivity
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hl := late_real (Kc M) (Cmax M) (M.sigma0 ^ 2) (Br M) γ κ ρ
            ((M.m1 - M.m2) ^ 2 / 8) (S.card : ℝ) (∑ k ∈ Finset.Icc 1 n, chi k) (M.J n) n
            (by omega) (Kc_nonneg M) hCm (sq_nonneg _) (Br_nonneg M) hγ hκ hρ hg8 hs1
            (chi_sum_le n) (by linarith)
          rw [htn] at hl
          unfold At
          rw [hchi, if_neg (by omega)]
          calc _ ≤ _ := hl
            _ = A1 M γ κ ρ * (S.card : ℝ) * (1 / Real.sqrt t) := by unfold A1; ring
            _ ≤ _ := by simp

end BK2A

open MeasureTheory
open scoped ENNReal

open BanKeskin.KnownSparsity BK2A in
theorem solution {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Model d S Ω P) (N : NoiseConditions P M) (I : InteriorConditions M)
    (hest : M.IsEstimator) :
    ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ M.Theta, ∀ T : ℕ, 2 ≤ T →
        M.regret θ T ≤ ENNReal.ofReal
          (C * (S.card : ℝ) * Real.sqrt (T : ℝ) * Real.log (T : ℝ)) := by
  obtain ⟨γ, κ, ρ, hγ, hκ, hρ, hL1⟩ := lemma_1 P M N I hest
  have hJ := fun t ht => eq_15 P M t ht
  have hCm := Cmax_nonneg M
  have hA1 := A1_nonneg M hγ hκ hρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K0 := 8 * Cmax M + 2 * A1 M γ κ ρ with hK0
  have hK0n : 0 ≤ K0 := by positivity
  refine ⟨K0 / Real.log 2 + 1, by positivity, fun θ hθ T hT => ?_⟩
  have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast M.support_nonempty
  choose g hgm hgle hgint using fun t => per_t M N I hest hγ hκ hρ hL1 hJ hθ t
  have hsum : ∑ t ∈ Finset.Icc 1 T, At M γ κ ρ t ≤
      K0 / Real.log 2 + 1 * 0 + (K0 / Real.log 2 + 1) * (S.card : ℝ) * Real.sqrt T * Real.log T -
        (K0 / Real.log 2 + 1 * 0) := by
    have hT1 : (1 : ℝ) ≤ Real.sqrt T := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ T)
    have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have e : ∑ t ∈ Finset.Icc 1 T, At M γ κ ρ t =
        Cmax M * ∑ t ∈ Finset.Icc 1 T, (if t ≤ 6 then (1 : ℝ) else 0) +
          Cmax M * ∑ t ∈ Finset.Icc 1 T, chi t +
          A1 M γ κ ρ * (S.card : ℝ) * ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t := by
      unfold At; rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
    rw [e]
    have h1 := small_sum_le T
    have h2 := chi_sum_le T
    have h3 := inv_sqrt_sum_le T
    have hb : Cmax M * ∑ t ∈ Finset.Icc 1 T, (if t ≤ 6 then (1 : ℝ) else 0) +
          Cmax M * ∑ t ∈ Finset.Icc 1 T, chi t +
          A1 M γ κ ρ * (S.card : ℝ) * ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t ≤
        K0 * (S.card : ℝ) * Real.sqrt T := by
      have hsT : 1 ≤ (S.card : ℝ) * Real.sqrt T := by nlinarith
      calc _ ≤ Cmax M * 6 + Cmax M * (2 * Real.sqrt T) +
            A1 M γ κ ρ * (S.card : ℝ) * (2 * Real.sqrt T) := by gcongr
        _ ≤ _ := by
          rw [hK0]
          nlinarith [mul_le_mul_of_nonneg_left hsT hCm,
            mul_le_mul_of_nonneg_left (show Real.sqrt T ≤ (S.card : ℝ) * Real.sqrt T by nlinarith) hCm]
    have hc : K0 ≤ (K0 / Real.log 2 + 1) * Real.log T := by
      have : K0 ≤ K0 / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlogT hK0n
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ T by exact_mod_cast (by omega : 1 ≤ T))]
    have hpos : 0 ≤ (S.card : ℝ) * Real.sqrt T := by positivity
    have := mul_le_mul_of_nonneg_right hc hpos
    linarith
  calc M.regret θ T
      = ∫⁻ ω, ∑ t ∈ Finset.Icc 1 T, ENNReal.ofReal
          (M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) -
            M.revenue θ (M.price θ t ω) (M.X t ω)) ∂P := rfl
    _ ≤ ∫⁻ ω, ∑ t ∈ Finset.Icc 1 T, g t ω ∂P :=
        lintegral_mono fun ω => Finset.sum_le_sum fun t ht => hgle t (Finset.mem_Icc.1 ht).1 ω
    _ = ∑ t ∈ Finset.Icc 1 T, ∫⁻ ω, g t ω ∂P := lintegral_finset_sum _ fun t _ => hgm t
    _ ≤ ∑ t ∈ Finset.Icc 1 T, ENNReal.ofReal (At M γ κ ρ t) := Finset.sum_le_sum fun t _ => hgint t
    _ = ENNReal.ofReal (∑ t ∈ Finset.Icc 1 T, At M γ κ ρ t) :=
        (ENNReal.ofReal_sum_of_nonneg fun t _ => At_nonneg M hγ hκ hρ t).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        linarith
