-- Prove2me | solution 1 for CritWinSpin.p6b_6_3_lift_props
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T04:03:47.374911+00:00
-- url     : https://prove2.me/submissions/36e89b54-7b54-4d8b-b744-6edd37f77936

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
import Theorems.Thm_CritWinSpin_lemma_3_1_ii

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

namespace CritWinSpin

private lemma p6b63_tau_pos (S : SpinLaw) : 0 < tau S := by
  have hvar_pos : 0 < varQ S := by
    unfold varQ
    have hsum_pos : 0 < ∑ x ∈ S.A, x ^ 2 * S.ρ x := by
      apply Finset.sum_pos'
      · intro x hx
        exact mul_nonneg (sq_nonneg x) (le_of_lt (S.pos x hx))
      · refine ⟨1, S.one_mem, ?_⟩
        simpa using S.pos 1 S.one_mem
    exact hsum_pos
  unfold tau tauQ
  have hq : 0 < (1 / varQ S : ℚ) := div_pos zero_lt_one hvar_pos
  exact_mod_cast hq

private lemma p6b63_width_nonneg {ι : Type} [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    0 ≤ width J h := by
  by_cases hne : Nonempty ι
  · let i₀ := Classical.arbitrary ι
    have hle : |h i₀| + ∑ j, |J i₀ j| ≤ width J h := by
      unfold width
      exact le_ciSup (f := fun i => |h i| + ∑ j, |J i j|) (Finite.bddAbove_range _) i₀
    have hnn : 0 ≤ |h i₀| + ∑ j, |J i₀ j| :=
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact hnn.trans hle
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    unfold width
    simp

private lemma p6b63_row_abs_le_width {ι : Type} [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (i : ι) : |h i| + ∑ j, |J i j| ≤ width J h := by
  unfold width
  exact le_ciSup (f := fun k => |h k| + ∑ j, |J k j|) (Finite.bddAbove_range _) i

private lemma p6b63_quad_bound {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hSymm : J.IsSymm) (w : Fin n → ℝ) :
    |∑ i, ∑ j, J i j * w i * w j| ≤ width J h * ∑ i, w i ^ 2 := by
  have htri : |∑ i, ∑ j, J i j * w i * w j| ≤ ∑ i, ∑ j, |J i j| * |w i| * |w j| := by
    calc |∑ i, ∑ j, J i j * w i * w j|
        ≤ ∑ i, |∑ j, J i j * w i * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |J i j * w i * w j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∑ j, |J i j| * |w i| * |w j| := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_mul]
  have ham : ∑ i, ∑ j, |J i j| * |w i| * |w j| ≤
      (1 / 2 : ℝ) * ∑ i, ∑ j, |J i j| * (w i ^ 2 + w j ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hsq : 0 ≤ (|w i| - |w j|) ^ 2 := sq_nonneg _
    have h2 : |w i| * |w j| ≤ (w i ^ 2 + w j ^ 2) / 2 := by
      nlinarith only [hsq, sq_abs (w i), sq_abs (w j)]
    calc |J i j| * |w i| * |w j| = |J i j| * (|w i| * |w j|) := by ring
      _ ≤ |J i j| * ((w i ^ 2 + w j ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (1 / 2) * (|J i j| * (w i ^ 2 + w j ^ 2)) := by ring
  have hcol : ∀ j, ∑ i, |J i j| = ∑ i, |J j i| := by
    intro j
    refine Finset.sum_congr rfl fun i _ => ?_
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) hSymm
    simpa [Matrix.transpose_apply] using congrArg abs hij
  have hsplit : (1 / 2 : ℝ) * ∑ i, ∑ j, |J i j| * (w i ^ 2 + w j ^ 2) =
      ∑ i, (∑ j, |J i j|) * w i ^ 2 := by
    have ha : ∑ i, ∑ j, |J i j| * (w i ^ 2 + w j ^ 2) =
        ∑ i, ∑ j, |J i j| * w i ^ 2 + ∑ i, ∑ j, |J i j| * w j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have h1 : ∑ i, ∑ j, |J i j| * w i ^ 2 = ∑ i, (∑ j, |J i j|) * w i ^ 2 :=
      Finset.sum_congr rfl fun i _ => (Finset.sum_mul Finset.univ (fun j => |J i j|) (w i ^ 2)).symm
    have h2 : ∑ i, ∑ j, |J i j| * w j ^ 2 = ∑ j, (∑ i, |J i j|) * w j ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul Finset.univ (fun i => |J i j|) (w j ^ 2)).symm
    have h3 : ∑ j, (∑ i, |J i j|) * w j ^ 2 = ∑ j, (∑ i, |J j i|) * w j ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [hcol j]
    rw [ha, h1, h2, h3]
    ring
  calc |∑ i, ∑ j, J i j * w i * w j|
      ≤ ∑ i, (∑ j, |J i j|) * w i ^ 2 := le_trans htri (le_trans ham hsplit.le)
    _ ≤ ∑ i, width J h * w i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have hw := p6b63_row_abs_le_width J h i
        linarith [abs_nonneg (h i)]
    _ = width J h * ∑ i, w i ^ 2 := (Finset.mul_sum _ _ _).symm

private lemma p6b63_liftJQ_quad {S : SpinLaw} {p Ac Cc n : ℕ} (hr : 1 ≤ cloudSize p Cc n)
    (H : Inst n) (û : ℚ) (hû : û ≠ 0) (v : Fin n × Fin (cloudSize p Cc n) → ℝ) :
    let r := cloudSize p Cc n
    let β := tau S + ((thetaQ p Ac Cc n : ℚ) : ℝ)
    let J₀ := castM H.1
    let w : Fin n → ℝ := fun i => ∑ α : Fin r, v (i, α)
    (∑ a, ∑ b, v a * (castM (liftJQ S p Ac Cc H û) a b) * v b) =
      (1 / (r : ℝ)) * (β * ∑ i, w i ^ 2 + (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, J₀ i j * w i * w j) := by
  intro r β J₀ w
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hû_ne : (û : ℝ) ≠ 0 := by exact_mod_cast hû
  have hentry : ∀ a b : Fin n × Fin r,
      castM (liftJQ S p Ac Cc H û) a b =
        ((if a.1 = b.1 then β else 0) + J₀ a.1 b.1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (1 / (r : ℝ)) := by
    intro a b
    dsimp [castM, liftJQ, liftJ, Matrix.map_apply, β, J₀, r]
    split_ifs with h
    · push_cast [tau]; ring
    · push_cast; ring
  calc ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r, v a * castM (liftJQ S p Ac Cc H û) a b * v b
      = ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r,
          (1 / (r : ℝ)) * (v a * ((if a.1 = b.1 then β else 0) + J₀ a.1 b.1 / ((r : ℝ) * (û : ℝ) ^ 2)) * v b) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hentry a b]; ring
    _ = (1 / (r : ℝ)) * ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r,
          (v a * (if a.1 = b.1 then β else 0) * v b +
            (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (J₀ a.1 b.1 * v a * v b)) := by
          simp_rw [← Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = (1 / (r : ℝ)) * ((∑ i : Fin n, ∑ j : Fin n,
          (if i = j then β else 0) * (∑ α : Fin r, v (i, α)) * (∑ γ : Fin r, v (j, γ))) +
          (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
            J₀ i j * (∑ α : Fin r, v (i, α)) * (∑ γ : Fin r, v (j, γ))) := by
          congr 1
          have hpair : ∀ F : (Fin n × Fin r) → (Fin n × Fin r) → ℝ,
              ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r, F a b =
                ∑ i : Fin n, ∑ j : Fin n, ∑ α : Fin r, ∑ γ : Fin r, F (i, α) (j, γ) := by
            intro F
            rw [Fintype.sum_prod_type]
            simp only [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
          have hA : ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r, v a * (if a.1 = b.1 then β else 0) * v b =
              ∑ i : Fin n, ∑ j : Fin n, (if i = j then β else 0) * (∑ α : Fin r, v (i, α)) * (∑ γ : Fin r, v (j, γ)) := by
            rw [hpair]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.sum_comm]
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun α _ => by dsimp only; ring
          have hB : ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r, (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (J₀ a.1 b.1 * v a * v b) =
              (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
                J₀ i j * (∑ α : Fin r, v (i, α)) * (∑ γ : Fin r, v (j, γ)) := by
            simp_rw [← Finset.mul_sum]
            congr 1
            rw [hpair]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.sum_comm]
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
          have hsplit : ∑ a : Fin n × Fin r, ∑ b : Fin n × Fin r,
              (v a * (if a.1 = b.1 then β else 0) * v b +
                (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (J₀ a.1 b.1 * v a * v b)) =
              (∑ a, ∑ b, v a * (if a.1 = b.1 then β else 0) * v b) +
                ∑ a, ∑ b, (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (J₀ a.1 b.1 * v a * v b) := by
            simp_rw [Finset.sum_add_distrib]
            rfl
          rw [hsplit, hA, hB]
    _ = (1 / (r : ℝ)) * (β * ∑ i, w i ^ 2 + (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, J₀ i j * w i * w j) := by
          congr 2
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sq]
          ring

private lemma p6b63_sum_w_sq_le {n r : ℕ} (v : Fin n × Fin r → ℝ) :
    (∑ i : Fin n, (∑ α : Fin r, v (i, α)) ^ 2) ≤ (r : ℝ) * ∑ a : Fin n × Fin r, v a ^ 2 := by
  calc ∑ i : Fin n, (∑ α : Fin r, v (i, α)) ^ 2
      ≤ ∑ i : Fin n, ((r : ℝ) * ∑ α : Fin r, v (i, α) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r))) (f := fun α => v (i, α))
        simpa [Finset.card_univ, Fintype.card_fin] using hcs
    _ = (r : ℝ) * ∑ i : Fin n, ∑ α : Fin r, v (i, α) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = (r : ℝ) * ∑ a : Fin n × Fin r, v a ^ 2 := by rw [Fintype.sum_prod_type]

private lemma p6b63_liftJQ_isHermitian {S : SpinLaw} {p Ac Cc n : ℕ}
    (H : Inst n) (hSymm : H.1.IsSymm) (û : ℚ) :
    (castM (liftJQ S p Ac Cc H û)).IsHermitian := by
  have hmat : ∀ i j : Fin n, H.1 j i = H.1 i j := by
    intro i j
    have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i j) hSymm
    simpa [Matrix.transpose_apply] using ht
  ext a b
  change ((liftJQ S p Ac Cc H û b a : ℚ) : ℝ) = ((liftJQ S p Ac Cc H û a b : ℚ) : ℝ)
  congr 1
  dsimp [liftJQ, liftJ]
  have h1 := hmat a.1 b.1
  by_cases hab : b.1 = a.1
  · rw [if_pos hab, if_pos hab.symm, h1]
  · have hne : a.1 ≠ b.1 := fun h => hab h.symm
    rw [if_neg hab, if_neg hne, h1]

theorem p6b_6_3_lift_props (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
        ∃ n₀ : ℕ, ∀ (n : ℕ) (H : Inst n), n₀ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          ∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
            (castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
            ((tau S * (1 + ((n * cloudSize p Cc n : ℕ) : ℝ) ^ (-dExp p + ε))) •
                (1 : Matrix (Fin (n * cloudSize p Cc n)) (Fin (n * cloudSize p Cc n)) ℝ) -
              castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
            width (castM (liftInst S p Ac Cc H û).1) (castV (liftInst S p Ac Cc H û).2) ≤ Cρ ∧
            (H.2 = 0 → (liftInst S p Ac Cc H û).2 = 0) := by
  have hτpos : 0 < tau S := p6b63_tau_pos S
  obtain ⟨θ₀, c₃, C₃, hθ₀, hc₃, hC₃, h31⟩ := lemma_3_1_ii S p hS hp
  refine ⟨tau S + 3, by linarith, ?_⟩
  intro w ε Ac Cc hw hε hεd ⟨hpar1, hpar2, hpar3⟩
  have hp2 : 2 ≤ p := hp.1
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  let exp_θ : ℝ := (Ac : ℝ) - ((p : ℝ) - 1) * (Cc : ℝ)
  have hexp_θ_lt : exp_θ ≤ -1 := by dsimp [exp_θ]; linarith
  let exc : ℝ := ε * (1 + (p : ℝ) * (Cc : ℝ)) - (Ac : ℝ) - dExp p
  have hexc_gt1 : 1 < exc := by dsimp [exc]; linarith
  let γ : ℝ := (Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1) - w
  have hγ_gt : w + 4 < γ := by dsimp [γ]; linarith
  have hγ_pos : 0 < γ := by linarith
  let K0 : ℝ := 16 / c₃ ^ 2
  have hK0_pos : 0 < K0 := by positivity
  let n₀ : ℕ := max 2 (max (Nat.ceil (1 / θ₀) + 1) (max (Nat.ceil (2 / tau S) + 1) (Nat.ceil K0 + 1)))
  refine ⟨n₀, fun n H hn hSymm hdiag hwidth û hUhat => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn_ge_θ : 1 / θ₀ ≤ (n : ℝ) := by
    have hnat : Nat.ceil (1 / θ₀) + 1 ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have h1 : 1 / θ₀ ≤ (Nat.ceil (1 / θ₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (1 / θ₀) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil (1 / θ₀) ≤ n)
    linarith
  have hn_ge_τ : 2 / tau S ≤ (n : ℝ) := by
    have hnat : Nat.ceil (2 / tau S) + 1 ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
    have h1 : 2 / tau S ≤ (Nat.ceil (2 / tau S) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (2 / tau S) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil (2 / tau S) ≤ n)
    linarith
  have hn_ge_K0 : K0 ≤ (n : ℝ) := by
    have hnat : Nat.ceil K0 + 1 ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
    have h1 : K0 ≤ (Nat.ceil K0 : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil K0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil K0 ≤ n)
    linarith
  let r := cloudSize p Cc n
  have hr1 : 1 ≤ r := Nat.one_le_pow _ _ hn1
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  let θ : ℝ := ((thetaQ p Ac Cc n : ℚ) : ℝ)
  have hθ_rpow : θ = (n : ℝ) ^ exp_θ := by
    dsimp [θ, thetaQ, exp_θ]
    rw [Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    push_cast
    rfl
  have hθ_pos : 0 < θ := by rw [hθ_rpow]; exact Real.rpow_pos_of_pos hnpos _
  have hθ_le_inv : θ ≤ 1 / (n : ℝ) := by
    rw [hθ_rpow, show (1 / (n : ℝ)) = (n : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one, inv_eq_one_div]]
    exact Real.rpow_le_rpow_of_exponent_le hn_ge1 hexp_θ_lt
  have hθ_le_1 : θ ≤ 1 := hθ_le_inv.trans ((div_le_one hnpos).mpr hn_ge1)
  have hθ_le_θ₀ : θ ≤ θ₀ := by
    have h1 : 1 / (n : ℝ) ≤ θ₀ := (div_le_iff₀ hnpos).mpr (by
      have := mul_le_mul_of_nonneg_right hn_ge_θ hθ₀.le
      rw [one_div_mul_cancel hθ₀.ne', mul_comm] at this
      exact this)
    exact hθ_le_inv.trans h1
  obtain ⟨u, hu_prop, hu_uniq, hu_lo, _, _, _, _, _, _⟩ := h31 θ hθ_pos hθ_le_θ₀
  obtain ⟨u', hu'_pos, hu'_lt1, hu'_fp, _, hû_lo, hû_hi⟩ := hUhat
  have hu_eq : u' = u := hu_uniq u' hu'_pos hu'_lt1 hu'_fp
  subst hu_eq
  have hû_ge : (c₃ / 2) * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ (û : ℝ) := by
    have := hu_lo
    linarith
  have hû_pos : 0 < (û : ℝ) := lt_of_lt_of_le (by positivity) hû_ge
  have hû_lt2 : (û : ℝ) ≤ 2 := by linarith [hu'_lt1]
  have hû_neQ : û ≠ 0 := by exact_mod_cast hû_pos.ne'
  have hr_rpow : (r : ℝ) = (n : ℝ) ^ ((p : ℝ) * (Cc : ℝ)) := by
    dsimp [r, cloudSize]
    rw [Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_mul]
  have hr_θ_scale : (c₃ ^ 2 / 4) * ((n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1))) ≤
      (r : ℝ) * θ * (û : ℝ) ^ 2 := by
    have hû_sq : (c₃ ^ 2 / 4) * θ ^ (1 / ((p : ℝ) - 1)) ≤ (û : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (c₃ / 2) * θ ^ (1 / (2 * (p : ℝ) - 2)) := by positivity
      have hsq := pow_le_pow_left₀ hnonneg hû_ge 2
      have hexp2 : (θ ^ (1 / (2 * (p : ℝ) - 2))) ^ 2 = θ ^ (1 / ((p : ℝ) - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hθ_pos.le]
        congr 1
        field_simp [hp1_pos.ne']
        ring
      rw [mul_pow, hexp2] at hsq
      linarith [show (c₃ / 2) ^ 2 = c₃ ^ 2 / 4 by ring]
    have hpow_comb : (r : ℝ) * θ * θ ^ (1 / ((p : ℝ) - 1)) =
        (n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)) := by
      rw [hr_rpow, hθ_rpow, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      congr 1
      field_simp [hp1_pos.ne']
      ring
    calc (c₃ ^ 2 / 4) * ((n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)))
        = (r : ℝ) * θ * ((c₃ ^ 2 / 4) * θ ^ (1 / ((p : ℝ) - 1))) := by rw [← hpow_comb]; ring
      _ ≤ (r : ℝ) * θ * (û : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hû_sq (mul_nonneg hrpos.le hθ_pos.le)
  have hwidth_ratio : width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2) ≤ θ / 4 := by
    have hw_nn := p6b63_width_nonneg (castM H.1) (castV H.2)
    have hden_ge : 4 * (n : ℝ) ^ w ≤ (n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)) * (c₃ ^ 2 / 4) := by
      have hpow_ge : (n : ℝ) ^ (w + 1) ≤ (n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)) :=
        Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
      have hnK : 4 * (K0 / 4) ≤ (n : ℝ) := by
        dsimp [K0] at hn_ge_K0 ⊢
        linarith
      have h1 : (n : ℝ) ^ (w + 1) = (n : ℝ) * (n : ℝ) ^ w := by
        rw [Real.rpow_add hnpos, Real.rpow_one]; ring
      calc 4 * (n : ℝ) ^ w
          = (16 / c₃ ^ 2) * (c₃ ^ 2 / 4) * (n : ℝ) ^ w := by field_simp [hc₃.ne']; norm_num
        _ ≤ (n : ℝ) * (c₃ ^ 2 / 4) * (n : ℝ) ^ w :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn_ge_K0 (by positivity)) (by positivity)
        _ = (n : ℝ) ^ (w + 1) * (c₃ ^ 2 / 4) := by rw [h1]; ring
        _ ≤ (n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)) * (c₃ ^ 2 / 4) :=
            mul_le_mul_of_nonneg_right hpow_ge (by positivity)
    have hdiv_le : (n : ℝ) ^ w / ((r : ℝ) * θ * (û : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc (n : ℝ) ^ w = (1 / 4) * (4 * (n : ℝ) ^ w) := by ring
        _ ≤ (1 / 4) * ((n : ℝ) ^ ((Ac : ℝ) * (p : ℝ) / ((p : ℝ) - 1)) * (c₃ ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_left hden_ge (by norm_num)
        _ ≤ (1 / 4) * ((r : ℝ) * θ * (û : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith [hr_θ_scale]) (by norm_num)
    calc width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2)
        ≤ (n : ℝ) ^ w / ((r : ℝ) * (û : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hwidth (by positivity)
      _ = ((n : ℝ) ^ w / ((r : ℝ) * θ * (û : ℝ) ^ 2)) * θ := by
            field_simp [hrpos.ne', hθ_pos.ne', hû_pos.ne']
      _ ≤ (1 / 4) * θ := mul_le_mul_of_nonneg_right hdiv_le hθ_pos.le
      _ = θ / 4 := by ring
  have hwidth_ru : width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ)) ≤ θ / 2 := by
    have hw_nn := p6b63_width_nonneg (castM H.1) (castV H.2)
    calc width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ))
        = (width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2)) * (û : ℝ) := by
            field_simp [hrpos.ne', hû_pos.ne']
      _ ≤ (θ / 4) * 2 := mul_le_mul hwidth_ratio hû_lt2 hû_pos.le (by positivity)
      _ = θ / 2 := by ring
  have hnr_bound : 2 * θ ≤ tau S * ((n * r : ℕ) : ℝ) ^ (-dExp p + ε) := by
    have hnr_eq : ((n * r : ℕ) : ℝ) = (n : ℝ) ^ (1 + (p : ℝ) * (Cc : ℝ)) := by
      rw [Nat.cast_mul, hr_rpow, Real.rpow_add hnpos, Real.rpow_one]
    have hnr_rpow : ((n * r : ℕ) : ℝ) ^ (-dExp p + ε) = (n : ℝ) ^ (exp_θ + exc) := by
      rw [hnr_eq, ← Real.rpow_mul hnpos.le]
      congr 1
      dsimp [exp_θ, exc, dExp]
      field_simp [(by positivity : (p : ℝ) ≠ 0)]
      ring
    have hle_exp : (n : ℝ) * θ ≤ ((n * r : ℕ) : ℝ) ^ (-dExp p + ε) := by
      rw [hnr_rpow, hθ_rpow, Real.rpow_add hnpos]
      have hn_le_exc : (n : ℝ) ≤ (n : ℝ) ^ exc := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn_ge1 hexc_gt1.le
      calc (n : ℝ) * (n : ℝ) ^ exp_θ ≤ (n : ℝ) ^ exc * (n : ℝ) ^ exp_θ :=
            mul_le_mul_of_nonneg_right hn_le_exc (Real.rpow_pos_of_pos hnpos _).le
        _ = (n : ℝ) ^ exp_θ * (n : ℝ) ^ exc := by ring
    calc 2 * θ = tau S * ((2 / tau S) * θ) := by field_simp [hτpos.ne']
      _ ≤ tau S * ((n : ℝ) * θ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn_ge_τ hθ_pos.le) hτpos.le
      _ ≤ tau S * ((n * r : ℕ) : ℝ) ^ (-dExp p + ε) := mul_le_mul_of_nonneg_left hle_exp hτpos.le
  have hSymm_castM : (castM H.1).IsSymm := by
    ext i j
    dsimp [castM, Matrix.transpose_apply, Matrix.map_apply]
    exact congrArg (fun q : ℚ => (q : ℝ)) (congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i j) hSymm)
  have hSymm_liftJQ : (castM (liftJQ S p Ac Cc H û)).IsHermitian :=
    p6b63_liftJQ_isHermitian H hSymm û
  have hquad_pos : ∀ v : Fin n × Fin r → ℝ,
      0 ≤ ∑ a, ∑ b, v a * castM (liftJQ S p Ac Cc H û) a b * v b := by
    intro v
    rw [p6b63_liftJQ_quad hr1 H û hû_neQ v]
    let wv : Fin n → ℝ := fun i => ∑ α : Fin r, v (i, α)
    have hqb := p6b63_quad_bound (castM H.1) (castV H.2) hSymm_castM wv
    have hlower : -(width (castM H.1) (castV H.2) * ∑ i, wv i ^ 2) ≤
        ∑ i, ∑ j, castM H.1 i j * wv i * wv j := (abs_le.mp hqb).1
    have hdiv_le : width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2) * ∑ i, wv i ^ 2 ≤
        (θ / 4) * ∑ i, wv i ^ 2 :=
      mul_le_mul_of_nonneg_right hwidth_ratio (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hmain : 0 ≤ (tau S + θ) * ∑ i, wv i ^ 2 +
        (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j := by
      have h1 : -(width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2) * ∑ i, wv i ^ 2) ≤
          (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j := by
        have := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ 1 / ((r : ℝ) * (û : ℝ) ^ 2))
        linarith [show (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * -(width (castM H.1) (castV H.2) * ∑ i, wv i ^ 2) =
          -(width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2) * ∑ i, wv i ^ 2) by ring]
      have hsw_nn : 0 ≤ ∑ i, wv i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith [mul_nonneg (by linarith : 0 ≤ tau S + 3 * θ / 4) hsw_nn]
    exact mul_nonneg (by positivity) hmain
  have hpsd1_pre : (castM (liftJQ S p Ac Cc H û)).PosSemidef := by
    refine ⟨hSymm_liftJQ, fun x => ?_⟩
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simpa [star_trivial, Finsupp.sum_fintype, mul_assoc] using hquad_pos x
  have hpsd1 : (castM (liftInst S p Ac Cc H û).1).PosSemidef := by
    have heq : castM (liftInst S p Ac Cc H û).1 =
        (castM (liftJQ S p Ac Cc H û)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext a b
      rfl
    rw [heq]
    exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hpsd1_pre
  let upperScalar : ℝ := tau S * (1 + ((n * r : ℕ) : ℝ) ^ (-dExp p + ε))
  have hpsd2_pre :
      (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
        castM (liftJQ S p Ac Cc H û)).PosSemidef := by
    have hHerm : (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
        castM (liftJQ S p Ac Cc H û)).IsHermitian :=
      (Matrix.isHermitian_one.smul (star_trivial upperScalar : IsSelfAdjoint upperScalar)).sub hSymm_liftJQ
    refine ⟨hHerm, fun x => ?_⟩
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    have hquad_up : (∑ a, ∑ b, (x : Fin n × Fin r → ℝ) a * castM (liftJQ S p Ac Cc H û) a b * x b) ≤
        upperScalar * ∑ a, x a ^ 2 := by
      rw [p6b63_liftJQ_quad hr1 H û hû_neQ x]
      let wv : Fin n → ℝ := fun i => ∑ α : Fin r, x (i, α)
      have hqb := p6b63_quad_bound (castM H.1) (castV H.2) hSymm_castM wv
      have hupper := (abs_le.mp hqb).2
      have hsw_nn : 0 ≤ ∑ i, wv i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h1 : (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j ≤
          (θ / 4) * ∑ i, wv i ^ 2 := by
        calc (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j
            ≤ (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * (width (castM H.1) (castV H.2) * ∑ i, wv i ^ 2) :=
              mul_le_mul_of_nonneg_left hupper (by positivity)
          _ = (width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, wv i ^ 2 := by ring
          _ ≤ (θ / 4) * ∑ i, wv i ^ 2 := mul_le_mul_of_nonneg_right hwidth_ratio hsw_nn
      have h2 : (1 / (r : ℝ)) * ((tau S + θ) * ∑ i, wv i ^ 2 +
          (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j) ≤
          (tau S + 2 * θ) * ((1 / (r : ℝ)) * ∑ i, wv i ^ 2) := by
        have hsum_le : (tau S + θ) * ∑ i, wv i ^ 2 +
            (1 / ((r : ℝ) * (û : ℝ) ^ 2)) * ∑ i, ∑ j, castM H.1 i j * wv i * wv j ≤
            (tau S + 2 * θ) * ∑ i, wv i ^ 2 := by linarith [mul_nonneg hθ_pos.le hsw_nn]
        calc _ ≤ (1 / (r : ℝ)) * ((tau S + 2 * θ) * ∑ i, wv i ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = (tau S + 2 * θ) * ((1 / (r : ℝ)) * ∑ i, wv i ^ 2) := by ring
      have h3 : (1 / (r : ℝ)) * ∑ i, wv i ^ 2 ≤ ∑ a : Fin n × Fin r, x a ^ 2 := by
        have hsw := p6b63_sum_w_sq_le (r := r) (fun a => x a)
        calc (1 / (r : ℝ)) * ∑ i, wv i ^ 2
            ≤ (1 / (r : ℝ)) * ((r : ℝ) * ∑ a : Fin n × Fin r, x a ^ 2) :=
              mul_le_mul_of_nonneg_left hsw (by positivity)
          _ = ∑ a : Fin n × Fin r, x a ^ 2 := by field_simp [hrpos.ne']
      have h4 : tau S + 2 * θ ≤ upperScalar := by dsimp [upperScalar]; linarith [hnr_bound]
      have h5 : (tau S + 2 * θ) * ((1 / (r : ℝ)) * ∑ i, wv i ^ 2) ≤
          upperScalar * ∑ a : Fin n × Fin r, x a ^ 2 :=
        mul_le_mul h4 h3 (mul_nonneg (by positivity) hsw_nn) (by linarith)
      exact h2.trans h5
    have hid : (∑ a : Fin n × Fin r,
        x.sum fun b xb =>
          star (x a) * (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
            castM (liftJQ S p Ac Cc H û)) a b * xb) =
        upperScalar * ∑ a, x a ^ 2 -
          ∑ a, ∑ b, (x : Fin n × Fin r → ℝ) a * castM (liftJQ S p Ac Cc H û) a b * x b := by
      have hinner : ∀ a : Fin n × Fin r,
          (x.sum fun b xb =>
            star (x a) * (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
              castM (liftJQ S p Ac Cc H û)) a b * xb) =
            upperScalar * x a ^ 2 - ∑ b, (x : Fin n × Fin r → ℝ) a * castM (liftJQ S p Ac Cc H û) a b * x b := by
        intro a
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        have hterm : ∀ b : Fin n × Fin r,
            star (x a) * (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
              castM (liftJQ S p Ac Cc H û)) a b * x b =
              (if a = b then upperScalar * x a ^ 2 else 0) -
                x a * castM (liftJQ S p Ac Cc H û) a b * x b := by
          intro b
          simp only [star_trivial, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
          split_ifs with h
          · subst h; ring
          · ring
        simp_rw [hterm]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
      simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hid]
    linarith
  have hpsd2 :
      ((tau S * (1 + ((n * cloudSize p Cc n : ℕ) : ℝ) ^ (-dExp p + ε))) •
          (1 : Matrix (Fin (n * cloudSize p Cc n)) (Fin (n * cloudSize p Cc n)) ℝ) -
        castM (liftInst S p Ac Cc H û).1).PosSemidef := by
    have h1 : (tau S * (1 + ((n * cloudSize p Cc n : ℕ) : ℝ) ^ (-dExp p + ε))) •
          (1 : Matrix (Fin (n * cloudSize p Cc n)) (Fin (n * cloudSize p Cc n)) ℝ) =
        (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ)).submatrix
          finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply, smul_eq_mul,
        finProdFinEquiv.symm.apply_eq_iff_eq]
      rfl
    have h2 : castM (liftInst S p Ac Cc H û).1 =
        (castM (liftJQ S p Ac Cc H û)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext a b; rfl
    have hsub : (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ)).submatrix
          finProdFinEquiv.symm finProdFinEquiv.symm -
        (castM (liftJQ S p Ac Cc H û)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm =
        (upperScalar • (1 : Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ) -
          castM (liftJQ S p Ac Cc H û)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext a b; rfl
    rw [h1, h2, hsub]
    exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hpsd2_pre
  have hwidth_lift : width (castM (liftInst S p Ac Cc H û).1) (castV (liftInst S p Ac Cc H û).2) ≤ tau S + 3 := by
    unfold width
    have : Nonempty (Fin (n * cloudSize p Cc n)) := ⟨⟨0, Nat.mul_pos hn1 hr1⟩⟩
    apply ciSup_le
    intro a
    obtain ⟨i, α⟩ := finProdFinEquiv.symm a
    let p_pair := finProdFinEquiv.symm a
    have hvec : |castV (liftInst S p Ac Cc H û).2 a| ≤ θ / 2 := by
      have heq : castV (liftInst S p Ac Cc H û).2 a = castV H.2 p_pair.1 / ((r : ℝ) * (û : ℝ)) := by
        dsimp [p_pair, castV, liftInst, liftHQ, liftH, r]
        push_cast
        rfl
      rw [heq, abs_div, abs_of_pos (mul_pos hrpos hû_pos)]
      have h1 : |castV H.2 p_pair.1| ≤ width (castM H.1) (castV H.2) := by
        have hw := p6b63_row_abs_le_width (castM H.1) (castV H.2) p_pair.1
        linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (castM H.1 p_pair.1 j)]
      exact (div_le_div_of_nonneg_right h1 (mul_pos hrpos hû_pos).le).trans hwidth_ru
    have hrow : ∑ b : Fin (n * cloudSize p Cc n), |castM (liftInst S p Ac Cc H û).1 a b| ≤
        tau S + θ + θ / 4 := by
      have hsum_eq : ∑ b : Fin (n * cloudSize p Cc n), |castM (liftInst S p Ac Cc H û).1 a b| =
          ∑ c : Fin n × Fin r, |castM (liftJQ S p Ac Cc H û) p_pair c| := by
        refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun b => ?_
        rfl
      rw [hsum_eq, Fintype.sum_prod_type]
      have hentry : ∀ j : Fin n, ∀ γ : Fin r,
          |castM (liftJQ S p Ac Cc H û) p_pair (j, γ)| ≤
            ((if p_pair.1 = j then tau S + θ else 0) +
              |castM H.1 p_pair.1 j| / ((r : ℝ) * (û : ℝ) ^ 2)) / (r : ℝ) := by
        intro j γ
        have heq : castM (liftJQ S p Ac Cc H û) p_pair (j, γ) =
            ((if p_pair.1 = j then tau S + θ else 0) +
              castM H.1 p_pair.1 j / ((r : ℝ) * (û : ℝ) ^ 2)) * (1 / (r : ℝ)) := by
          dsimp [castM, liftJQ, liftJ, Matrix.map_apply, r, θ]
          split_ifs with h
          · push_cast [tau]; ring
          · push_cast; ring
        rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (r : ℝ)), mul_one_div]
        refine div_le_div_of_nonneg_right ?_ hrpos.le
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · split_ifs
          · rw [abs_of_pos (add_pos hτpos hθ_pos)]
          · simp
        · rw [abs_div, abs_of_pos (mul_pos hrpos (sq_pos_of_pos hû_pos))]
      calc ∑ j : Fin n, ∑ γ : Fin r, |castM (liftJQ S p Ac Cc H û) p_pair (j, γ)|
          ≤ ∑ j : Fin n, ∑ _γ : Fin r,
              ((if p_pair.1 = j then tau S + θ else 0) +
                |castM H.1 p_pair.1 j| / ((r : ℝ) * (û : ℝ) ^ 2)) / (r : ℝ) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun γ _ => hentry j γ
        _ = ∑ j : Fin n, ((if p_pair.1 = j then tau S + θ else 0) +
              |castM H.1 p_pair.1 j| / ((r : ℝ) * (û : ℝ) ^ 2)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp [hrpos.ne']
        _ = (∑ j : Fin n, if p_pair.1 = j then tau S + θ else 0) +
              (∑ j : Fin n, |castM H.1 p_pair.1 j|) / ((r : ℝ) * (û : ℝ) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_div]
        _ ≤ (tau S + θ) + width (castM H.1) (castV H.2) / ((r : ℝ) * (û : ℝ) ^ 2) := by
            refine add_le_add (by simp) (div_le_div_of_nonneg_right ?_ (by positivity))
            have hw := p6b63_row_abs_le_width (castM H.1) (castV H.2) p_pair.1
            linarith [abs_nonneg (castV H.2 p_pair.1)]
        _ ≤ tau S + θ + θ / 4 := by linarith [hwidth_ratio]
    linarith [hθ_le_1]
  refine ⟨hpsd1, hpsd2, hwidth_lift, ?_⟩
  intro hzero
  ext a
  simp [liftInst, liftHQ, liftH, hzero]

end CritWinSpin

open CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
        ∃ n₀ : ℕ, ∀ (n : ℕ) (H : Inst n), n₀ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          ∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
            (castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
            ((tau S * (1 + ((n * cloudSize p Cc n : ℕ) : ℝ) ^ (-dExp p + ε))) •
                (1 : Matrix (Fin (n * cloudSize p Cc n)) (Fin (n * cloudSize p Cc n)) ℝ) -
              castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
            width (castM (liftInst S p Ac Cc H û).1) (castV (liftInst S p Ac Cc H û).2) ≤ Cρ ∧
            (H.2 = 0 → (liftInst S p Ac Cc H û).2 = 0) :=
  p6b_6_3_lift_props S p hS hp
