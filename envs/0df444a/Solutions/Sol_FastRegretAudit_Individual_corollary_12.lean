-- Prove2me | solution 1 for FastRegretAudit.Individual.corollary_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T14:24:11.833201+00:00
-- url     : https://prove2.me/submissions/7f2bfeb0-a5ff-45e9-903f-beb86093cfd6

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Definitions.Def_FastRegretAudit_Individual_Runs
import Definitions.Def_FastRegretAudit_Individual_Geometry
import Definitions.Def_FastRegretAudit_Individual_Range

set_option autoImplicit false

namespace FRA30d86c63

open Finset RegLearnGames.TotalRegret FastRegretAudit.Individual

/-- dot product bounded by l1 norm times a sup bound -/
lemma dot_le_l1 {d : ℕ} (a b : Fin d → ℝ) (c : ℝ) (hb : ∀ x, |b x| ≤ c) :
    a ⬝ᵥ b ≤ l1 a * c := by
  unfold l1 dotProduct
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  calc a x * b x ≤ |a x * b x| := le_abs_self _
    _ = |a x| * |b x| := abs_mul _ _
    _ ≤ |a x| * c := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

lemma l1_nonneg {d : ℕ} (a : Fin d → ℝ) : 0 ≤ l1 a :=
  Finset.sum_nonneg (fun x _ => abs_nonneg (a x))

lemma l1_sub_comm {d : ℕ} (a b : Fin d → ℝ) : l1 (a - b) = l1 (b - a) := by
  unfold l1
  exact Finset.sum_congr rfl (fun x _ => by simp only [Pi.sub_apply]; exact abs_sub_comm _ _)

lemma l1_sub_mid {d : ℕ} (a b : Fin d → ℝ) :
    l1 (a - (1 / 2 : ℝ) • (a + b)) = l1 (a - b) / 2 := by
  unfold l1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [show a x - 1 / 2 * (a x + b x) = (a x - b x) / 2 by ring, abs_div]
  norm_num

lemma mid_mem {d : ℕ} {a b : Fin d → ℝ} (ha : a ∈ stdSimplex ℝ (Fin d))
    (hb : b ∈ stdSimplex ℝ (Fin d)) : (1 / 2 : ℝ) • (a + b) ∈ stdSimplex ℝ (Fin d) := by
  have h := (convex_stdSimplex ℝ (Fin d)) ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rwa [smul_add]

/-- Quadratic gap at a maximizer of a midpoint-strongly-concave objective. -/
lemma max_gap {d : ℕ} (R : (Fin d → ℝ) → ℝ) (hR : IsMidpointStronglyConvex l1 R)
    (η : ℝ) (hη : 0 < η) (L w : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ L - R v / η ≤ w ⬝ᵥ L - R w / η) :
    ∀ v ∈ stdSimplex ℝ (Fin d),
      l1 (w - v) ^ 2 / (2 * η) ≤ (w ⬝ᵥ L - R w / η) - (v ⬝ᵥ L - R v / η) := by
  -- P k : gap ≥ (1 - (1/2)^k) * l1^2/(2η)
  have key : ∀ k : ℕ, ∀ v ∈ stdSimplex ℝ (Fin d),
      (1 - (1 / 2 : ℝ) ^ k) * (l1 (w - v) ^ 2 / (2 * η)) ≤
        (w ⬝ᵥ L - R w / η) - (v ⬝ᵥ L - R v / η) := by
    intro k
    induction k with
    | zero =>
      intro v hv
      have := hopt v hv
      simp only [pow_zero, sub_self, zero_mul]
      linarith
    | succ k ih =>
      intro v hv
      set m : Fin d → ℝ := (1 / 2 : ℝ) • (w + v) with hm
      have hmS : m ∈ stdSimplex ℝ (Fin d) := mid_mem hw hv
      have h1 := ih m hmS
      have h2 : l1 (w - m) = l1 (w - v) / 2 := l1_sub_mid w v
      have h3 := hR w hw v hv
      have hdot : m ⬝ᵥ L = (w ⬝ᵥ L + v ⬝ᵥ L) / 2 := by
        rw [hm, smul_dotProduct, add_dotProduct, smul_eq_mul]; ring
      have h3' : R m / η ≤ (R w / η + R v / η) / 2 - l1 (w - v) ^ 2 / (8 * η) := by
        have := div_le_div_of_nonneg_right h3 hη.le
        calc R m / η ≤ ((R w + R v) / 2 - l1 (w - v) ^ 2 / 8) / η := this
          _ = (R w / η + R v / η) / 2 - l1 (w - v) ^ 2 / (8 * η) := by
            field_simp
      rw [h2] at h1
      rw [hdot] at h1
      have hp : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
      rw [hp]
      have e1 : (l1 (w - v) / 2) ^ 2 / (2 * η) = (l1 (w - v) ^ 2 / (2 * η)) / 4 := by
        field_simp; ring
      rw [e1] at h1
      have e2 : l1 (w - v) ^ 2 / (8 * η) = (l1 (w - v) ^ 2 / (2 * η)) / 4 := by
        field_simp; ring
      rw [e2] at h3'
      nlinarith
  intro v hv
  set A := l1 (w - v) ^ 2 / (2 * η) with hA
  set D := (w ⬝ᵥ L - R w / η) - (v ⬝ᵥ L - R v / η) with hD
  by_contra hcon
  rw [not_le] at hcon
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := by have := hopt v hv; linarith
  have hApos : 0 < A := lt_of_le_of_lt hD0 hcon
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (A - D) / A by
    apply div_pos <;> linarith) (by norm_num : (1 / 2 : ℝ) < 1)
  have := key k v hv
  rw [lt_div_iff₀ hApos] at hk
  nlinarith

/-- Stability of two maximizers whose linear terms differ by at most c. -/
lemma stab {d : ℕ} (R : (Fin d → ℝ) → ℝ) (hR : IsMidpointStronglyConvex l1 R)
    (η : ℝ) (hη : 0 < η) (L1 L2 w1 w2 : Fin d → ℝ)
    (hw1 : w1 ∈ stdSimplex ℝ (Fin d)) (hw2 : w2 ∈ stdSimplex ℝ (Fin d))
    (hopt1 : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ L1 - R v / η ≤ w1 ⬝ᵥ L1 - R w1 / η)
    (hopt2 : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ L2 - R v / η ≤ w2 ⬝ᵥ L2 - R w2 / η)
    (c : ℝ) (hc : 0 ≤ c) (hL : ∀ x, |L1 x - L2 x| ≤ c) :
    l1 (w1 - w2) ≤ η * c := by
  have g1 := max_gap R hR η hη L1 w1 hw1 hopt1 w2 hw2
  have g2 := max_gap R hR η hη L2 w2 hw2 hopt2 w1 hw1
  rw [l1_sub_comm w2 w1] at g2
  have hdot : (w1 - w2) ⬝ᵥ (L1 - L2) ≤ l1 (w1 - w2) * c :=
    dot_le_l1 _ _ c (fun x => by simpa only [Pi.sub_apply] using hL x)
  have expand : (w1 - w2) ⬝ᵥ (L1 - L2) =
      (w1 ⬝ᵥ L1 - w2 ⬝ᵥ L1) - (w1 ⬝ᵥ L2 - w2 ⬝ᵥ L2) := by
    simp only [sub_dotProduct, dotProduct_sub] <;> ring
  set x := l1 (w1 - w2) with hx
  have hx0 : 0 ≤ x := l1_nonneg _
  have hsum : x ^ 2 / η ≤ x * c := by
    have : x ^ 2 / η = x ^ 2 / (2 * η) + x ^ 2 / (2 * η) := by field_simp; ring
    rw [this]; linarith
  rw [div_le_iff₀ hη] at hsum
  by_cases h0 : x = 0
  · rw [h0]; positivity
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h0)
    nlinarith

/-- Regret of a finite-horizon OFTRL run against a fixed comparator. -/
lemma oftrl_regret {d : ℕ} (R : (Fin d → ℝ) → ℝ) (hR : IsMidpointStronglyConvex l1 R)
    (η : ℝ) (hη : 0 < η) (M U w : ℕ → Fin d → ℝ) (T : ℕ)
    (hw : IsOFTRLThrough R η M U w T) (a : ℝ)
    (ha : ∀ t, 1 ≤ t → t ≤ T → ∀ x, |U t x - M t x| ≤ a)
    (wstar : Fin d → ℝ) (hws : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ U t ≤
      (R wstar - R (w 0)) / η + T * (η / 2 * a ^ 2) := by
  obtain ⟨⟨hw0, hmin⟩, hstep⟩ := hw
  -- Q t : ∀ v, v ⬝ S (t+1) - R v/η ≤ -R(w0)/η + Σ_{Icc 1 t} w_k ⬝ U_k + t * (η/2 a^2)
  have Q : ∀ t, t ≤ T → ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ (∑ k ∈ Finset.Ico 1 (t + 1), U k) - R v / η ≤
        - R (w 0) / η + ∑ k ∈ Finset.Icc 1 t, w k ⬝ᵥ U k + t * (η / 2 * a ^ 2) := by
    intro t
    induction t with
    | zero =>
      intro _ v hv
      have := hmin v hv
      simp only [zero_add, Finset.Ico_self, Finset.sum_empty, dotProduct_zero,
        Finset.Icc_self, Nat.cast_zero, zero_mul, add_zero]
      have hb : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
      rw [hb, Finset.sum_empty, add_zero, zero_sub]
      have h2 := div_le_div_of_nonneg_right this hη.le
      have h3 : -R (w 0) / η = -(R (w 0) / η) := neg_div _ _
      linarith
    | succ t ih =>
      intro htT v hv
      have ht1 : 1 ≤ t + 1 := by omega
      obtain ⟨hwt, hopt⟩ := hstep (t + 1) ht1 htT
      set L : Fin d → ℝ := (∑ k ∈ Finset.Ico 1 (t + 1), U k) + M (t + 1) with hL
      have gap := max_gap R hR η hη L (w (t + 1)) hwt hopt v hv
      have IH := ih (by omega) (w (t + 1)) hwt
      have hS : ∑ k ∈ Finset.Ico 1 (t + 1 + 1), U k =
          (∑ k ∈ Finset.Ico 1 (t + 1), U k) + U (t + 1) := Finset.sum_Ico_succ_top ht1 _
      have hI : ∑ k ∈ Finset.Icc 1 (t + 1), w k ⬝ᵥ U k =
          (∑ k ∈ Finset.Icc 1 t, w k ⬝ᵥ U k) + w (t + 1) ⬝ᵥ U (t + 1) := by
        rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top ht1]
      rw [hS, hI]
      -- δ = U(t+1) - M(t+1)
      have hδ : (v - w (t + 1)) ⬝ᵥ (U (t + 1) - M (t + 1)) ≤ l1 (v - w (t + 1)) * a :=
        dot_le_l1 _ _ a (fun x => by simpa only [Pi.sub_apply] using ha (t + 1) ht1 htT x)
      rw [l1_sub_comm] at hδ
      set y := l1 (w (t + 1) - v) with hy
      have hquad : y * a - y ^ 2 / (2 * η) ≤ η / 2 * a ^ 2 := by
        have h0 : 0 ≤ (y - η * a) ^ 2 / (2 * η) := by positivity
        have : (y - η * a) ^ 2 / (2 * η) = η / 2 * a ^ 2 - (y * a - y ^ 2 / (2 * η)) := by
          field_simp; ring
        linarith
      have e1 : v ⬝ᵥ ((∑ k ∈ Finset.Ico 1 (t + 1), U k) + U (t + 1)) =
          v ⬝ᵥ L + (v - w (t + 1)) ⬝ᵥ (U (t + 1) - M (t + 1)) +
            w (t + 1) ⬝ᵥ (U (t + 1) - M (t + 1)) := by
        rw [hL]; simp only [dotProduct_add, dotProduct_sub, sub_dotProduct]; ring
      have e2 : w (t + 1) ⬝ᵥ L =
          w (t + 1) ⬝ᵥ (∑ k ∈ Finset.Ico 1 (t + 1), U k) + w (t + 1) ⬝ᵥ M (t + 1) := by
        rw [hL, dotProduct_add]
      have e3 : w (t + 1) ⬝ᵥ (U (t + 1) - M (t + 1)) =
          w (t + 1) ⬝ᵥ U (t + 1) - w (t + 1) ⬝ᵥ M (t + 1) := dotProduct_sub _ _ _
      rw [e1]
      push_cast
      nlinarith
  have hT := Q T le_rfl wstar hws
  have hsplit : ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ U t =
      wstar ⬝ᵥ (∑ k ∈ Finset.Ico 1 (T + 1), U k) - ∑ t ∈ Finset.Icc 1 T, w t ⬝ᵥ U t := by
    rw [Finset.Ico_add_one_right_eq_Icc, dotProduct_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun t _ => sub_dotProduct _ _ _)
  rw [hsplit]
  have : (R wstar - R (w 0)) / η = R wstar / η - R (w 0) / η := sub_div _ _ _
  rw [this]
  have h3 : -R (w 0) / η = -(R (w 0) / η) := neg_div _ _
  linarith

lemma simplex_sum_one {d : ℕ} {a : Fin d → ℝ} (ha : a ∈ stdSimplex ℝ (Fin d)) :
    ∑ x, a x = 1 := ha.2

lemma simplex_nonneg {d : ℕ} {a : Fin d → ℝ} (ha : a ∈ stdSimplex ℝ (Fin d)) (x : Fin d) :
    0 ≤ a x := ha.1 x

/-- Hybrid argument: expectations under two product distributions differ by at most the
sum of coordinatewise l1 distances (for |f| ≤ 1). -/
lemma hybrid {n d : ℕ} (σ τ : Fin n → Fin d → ℝ)
    (hσ : ∀ j, σ j ∈ stdSimplex ℝ (Fin d)) (hτ : ∀ j, τ j ∈ stdSimplex ℝ (Fin d))
    (f : (Fin n → Fin d) → ℝ) (hf : ∀ s, |f s| ≤ 1) :
    |∑ s : Fin n → Fin d, (∏ j, σ j (s j)) * f s -
        ∑ s : Fin n → Fin d, (∏ j, τ j (s j)) * f s| ≤ ∑ j, l1 (σ j - τ j) := by
  classical
  let h : ℕ → Fin n → Fin d → ℝ := fun k j => if (j : ℕ) < k then τ j else σ j
  have hmem : ∀ k j, h k j ∈ stdSimplex ℝ (Fin d) := by
    intro k j; simp only [h]; split_ifs
    · exact hτ j
    · exact hσ j
  let E : ℕ → ℝ := fun k => ∑ s : Fin n → Fin d, (∏ j, h k j (s j)) * f s
  have hE0 : E 0 = ∑ s : Fin n → Fin d, (∏ j, σ j (s j)) * f s := by
    simp only [E, h, Nat.not_lt_zero, if_false]
  have hEn : E n = ∑ s : Fin n → Fin d, (∏ j, τ j (s j)) * f s := by
    simp only [E, h, Fin.is_lt, if_true]
  rw [← hE0, ← hEn, ← Finset.sum_range_sub' E n]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have step : ∀ k (hk : k < n), |E k - E (k + 1)| ≤ l1 (σ ⟨k, hk⟩ - τ ⟨k, hk⟩) := by
    intro k hk
    set jk : Fin n := ⟨k, hk⟩ with hjk
    have hjmem : jk ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hoff : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase jk, h (k + 1) j = h k j := by
      intro j hj
      have hne : (j : ℕ) ≠ k := by
        intro he; apply (Finset.mem_erase.mp hj).1; exact Fin.ext he
      simp only [h]
      have : ((j : ℕ) < k + 1) ↔ ((j : ℕ) < k) := by omega
      simp only [this]
    have hk1 : h k jk = σ jk := by simp [h, hjk]
    have hk2 : h (k + 1) jk = τ jk := by simp [h, hjk]
    let P : (Fin n → Fin d) → ℝ := fun s => ∏ j ∈ (Finset.univ : Finset (Fin n)).erase jk, h k j (s j)
    have hP0 : ∀ s, 0 ≤ P s := fun s =>
      Finset.prod_nonneg (fun j _ => simplex_nonneg (hmem k j) _)
    have hdiff : ∀ s : Fin n → Fin d, (∏ j, h k j (s j)) - (∏ j, h (k + 1) j (s j)) =
        (σ jk (s jk) - τ jk (s jk)) * P s := by
      intro s
      rw [← Finset.mul_prod_erase _ (fun j => h k j (s j)) hjmem,
        ← Finset.mul_prod_erase _ (fun j => h (k + 1) j (s j)) hjmem]
      have : ∏ j ∈ (Finset.univ : Finset (Fin n)).erase jk, h (k + 1) j (s j) = P s :=
        Finset.prod_congr rfl (fun j hj => by rw [hoff j hj])
      rw [this, hk1, hk2]; ring
    have hEd : E k - E (k + 1) =
        ∑ s : Fin n → Fin d, ((σ jk (s jk) - τ jk (s jk)) * P s) * f s := by
      simp only [E]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s _ => by rw [← sub_mul, hdiff s])
    rw [hEd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hpt : ∀ s : Fin n → Fin d, |((σ jk (s jk) - τ jk (s jk)) * P s) * f s| ≤
        |σ jk (s jk) - τ jk (s jk)| * P s := by
      intro s
      rw [abs_mul, abs_mul, abs_of_nonneg (hP0 s)]
      have := hf s
      have h0 : 0 ≤ |σ jk (s jk) - τ jk (s jk)| * P s := mul_nonneg (abs_nonneg _) (hP0 s)
      nlinarith
    refine le_trans (Finset.sum_le_sum (fun s _ => hpt s)) ?_
    -- factorize
    let g : Fin n → Fin d → ℝ := fun j => if j = jk then (fun x => |σ jk x - τ jk x|) else h k j
    have hg : ∀ s : Fin n → Fin d, |σ jk (s jk) - τ jk (s jk)| * P s = ∏ j, g j (s j) := by
      intro s
      rw [← Finset.mul_prod_erase _ (fun j => g j (s j)) hjmem]
      congr 1
      · simp [g]
      · exact Finset.prod_congr rfl (fun j hj => by
          simp [g, (Finset.mem_erase.mp hj).1])
    rw [Finset.sum_congr rfl (fun s _ => hg s)]
    rw [← Fintype.prod_sum]
    rw [← Finset.mul_prod_erase _ (fun j => ∑ x, g j x) hjmem]
    have hrest : ∏ j ∈ (Finset.univ : Finset (Fin n)).erase jk, ∑ x, g j x = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp only [g, (Finset.mem_erase.mp hj).1, if_false]
      exact simplex_sum_one (hmem k j)
    rw [hrest, mul_one]
    simp [g, l1]
  calc ∑ k ∈ Finset.range n, |E k - E (k + 1)|
      ≤ ∑ k ∈ Finset.range n, (if hk : k < n then l1 (σ ⟨k, hk⟩ - τ ⟨k, hk⟩) else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        rw [dif_pos hk']
        exact step k hk'
    _ = ∑ j : Fin n, l1 (σ j - τ j) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => if hk : k < n then l1 (σ ⟨k, hk⟩ - τ ⟨k, hk⟩) else 0) n]
        exact Finset.sum_congr rfl (fun j _ => by simp [j.is_lt])

lemma profile_mem {n d : ℕ} (w : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (i : Fin n) (x : Fin d) :
    ∀ j, Function.update w i (Pi.single x 1) j ∈ stdSimplex ℝ (Fin d) := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact single_mem_stdSimplex ℝ x
  · rw [Function.update_of_ne hj]; exact hw j

lemma util_mem {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1) (w : Fin n → Fin d → ℝ)
    (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) (x : Fin d) :
    0 ≤ utilVec u w i x ∧ utilVec u w i x ≤ 1 := by
  classical
  have hσ := profile_mem w hw i x
  set σ := Function.update w i (Pi.single x 1) with hσdef
  have hval : utilVec u w i x = ∑ s : Fin n → Fin d, (∏ j, σ j (s j)) * u i s := rfl
  rw [hval]
  have hpn : ∀ s : Fin n → Fin d, 0 ≤ ∏ j, σ j (s j) := fun s =>
    Finset.prod_nonneg (fun j _ => simplex_nonneg (hσ j) _)
  have htot : ∑ s : Fin n → Fin d, (∏ j, σ j (s j)) = 1 := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun j _ => simplex_sum_one (hσ j))
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hpn s) (hu i s).1)
  · calc ∑ s : Fin n → Fin d, (∏ j, σ j (s j)) * u i s
        ≤ ∑ s : Fin n → Fin d, (∏ j, σ j (s j)) :=
          Finset.sum_le_sum (fun s _ => by
            have := (hu i s).2; have := hpn s; nlinarith)
      _ = 1 := htot

lemma util_lip {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1) (w w' : Fin n → Fin d → ℝ)
    (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d)) (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d))
    (i : Fin n) (x : Fin d) :
    |utilVec u w i x - utilVec u w' i x| ≤
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, l1 (w j - w' j) := by
  classical
  have hval : ∀ v : Fin n → Fin d → ℝ, utilVec u v i x =
      ∑ s : Fin n → Fin d, (∏ j, Function.update v i (Pi.single x 1) j (s j)) * u i s :=
    fun v => rfl
  rw [hval, hval]
  refine le_trans (hybrid _ _ (profile_mem w hw i x) (profile_mem w' hw' i x) (u i)
    (fun s => by rw [abs_of_nonneg (hu i s).1]; exact (hu i s).2)) (le_of_eq ?_)
  rw [← Finset.sum_erase (Finset.univ : Finset (Fin n))
    (show l1 (Function.update w i (Pi.single x 1) i - Function.update w' i (Pi.single x 1) i) = 0 by
      simp [l1])]
  exact Finset.sum_congr rfl (fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1,
      Function.update_of_ne (Finset.mem_erase.mp hj).1])

lemma arith (ρ A B η N Tr : ℝ) (hA : 0 < A) (hB : 0 < B) (hN : N = A ^ 2) (hT : Tr = B ^ 4)
    (hη : η = A⁻¹ * B⁻¹) :
    ρ / η + Tr * (η / 2 * (N * (η * 2)) ^ 2) = (ρ + 2) * (A * B) := by
  subst hN hT hη
  field_simp

theorem main {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ)
    (h𝓡 : ∀ i, IsMidpointStronglyConvex RegLearnGames.TotalRegret.l1 (𝓡 i))
    (T : ℕ) (hT : 1 ≤ T) (w : ℕ → Fin n → Fin d → ℝ)
    (hw : IsGameOFTRLThrough u 𝓡 (corollaryStepsize n T) w T) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ((∑ t ∈ Finset.Icc 1 T,
        (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i : ℝ) : EReal) ≤
        (commonRange 𝓡 + 4) *
          ((Real.sqrt ((n : ℝ) - 1) * Real.rpow (T : ℝ) (1 / 4 : ℝ) : ℝ) : EReal) := by
  intro i wstar hws
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hApos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hBpos : 0 < Real.rpow (T : ℝ) (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hA2 : (n : ℝ) - 1 = Real.sqrt ((n : ℝ) - 1) ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hB4 : (T : ℝ) = Real.rpow (T : ℝ) (1 / 4 : ℝ) ^ 4 := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hηeq : corollaryStepsize n T =
      (Real.sqrt ((n : ℝ) - 1))⁻¹ * (Real.rpow (T : ℝ) (1 / 4 : ℝ))⁻¹ := by
    unfold corollaryStepsize
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_neg (by linarith),
      Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]
  set η := corollaryStepsize n T with hηdef
  have hηpos : 0 < η := by rw [hηeq]; positivity
  have hS : ∀ t, t ≤ T → ∀ j, w t j ∈ stdSimplex ℝ (Fin d) := by
    intro t ht j
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; exact (hw j).1.1
    · exact ((hw j).2 t hpos ht).1
  have hclean : ∀ j t, 1 ≤ t → t ≤ T → w t j ∈ stdSimplex ℝ (Fin d) ∧
      ∀ v ∈ stdSimplex ℝ (Fin d),
        v ⬝ᵥ ((∑ k ∈ Finset.Ico 1 t, utilVec u (w k) j) + utilVec u (w (t - 1)) j) - 𝓡 j v / η ≤
          w t j ⬝ᵥ ((∑ k ∈ Finset.Ico 1 t, utilVec u (w k) j) + utilVec u (w (t - 1)) j) -
            𝓡 j (w t j) / η :=
    fun j t h1 h2 => (hw j).2 t h1 h2
  have hU : ∀ k, k ≤ T → ∀ j x, 0 ≤ utilVec u (w k) j x ∧ utilVec u (w k) j x ≤ 1 :=
    fun k hk j x => util_mem u hu (w k) (hS k hk) j x
  have hstab : ∀ t, 1 ≤ t → t ≤ T → ∀ j, l1 (w t j - w (t - 1) j) ≤ η * 2 := by
    intro t ht1 htT j
    have hw0 : w 0 j ∈ stdSimplex ℝ (Fin d) := (hw j).1.1
    have hmin : ∀ v ∈ stdSimplex ℝ (Fin d), 𝓡 j (w 0 j) ≤ 𝓡 j v := (hw j).1.2
    rcases Nat.lt_or_ge t 2 with hlt | hge
    · have h1 : t = 1 := by omega
      subst h1
      obtain ⟨hw1, hopt1⟩ := hclean j 1 le_rfl htT
      have hopt0 : ∀ v ∈ stdSimplex ℝ (Fin d),
          v ⬝ᵥ (0 : Fin d → ℝ) - 𝓡 j v / η ≤ w 0 j ⬝ᵥ (0 : Fin d → ℝ) - 𝓡 j (w 0 j) / η := by
        intro v hv
        simp only [dotProduct_zero, zero_sub]
        have := div_le_div_of_nonneg_right (hmin v hv) hηpos.le
        linarith
      refine stab (𝓡 j) (h𝓡 j) η hηpos _ (0 : Fin d → ℝ) (w 1 j) (w 0 j) hw1 hw0 hopt1 hopt0
        2 (by norm_num) ?_
      intro x
      have h := hU 0 (Nat.zero_le _) j x
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add, Pi.zero_apply, sub_zero,
        Nat.sub_self]
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
      obtain ⟨hwa, hopta⟩ := hclean j (s + 2) (by omega) htT
      obtain ⟨hwb, hoptb⟩ := hclean j (s + 1) (by omega) (by omega)
      have e1 : s + 2 - 1 = s + 1 := by omega
      have e2 : s + 1 - 1 = s := by omega
      have e3 : ∑ k ∈ Finset.Ico 1 (s + 2), utilVec u (w k) j =
          (∑ k ∈ Finset.Ico 1 (s + 1), utilVec u (w k) j) + utilVec u (w (s + 1)) j :=
        Finset.sum_Ico_succ_top (by omega : 1 ≤ s + 1) _
      rw [e1, e3] at hopta
      rw [e2] at hoptb
      rw [e1]
      refine stab (𝓡 j) (h𝓡 j) η hηpos _ _ (w (s + 2) j) (w (s + 1) j) hwa hwb hopta hoptb
        2 (by norm_num) ?_
      intro x
      have ha := hU (s + 1) (by omega) j x
      have hb := hU s (by omega) j x
      simp only [Pi.add_apply]
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hvar : ∀ t, 1 ≤ t → t ≤ T → ∀ x,
      |utilVec u (w t) i x - utilVec u (w (t - 1)) i x| ≤ ((n : ℝ) - 1) * (η * 2) := by
    intro t h1 h2 x
    refine le_trans (util_lip u hu (w t) (w (t - 1)) (hS t h2) (hS (t - 1) (by omega)) i x) ?_
    calc ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, l1 (w t j - w (t - 1) j)
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, η * 2 :=
          Finset.sum_le_sum (fun j _ => hstab t h1 h2 j)
      _ = ((n : ℝ) - 1) * (η * 2) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hreg : ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ utilVec u (w t) i ≤
      (𝓡 i wstar - 𝓡 i (w 0 i)) / η + T * (η / 2 * (((n : ℝ) - 1) * (η * 2)) ^ 2) :=
    oftrl_regret (𝓡 i) (h𝓡 i) η hηpos (fun t => utilVec u (w (t - 1)) i)
      (fun t => utilVec u (w t) i) (fun t => w t i) T (hw i) _ hvar wstar hws
  rw [arith _ _ _ η _ _ hApos hBpos hA2 hB4 hηeq] at hreg
  set ρ := 𝓡 i wstar - 𝓡 i (w 0 i) with hρ
  set X := Real.sqrt ((n : ℝ) - 1) * Real.rpow (T : ℝ) (1 / 4 : ℝ) with hX
  have hXpos : 0 < X := mul_pos hApos hBpos
  have hw0i : w 0 i ∈ stdSimplex ℝ (Fin d) := (hw i).1.1
  have hρC : ((ρ : ℝ) : EReal) ≤ commonRange 𝓡 := by
    calc ((ρ : ℝ) : EReal) = (𝓡 i wstar : EReal) - (𝓡 i (w 0 i) : EReal) := EReal.coe_sub _ _
      _ ≤ regularizerRange (𝓡 i) := by
          unfold regularizerRange
          exact EReal.sub_le_sub (le_sSup (Set.mem_image_of_mem _ hws))
            (sInf_le (Set.mem_image_of_mem _ hw0i))
      _ ≤ commonRange 𝓡 := le_iSup (fun j => regularizerRange (𝓡 j)) i
  have h4 : ((4 : ℝ) : EReal) = 4 := by norm_cast
  generalize commonRange 𝓡 = C at hρC ⊢
  cases C using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp hρC) (EReal.coe_ne_bot _)
  | top =>
      rw [← h4, EReal.top_add_coe, EReal.top_mul_coe_of_pos hXpos]
      exact le_top
  | coe c =>
      have hc : ρ ≤ c := EReal.coe_le_coe_iff.mp hρC
      rw [← h4, ← EReal.coe_add, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.mpr ?_
      have : 0 ≤ (c - ρ + 2) * X := mul_nonneg (by linarith) hXpos.le
      nlinarith

end FRA30d86c63

open FastRegretAudit.Individual in
theorem solution {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ)
    (h𝓡 : ∀ i, IsMidpointStronglyConvex RegLearnGames.TotalRegret.l1 (𝓡 i))
    (T : ℕ) (hT : 1 ≤ T) (w : ℕ → Fin n → Fin d → ℝ)
    (hw : IsGameOFTRLThrough u 𝓡 (corollaryStepsize n T) w T) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ((∑ t ∈ Finset.Icc 1 T,
        (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i : ℝ) : EReal) ≤
        (commonRange 𝓡 + 4) *
          ((Real.sqrt ((n : ℝ) - 1) * Real.rpow (T : ℝ) (1 / 4 : ℝ) : ℝ) : EReal) := by
  exact FRA30d86c63.main hn hd u hu 𝓡 h𝓡 T hT w hw
