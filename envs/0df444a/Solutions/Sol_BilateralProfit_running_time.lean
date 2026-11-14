-- Prove2me | solution 1 for BilateralProfit.running_time
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:48:36.180567+00:00
-- url     : https://prove2.me/submissions/00aa144f-e981-4aee-accc-f452e6142786

import Definitions.Def_BilateralProfit_Algorithm1
import Mathlib

namespace BilateralProfit.RuntimeSubmission

open CapacitatedAssort.General (Work charge)

def CostLE {α : Type} (m : StateM ℕ α) (c : ℕ) : Prop :=
  ∀ s, (m.run s).2 ≤ s + c

lemma costLE_pure {α : Type} (a : α) : CostLE (pure a) 0 := by
  intro s
  exact Nat.le_refl _

lemma costLE_charge (k : ℕ) : CostLE (charge k) k := by
  intro s
  exact Nat.le_refl _

lemma costLE_mono {α : Type} {m : StateM ℕ α} {c d : ℕ}
    (h : CostLE m c) (hcd : c ≤ d) : CostLE m d := by
  intro s
  exact (h s).trans (Nat.add_le_add_left hcd s)

lemma costLE_bind {α β : Type} {m : StateM ℕ α} {f : α → StateM ℕ β}
    {c d : ℕ} (hm : CostLE m c) (hf : ∀ a, CostLE (f a) d) :
    CostLE (m >>= f) (c + d) := by
  intro s
  change (f (m.run s).1 |>.run (m.run s).2).2 ≤ s + (c + d)
  exact (hf _ _).trans (by have := hm s; omega)

lemma costLE_forIn {α β : Type} (l : List α)
    (f : α → β → StateM ℕ (ForInStep β)) (B : ℕ)
    (hf : ∀ x b, CostLE (f x b) B) (b : β) :
    CostLE (forIn l b f) (l.length * B) := by
  induction l generalizing b with
  | nil =>
    simpa using costLE_pure b
  | cons x xs ih =>
    intro s
    have hstep := hf x b s
    rcases heq : (f x b).run s with ⟨z, s'⟩
    change f x b s = (z, s') at heq
    change (f x b s).2 ≤ s + B at hstep
    rw [heq] at hstep
    cases z with
    | done b' =>
      simpa only [List.forIn_cons, StateT.bind, StateT.pure, StateT.run, heq,
        List.length_cons, Id.run, pure, bind, Nat.succ_mul] using
        (show s' ≤ s + (xs.length + 1) * B by dsimp at hstep; simp only [Nat.add_mul, Nat.one_mul]; omega)
    | yield b' =>
      have htail := ih b' s'
      change (forIn xs b' f |>.run s').2 ≤ s' + xs.length * B at htail
      have htotal : (forIn xs b' f |>.run s').2 ≤ s + (xs.length + 1) * B := by
        dsimp at hstep
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [List.forIn_cons, StateT.bind, StateT.pure, StateT.run, heq,
        List.length_cons, Id.run, pure, bind] using htotal

end BilateralProfit.RuntimeSubmission

namespace BilateralProfit.RuntimeSubmission

lemma nA_pos (K : ℕ) : 0 < nA K := by
  unfold nA
  exact_mod_cast Fintype.card_pos

lemma nA_one_le (K : ℕ) : 1 ≤ nA K := by
  unfold nA
  exact_mod_cast Fintype.card_pos

lemma nG_eq (K : ℕ) : nG K = ((K : ℝ) + 1) ^ 2 := by
  simp [nG, Grid, Fintype.card_prod, pow_two, Nat.cast_add, Nat.cast_mul]

lemma nA_le_nG (K : ℕ) : nA K ≤ nG K := by
  unfold nA nG
  exact_mod_cast Fintype.card_subtype_le (fun x : Grid K => x.1 ≤ x.2)

lemma nG_one_le (K : ℕ) : 1 ≤ nG K := by
  rw [nG_eq]
  nlinarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K]

lemma nG_le (K : ℕ) (hK : 1 ≤ K) : nG K ≤ 4 * (K : ℝ) ^ 2 := by
  rw [nG_eq]
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith

lemma nA_le (K : ℕ) (hK : 1 ≤ K) : nA K ≤ 4 * (K : ℝ) ^ 2 :=
  (nA_le_nG K).trans (nG_le K hK)

lemma logScale_one_le (K : ℕ) : 1 ≤ 1 + Real.log K := by
  linarith [Real.log_natCast_nonneg K]

lemma logScale_le (K : ℕ) (hK : 1 ≤ K) : 1 + Real.log K ≤ K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  linarith [Real.log_le_sub_one_of_pos hk]

lemma log_eight_le : Real.log 8 ≤ 3 := by
  have h : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  linarith

lemma log_sixteen_le : Real.log 16 ≤ 4 := by
  have h : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  linarith

lemma beta_le (K : ℕ) : beta K ≤ (K : ℝ)^2 * (1 + Real.log K)^6 := by
  unfold beta
  gcongr
  linarith

lemma Hpar_nonneg (K : ℕ) : 0 ≤ Hpar K := by
  have hb : 0 ≤ beta K := by unfold beta; positivity
  have hn := nA_one_le K
  have hprod : 1 ≤ nA K * (1 + beta K * K) := by
    nlinarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K, mul_nonneg hb (show (0 : ℝ) ≤ K from Nat.cast_nonneg K)]
  have hl := Real.log_nonneg hprod
  unfold Hpar
  positivity

lemma log_posterior_scale_le (K : ℕ) (hK : 1 ≤ K) :
    Real.log (nA K * (1 + beta K * K)) ≤ 14 * (1 + Real.log K) := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := by positivity
  have hL0 : 0 ≤ 1 + Real.log K := by linarith [logScale_one_le K]
  have hL6 : (1 + Real.log K)^6 ≤ (K : ℝ)^6 := by
    gcongr
    exact logScale_le K hK
  have hb : beta K * K ≤ (K : ℝ)^9 := by
    calc
      beta K * K ≤ ((K : ℝ)^2 * (1 + Real.log K)^6) * K := by
        gcongr; exact beta_le K
      _ ≤ ((K : ℝ)^2 * (K : ℝ)^6) * K := by gcongr
      _ = (K : ℝ)^9 := by ring
  have hk9 : (1 : ℝ) ≤ (K : ℝ)^9 := one_le_pow₀ hk
  have hinside : nA K * (1 + beta K * K) ≤ 8 * (K : ℝ)^11 := by
    calc
      _ ≤ (4 * (K : ℝ)^2) * (1 + (K : ℝ)^9) := by
        exact mul_le_mul (nA_le K hK) (by linarith [hb])
          (by unfold beta; positivity) (by positivity)
      _ ≤ (4 * (K : ℝ)^2) * (2 * (K : ℝ)^9) := by gcongr; linarith
      _ = _ := by ring
  have hpos : 0 < nA K * (1 + beta K * K) := by
    have := nA_pos K
    unfold beta
    positivity
  have hlog := Real.log_le_log hpos hinside
  have heq : Real.log (8 * (K : ℝ)^11) = Real.log 8 + 11 * Real.log K := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hk0.ne'), Real.log_pow]
    norm_num
  rw [heq] at hlog
  linarith [log_eight_le, Real.log_natCast_nonneg K]

lemma Hpar_le (K : ℕ) (hK : 1 ≤ K) :
    Hpar K ≤ 15 * (K : ℝ)^2 * (1 + Real.log K)^7 := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL := logScale_one_le K
  have hbase : 1 ≤ (K : ℝ)^2 * (1 + Real.log K)^7 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hL)
  have hb : 0 ≤ beta K := by unfold beta; positivity
  have hlog := log_posterior_scale_le K hK
  have hmul := mul_le_mul_of_nonneg_left hlog hb
  have hmul' : beta K * (14 * (1 + Real.log K)) ≤
      14 * (K : ℝ)^2 * (1 + Real.log K)^7 := by
    calc
      _ ≤ ((K : ℝ)^2 * (1 + Real.log K)^6) * (14 * (1 + Real.log K)) := by
        gcongr; exact beta_le K
      _ = _ := by ring
  unfold Hpar
  nlinarith

lemma log_card_product_le (K : ℕ) (hK : 1 ≤ K) :
    Real.log (nA K * nG K) ≤ 4 * (1 + Real.log K) := by
  have hk0 : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hprod : nA K * nG K ≤ 16 * (K : ℝ)^4 := by
    calc
      _ ≤ (4 * (K : ℝ)^2) * (4 * (K : ℝ)^2) := by
        exact mul_le_mul (nA_le K hK) (nG_le K hK)
          (le_trans zero_le_one (nG_one_le K)) (by positivity)
      _ = _ := by ring
  have hp : 0 < nA K * nG K :=
    mul_pos (nA_pos K) (lt_of_lt_of_le zero_lt_one (nG_one_le K))
  have hlog := Real.log_le_log hp hprod
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hk0.ne'), Real.log_pow] at hlog
  norm_num at hlog
  linarith [log_sixteen_le]

lemma Jpar_le (K : ℕ) (hK : 1 ≤ K) :
    (Jpar K : ℝ) ≤ 4000 * (K : ℝ)^6 * (1 + Real.log K)^15 := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL := logScale_one_le K
  have hlog0 : 0 ≤ Real.log (nA K * nG K) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (nA_one_le K) (nG_one_le K)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤
    4 * (K : ℝ)^2 * Hpar K ^ 2 * Real.log (nA K * nG K) by positivity)).le
  change (Jpar K : ℝ) ≤ _ at hceil
  have hbound : 4 * (K : ℝ)^2 * Hpar K ^ 2 * Real.log (nA K * nG K) ≤
      3600 * (K : ℝ)^6 * (1 + Real.log K)^15 := by
    calc
      _ ≤ 4 * (K : ℝ)^2 *
          (15 * (K : ℝ)^2 * (1 + Real.log K)^7)^2 * (4 * (1 + Real.log K)) := by
        gcongr
        · exact Hpar_nonneg K
        · exact Hpar_le K hK
        · exact log_card_product_le K hK
      _ = _ := by ring
  have hbase : 1 ≤ (K : ℝ)^6 * (1 + Real.log K)^15 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hL)
  nlinarith

lemma gridList_length (K : ℕ) : (gridList K).length = (K + 1)^2 := by
  simp [gridList, List.length_flatMap, List.length_finRange, List.length_map, pow_two]

lemma actList_length_le (K : ℕ) : (actList K).length ≤ (K + 1)^2 := by
  exact (List.length_filterMap_le _ _).trans_eq (gridList_length K)

lemma tableList_length (K : ℕ) :
    (tableList K).length = (gridList K).length * (actList K).length := by
  simp [tableList, List.length_flatMap, List.length_map]

lemma gridList_length_pos (K : ℕ) : 0 < (gridList K).length := by
  rw [gridList_length]
  positivity

lemma actList_length_pos (K : ℕ) : 0 < (actList K).length := by
  have hzero : ((0 : Fin (K+1)), (0 : Fin (K+1))) ∈ gridList K := by
    simp [gridList]
  have hmem : (⟨(0, 0), le_rfl⟩ : Act K) ∈ actList K := by
    apply List.mem_filterMap.mpr
    refine ⟨((0 : Fin (K+1)), (0 : Fin (K+1))), hzero, ?_⟩
    simp
  exact List.length_pos_of_mem hmem

end BilateralProfit.RuntimeSubmission

namespace BilateralProfit.RuntimeSubmission

open CapacitatedAssort.General (Work charge)

lemma costLE_sumW {α : Type} (l : List α) (f : α → Work ℝ) (B : ℕ)
    (hf : ∀ x, CostLE (f x) B) :
    CostLE (sumW l f) (1 + l.length * (2 + B)) := by
  unfold sumW
  apply costLE_mono
  · apply costLE_bind (costLE_charge 1)
    intro _
    apply costLE_bind
    · apply costLE_forIn l _ (2 + B)
      intro x acc
      apply costLE_bind (costLE_charge 2)
      intro _
      apply costLE_mono
      · apply costLE_bind (hf x)
        intro y
        exact costLE_pure _
      · omega
    · intro _
      exact costLE_pure _
  · omega

lemma costLE_tab {α : Type} [DecidableEq α] (l : List α) (f : α → Work ℝ) (B : ℕ)
    (hf : ∀ x, CostLE (f x) B) :
    CostLE (tab l f) (1 + l.length * (2 + B)) := by
  unfold tab
  apply costLE_mono
  · apply costLE_bind (costLE_charge 1)
    intro _
    apply costLE_bind
    · apply costLE_forIn l _ (2 + B)
      intro x acc
      apply costLE_bind (costLE_charge 2)
      intro _
      apply costLE_mono
      · apply costLE_bind (hf x)
        intro y
        exact costLE_pure _
      · omega
    · intro _
      exact costLE_pure _
  · omega

def candidateBudget (K : ℕ) : ℕ :=
  7 + 34 * (actList K).length + 17 * (actList K).length * (gridList K).length +
    22 * (tableList K).length

lemma costLE_candidate (K : ℕ) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ)
    (a : Act K) : CostLE (candidate K w ρ a) (candidateBudget K) := by
  unfold candidate
  apply costLE_mono
  · apply costLE_bind
    · apply costLE_tab _ _ (1 + (gridList K).length * (2 + 6))
      intro a'
      apply costLE_sumW _ _ 6
      intro v
      apply costLE_mono
      · apply costLE_bind (costLE_charge 6)
        intro _
        exact costLE_pure _
      · omega
    · intro j1
      apply costLE_bind
      · apply costLE_tab _ _ (1 + (gridList K).length * (2 + 7))
        intro a'
        apply costLE_sumW _ _ 7
        intro v
        apply costLE_mono
        · apply costLE_bind (costLE_charge 7)
          intro _
          exact costLE_pure _
        · omega
      · intro j0
        apply costLE_bind
        · apply costLE_sumW _ _ 1
          intro a'
          apply costLE_mono
          · apply costLE_bind (costLE_charge 1)
            intro _
            exact costLE_pure _
          · omega
        · intro p1
          apply costLE_bind
          · apply costLE_sumW _ _ 1
            intro a'
            apply costLE_mono
            · apply costLE_bind (costLE_charge 1)
              intro _
              exact costLE_pure _
            · omega
          · intro p0
            apply costLE_bind
            · apply costLE_tab _ _ 9
              intro a'
              apply costLE_mono
              · apply costLE_bind (costLE_charge 9)
                intro _
                exact costLE_pure _
              · omega
            · intro Q1
              apply costLE_bind
              · apply costLE_tab _ _ 9
                intro a'
                apply costLE_mono
                · apply costLE_bind (costLE_charge 9)
                  intro _
                  exact costLE_pure _
                · omega
              · intro Q0
                apply costLE_bind
                · apply costLE_sumW _ _ 20
                  intro x
                  apply costLE_mono
                  · apply costLE_bind (costLE_charge 20)
                    intro _
                    exact costLE_pure _
                  · omega
                · intro sc
                  exact costLE_pure _
  · unfold candidateBudget
    ring_nf
    exact le_rfl


def stepBudget (K : ℕ) : ℕ :=
  (actList K).length * (candidateBudget K + 2) + 2 + 24 * (tableList K).length

lemma costLE_oneStep (K : ℕ) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    CostLE (oneStep K w ρ) (stepBudget K) := by
  unfold oneStep
  apply costLE_mono
  · apply costLE_bind
    · apply costLE_forIn _ _ (candidateBudget K + 2)
      intro a best
      apply costLE_mono
      · apply costLE_bind (costLE_charge 1)
        intro _
        apply costLE_bind (costLE_candidate K w ρ a)
        intro out
        rcases out with ⟨Q0, Q1, sc⟩
        cases best with
        | none => exact costLE_mono (costLE_pure _) (show 0 ≤ 1 by omega)
        | some best =>
          rcases best with ⟨P, bsc⟩
          apply costLE_mono
          · apply costLE_bind (costLE_charge 1)
            intro _
            split_ifs <;> exact costLE_pure _
          · omega
      · omega
    · intro best
      apply costLE_bind (costLE_charge 1)
      intro _
      apply costLE_bind
      · apply costLE_tab _ _ 22
        intro x
        apply costLE_mono
        · apply costLE_bind (costLE_charge 22)
          intro _
          exact costLE_pure _
        · omega
      · intro ρ'
        exact costLE_pure _
  · unfold stepBudget
    omega

lemma costLE_oneRoundLoop (K : ℕ) (w : Act K → ℝ) (n : ℕ)
    (ρ : Grid K × Act K → ℝ) :
    CostLE (oneRoundLoop K w n ρ) ((n + 1) * stepBudget K) := by
  induction n generalizing ρ with
  | zero =>
    apply costLE_mono
    · apply costLE_bind (costLE_oneStep K w ρ)
      intro out
      exact costLE_pure _
    · omega
  | succ n ih =>
    apply costLE_mono
    · apply costLE_bind (costLE_oneStep K w ρ)
      intro out
      exact ih out.2
    · simp only [Nat.add_mul, Nat.one_mul]
      omega

noncomputable def roundBudget (K : ℕ) : ℕ :=
  41 + 5 * (tableList K).length + Jpar K * stepBudget K

lemma costLE_oneRound (K : ℕ) (w : Act K → ℝ) (j : Fin (Jpar K)) :
    CostLE (oneRound K w j) (roundBudget K) := by
  unfold oneRound
  apply costLE_mono
  · apply costLE_bind (costLE_charge 40)
    intro _
    apply costLE_bind
    · apply costLE_tab _ _ 3
      intro x
      apply costLE_mono
      · apply costLE_bind (costLE_charge 3)
        intro _
        exact costLE_pure _
      · omega
    · intro ρ
      exact costLE_oneRoundLoop K w j.val ρ
  · unfold roundBudget
    have hj : j.val + 1 ≤ Jpar K := j.isLt
    have hm := Nat.mul_le_mul_right (stepBudget K) hj
    omega

noncomputable def algorithmBudget (K T : ℕ) : ℕ :=
  1 + 4 * (actList K).length + T * (8 + (actList K).length + roundBudget K)

lemma costLE_alg1 (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K)) :
    CostLE (alg1 K T S ω) (algorithmBudget K T) := by
  unfold alg1
  apply costLE_mono
  · apply costLE_bind
    · apply costLE_tab _ _ 2
      intro a
      apply costLE_mono
      · apply costLE_bind (costLE_charge 2)
        intro _
        exact costLE_pure _
      · omega
    · intro w1
      apply costLE_bind
      · apply costLE_forIn _ _ (8 + (actList K).length + roundBudget K)
        intro t acc
        apply costLE_mono
        · apply costLE_bind (costLE_charge 2)
          intro _
          apply costLE_bind (costLE_oneRound K _ (ω t))
          intro P
          apply costLE_bind (costLE_charge 6)
          intro _
          apply costLE_bind (costLE_charge (actList K).length)
          intro _
          exact costLE_pure _
        · omega
      · intro acc
        exact costLE_pure _
  · simp only [List.length_finRange]
    unfold algorithmBudget
    omega

lemma alg1Cost_le_budget (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K)) :
    alg1Cost K T S ω ≤ algorithmBudget K T := by
  simpa [alg1Cost, runW] using costLE_alg1 K T S ω 0

end BilateralProfit.RuntimeSubmission

namespace BilateralProfit.RuntimeSubmission

lemma algorithmBudget_le (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    (algorithmBudget K T : ℝ) ≤
      50000000 * T * (K : ℝ)^12 * (1 + Real.log K)^15 := by
  let a : ℝ := (actList K).length
  let g : ℝ := (gridList K).length
  let J : ℝ := Jpar K
  have ha : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast actList_length_pos K
  have hg : 1 ≤ g := by
    dsimp [g]
    exact_mod_cast gridList_length_pos K
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have ha0 : 0 ≤ a := by positivity
  have hg0 : 0 ≤ g := by positivity
  have ha2 : a ≤ a^2 := by nlinarith
  have ha2g : a^2 ≤ g*a^2 := by nlinarith [sq_nonneg a]
  have hga : g*a ≤ g*a^2 := mul_le_mul_of_nonneg_left ha2 hg0
  have hga1 : 1 ≤ g*a^2 := by nlinarith
  have hstep : a * (7 + 34*a + 17*a*g + 22*g*a + 2) + 2 + 24*g*a ≤
      108*g*a^2 := by
    nlinarith
  have hround : 41 + 5*g*a + J*(a*(7+34*a+17*a*g+22*g*a+2)+2+24*g*a) ≤
      46*g*a^2 + 108*J*g*a^2 := by
    have hmul := mul_le_mul_of_nonneg_left hstep hJ
    nlinarith
  have hinit : 1 + 4*a ≤ (T : ℝ) * (1 + 4*a) := by nlinarith
  have hraw :
      1+4*a+(T:ℝ)*(8+a+(41+5*g*a+J*(a*(7+34*a+17*a*g+22*g*a+2)+2+24*g*a))) ≤
        168*T*(J+1)*g*a^2 := by
    have hm := mul_le_mul_of_nonneg_left hround (show (0 : ℝ) ≤ T by positivity)
    have hrest : 50+5*a+5*g*a ≤ 60*g*a^2 := by nlinarith
    have hm' := mul_le_mul_of_nonneg_left hrest (show (0 : ℝ) ≤ T by positivity)
    have hnon : 0 ≤ (T : ℝ) * J * g * a^2 := by positivity
    nlinarith
  have hbudget : (algorithmBudget K T : ℝ) ≤ 168*T*(J+1)*g*a^2 := by
    convert hraw using 1 <;>
      simp only [algorithmBudget, roundBudget, stepBudget, candidateBudget, tableList_length,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> dsimp [a, g, J] <;> ring
  have hgK : g ≤ 4 * (K : ℝ)^2 := by
    simpa [g, gridList_length, nG_eq, Nat.cast_pow, Nat.cast_add] using nG_le K hK
  have haK : a ≤ 4 * (K : ℝ)^2 := by
    apply le_trans _ hgK
    dsimp [a, g]
    exact_mod_cast (actList_length_le K).trans_eq (gridList_length K).symm
  have hgaK : g*a^2 ≤ 64*(K : ℝ)^6 := by
    calc
      g*a^2 ≤ (4*(K : ℝ)^2)*(4*(K : ℝ)^2)^2 := by
        gcongr
      _ = _ := by ring
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL := logScale_one_le K
  have hbase : 1 ≤ (K : ℝ)^6*(1+Real.log K)^15 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hL)
  have hJK : J+1 ≤ 4001*(K : ℝ)^6*(1+Real.log K)^15 := by
    dsimp [J]
    nlinarith [Jpar_le K hK]
  calc
    (algorithmBudget K T : ℝ) ≤ 168*T*(J+1)*(g*a^2) := by
      convert hbudget using 1 <;> ring
    _ ≤ 168*T*(4001*(K : ℝ)^6*(1+Real.log K)^15)*(64*(K : ℝ)^6) := by
      gcongr
    _ = 43018752*T*(K : ℝ)^12*(1+Real.log K)^15 := by ring
    _ ≤ 50000000*T*(K : ℝ)^12*(1+Real.log K)^15 := by
      gcongr
      norm_num

lemma alg1Cost_bound (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K)) :
    (alg1Cost K T S ω : ℝ) ≤
      50000000 * T * (K : ℝ)^12 * (1 + Real.log K)^15 := by
  exact (Nat.cast_le.mpr (alg1Cost_le_budget K T S ω)).trans (algorithmBudget_le K T hK hT)

end BilateralProfit.RuntimeSubmission

namespace BilateralProfit

theorem cert_running_time_submission :
    ∃ C c : ℝ, ∀ T K : ℕ, 1 ≤ T → 1 ≤ K →
      ∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar K),
          (alg1Cost K T S ω : ℝ) ≤ C * T * (K : ℝ)^12 * (1 + Real.log K)^c := by
  refine ⟨50000000, 15, ?_⟩
  intro T K hT hK S hS ω
  simpa only [show (15 : ℝ) = (15 : ℕ) by norm_num, Real.rpow_natCast] using
    RuntimeSubmission.alg1Cost_bound K T hK hT S ω

end BilateralProfit

open BilateralProfit

theorem solution :
    ∃ C c : ℝ, ∀ T K : ℕ, 1 ≤ T → 1 ≤ K →
      ∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar K),
          (alg1Cost K T S ω : ℝ) ≤ C * T * (K : ℝ) ^ 12 * (1 + Real.log K) ^ c := by exact BilateralProfit.cert_running_time_submission

