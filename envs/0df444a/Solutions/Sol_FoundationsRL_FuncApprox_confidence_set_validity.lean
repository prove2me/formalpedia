-- Prove2me | solution 1 for FoundationsRL.FuncApprox.confidence_set_validity
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:36:06.392492+00:00
-- url     : https://prove2.me/submissions/7892058c-9f65-4b70-8011-6f669e6ee85e

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

set_option autoImplicit false

namespace CexBLU08

open FoundationsRL.RLBasics FoundationsRL.FuncApprox

/-- Two states, one action, horizon 2; uniform transitions; reward `L` only at layer 1 in state
`true`. -/
noncomputable def cexM (L : ℝ) : EpisodicMDP Bool Unit 2 where
  P := fun _ _ _ _ => 1 / 2
  R := fun h s _ => if h = 1 ∧ s = true then L else 0
  d1 := fun _ => 1 / 2
  P_nonneg := by intros; norm_num
  P_sum_one := by intros; simp
  d1_nonneg := by intros; norm_num
  d1_sum_one := by simp

noncomputable def cexQ (L : ℝ) : Unit → ℕ → Bool → Unit → ℝ :=
  fun _ h s a => if h < 2 then Qstar (cexM L) h s a else 0

instance instNEPol : Nonempty {π : Policy Bool Unit 2 // IsPolicy 2 π} :=
  ⟨⟨fun _ _ _ => 1, by intro h _ s; simp⟩⟩

theorem Q1 (L : ℝ) (π : Policy Bool Unit 2) (s : Bool) :
    Q (cexM L) π 1 s () = if s then L else 0 := by
  cases s <;> simp [Q, V, valueAux, cexM]

theorem Q0 (L : ℝ) (π : Policy Bool Unit 2) (hπ : IsPolicy 2 π) (s : Bool) :
    Q (cexM L) π 0 s () = L / 2 := by
  have h1 : ∀ s', π 1 s' () = 1 := by
    intro s'
    have := (hπ 1 (by norm_num) s').2
    simpa using this
  simp [Q, V, valueAux, cexM, h1]
  ring

theorem Qstar1 (L : ℝ) (s : Bool) : Qstar (cexM L) 1 s () = if s then L else 0 := by
  unfold Qstar
  simp only [Q1]
  exact ciSup_const

theorem Qstar0 (L : ℝ) (s : Bool) : Qstar (cexM L) 0 s () = L / 2 := by
  unfold Qstar
  have : ∀ π : {π : Policy Bool Unit 2 // IsPolicy 2 π}, Q (cexM L) π.1 0 s () = L / 2 :=
    fun π => Q0 L π.1 π.2 s
  simp only [this]
  exact ciSup_const

theorem resid_sq (L : ℝ) (τ : Trajectory Bool Unit 2) :
    (cexQ L () 0 (stateAt τ 0) (actionAt τ 0) - (cexM L).R 0 (stateAt τ 0) (actionAt τ 0) -
        (if 0 + 1 < 2 then ⨆ a' : Unit, cexQ L () (0 + 1) (nextStateAt τ 0) a' else 0)) ^ 2
      = L ^ 2 / 4 := by
  have hR : (cexM L).R 0 (stateAt τ 0) (actionAt τ 0) = 0 := by simp [cexM]
  rw [hR]
  simp only [cexQ, show (0:ℕ) < 2 by norm_num, show (0:ℕ) + 1 < 2 by norm_num, if_true,
    show (0:ℕ) + 1 = 1 by norm_num]
  rw [Qstar0, ciSup_unique, Qstar1]
  cases nextStateAt τ 0 <;> simp <;> ring

theorem resEst_sq (L : ℝ) (hist : List (Trajectory Bool Unit 2)) (hl : 1 ≤ hist.length) :
    (residualEst (cexM L) (cexQ L) hist 1 0 0 ()) ^ 2 = L ^ 2 / 4 := by
  unfold residualEst batch
  have hlen : ((hist.drop (0 * 1)).take 1).length = 1 := by simp; omega
  obtain ⟨τ, hτ⟩ := List.length_eq_one_iff.mp hlen
  rw [hτ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Nat.cast_one, div_one]
  exact resid_sq L τ

theorem prob_zero (L β : ℝ) (hβ : β < L ^ 2 / 4) (T : ℕ) (hT : 1 ≤ T)
    (learner : Learner Bool Unit 2) (E : (Fin T → Trajectory Bool Unit 2) → Prop)
    (hE : ∀ histT, E histT → () ∈ confSet (cexM L) (cexQ L) (List.ofFn histT) 1 β 1) :
    probEvent (cexM L) learner T E = 0 := by
  unfold probEvent
  apply Finset.sum_eq_zero
  intro histT _
  rw [if_neg]
  intro hx
  have hm := hE histT hx
  simp only [confSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have h0 := hm ⟨0, by norm_num⟩
  simp only [Finset.sum_range_one] at h0
  rw [resEst_sq L _ (by simpa using hT)] at h0
  linarith

end CexBLU08

open FoundationsRL.RLBasics FoundationsRL.FuncApprox in
theorem solution : ¬ (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ → δ ≤ 1 →
        ∀ β : ℝ, β = c * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
        probEvent M (biLinUCBLearner M qeval n β) (K * n)
            (fun histT =>
              ∀ k, k < K →
                (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                    ∑ i ∈ Finset.range k,
                      (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                        (qeval Qf)) ^ 2 ≤ C * β) ∧
                q0 ∈ confSet M qeval (List.ofFn histT) n β k)
          ≥ 1 - δ) := by
  rintro ⟨c, C, hc, hC, h⟩
  have key := h (S := Bool) (A := Unit) (H := 2) (CexBLU08.cexM (2 * (8 * c + 1))) (Qc := Unit)
    (CexBLU08.cexQ (2 * (8 * c + 1))) () rfl 1 2 (1 / 2) one_pos (by norm_num) (by norm_num) _ rfl
  rw [CexBLU08.prob_zero (2 * (8 * c + 1)) _ ?hb (2 * 1) (by norm_num) _ _ ?hE] at key
  · norm_num at key
  case hE =>
    intro histT hx
    exact (hx 1 (by norm_num)).2
  case hb =>
    have hl : Real.log (2 * 2 / (1 / 2)) ≤ 2 * 2 / (1 / 2) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hl0 : 0 ≤ Real.log (2 * 2 / (1 / 2)) := Real.log_nonneg (by norm_num)
    simp only [Fintype.card_unit, Nat.cast_one, Real.log_one, mul_zero, zero_add, div_one,
      Nat.cast_ofNat]
    nlinarith
