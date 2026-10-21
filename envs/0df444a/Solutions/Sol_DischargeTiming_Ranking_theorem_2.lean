-- Prove2me | solution 1 for DischargeTiming.Ranking.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:08:53.425155+00:00
-- url     : https://prove2.me/submissions/0017a831-e716-4f34-bc9f-b1a071da69cb

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model
import Theorems.Thm_DischargeTiming_Ranking_interchange_cost

namespace DischargeTiming.Ranking
namespace DTmain

variable {M J : ℕ}

lemma traj_succ_pos (x0 : State M J) (arr : ℕ → Fin M → ℕ) (D : ℕ → Action M J) (i j : ℕ)
    (m : Fin M) (h : j + 1 < J + 1) (h' : j < J + 1) :
    traj x0 arr D (i + 1) m ⟨j + 1, h⟩
      = traj x0 arr D i m ⟨j, h'⟩ - D i m ⟨j, h'⟩ := by
  simp [traj, step]

lemma traj_agree (x0 : State M J) (arr : ℕ → Fin M → ℕ) (D D' : ℕ → Action M J) (n : ℕ)
    (h : ∀ i < n, D' i = D i) : ∀ i ≤ n, traj x0 arr D' i = traj x0 arr D i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    simp only [traj]
    rw [ih (by omega), h i (by omega)]

/-- Following the kept `(m1, t1)` cohort forward from epoch `k`: it is either discharged
(at least partly) at some epoch `k' < H` with LOS `t1 + (k' - k) ≤ J`, or still present
at the horizon. -/
lemma exists_kp (P : Model M J) (x0 : State M J) (arr : ℕ → Fin M → ℕ) (H : ℕ)
    (D : ℕ → Action M J) (hD : FeasibleSchedule P x0 arr H D) (m1 : Fin M) (t1 : Fin (J + 1))
    (k : ℕ) (hk : k < H) (hD1 : D k m1 t1 < traj x0 arr D k m1 t1) :
    ∃ k', k < k' ∧ k' ≤ H ∧ ∃ h1 : (t1 : ℕ) + (k' - k) ≤ J,
      (k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1)) ∧
      (k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1)) := by
  have ht1 : t1.val < J := by
    by_contra hc
    have e : t1 = Fin.last J := Fin.ext (by simp; omega)
    have := (hD k hk).2.2 m1
    rw [← e] at this
    omega
  suffices aux : ∀ n Δ, Δ + n = J - t1.val → 1 ≤ Δ → k + Δ ≤ H →
      ∀ hΔ : t1.val + Δ < J + 1, 1 ≤ traj x0 arr D (k + Δ) m1 ⟨t1.val + Δ, hΔ⟩ →
      ∃ k', k < k' ∧ k' ≤ H ∧ ∃ h1 : (t1 : ℕ) + (k' - k) ≤ J,
        (k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1)) ∧
        (k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1)) by
    have e := traj_succ_pos x0 arr D k t1.val m1 (by omega) t1.isLt
    simp only [Fin.eta] at e
    exact aux (J - t1.val - 1) 1 (by omega) le_rfl (by omega) (by omega) (by rw [e]; omega)
  intro n
  induction n with
  | zero =>
    intro Δ hn h1Δ hkH hΔ hX
    by_cases hH : k + Δ = H
    · refine ⟨H, by omega, le_rfl, by omega, fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      convert hX using 2
      · omega
      · ext; simp [losShift]; omega
    · have hlast : (⟨t1.val + Δ, hΔ⟩ : Fin (J + 1)) = Fin.last J := Fin.ext (by simp; omega)
      have := (hD (k + Δ) (by omega)).2.2 m1
      rw [← hlast] at this
      refine ⟨k + Δ, by omega, hkH, by omega, fun _ => ?_, fun h => absurd h hH⟩
      have e : losShift t1 (k + Δ - k) (by omega) = (⟨t1.val + Δ, hΔ⟩ : Fin (J + 1)) := by
        ext; simp [losShift]
      rw [e]; omega
  | succ n ih =>
    intro Δ hn h1Δ hkH hΔ hX
    by_cases hH : k + Δ = H
    · refine ⟨H, by omega, le_rfl, by omega, fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      convert hX using 2
      · omega
      · ext; simp [losShift]; omega
    · have e : losShift t1 (k + Δ - k) (by omega) = (⟨t1.val + Δ, hΔ⟩ : Fin (J + 1)) := by
        ext; simp [losShift]
      by_cases hd : 1 ≤ D (k + Δ) m1 ⟨t1.val + Δ, hΔ⟩
      · refine ⟨k + Δ, by omega, hkH, by omega, fun _ => ?_, fun h => absurd h hH⟩
        rw [e]; exact hd
      · have es := traj_succ_pos x0 arr D (k + Δ) (t1.val + Δ) m1 (by omega) hΔ
        exact ih (Δ + 1) (by omega) (by omega) (by omega) (by omega)
          (by rw [show k + (Δ + 1) = k + Δ + 1 by omega]
              rw [show (⟨t1.val + (Δ + 1), (by omega : t1.val + (Δ + 1) < J + 1)⟩ : Fin (J + 1))
                = ⟨t1.val + Δ + 1, by omega⟩ from rfl, es]
              omega)

end DTmain
end DischargeTiming.Ranking

open DischargeTiming.Ranking

theorem solution {M J : ℕ} (P : Model M J) (hP : P.Standing) (x0 : State M J)
    (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1))
    (hdom : StronglyDominates P m1 ((t1 : ℕ) : ℝ) m2 ((t2 : ℕ) : ℝ))
    (hne : (m1, t1) ≠ (m2, t2)) (hle : t2 ≤ t1) (hL : P.L m1 ≤ t1) :
    ∃ D' : ℕ → Action M J, FeasibleSchedule P x0 arr H D' ∧
      totalCost P x0 arr H D' ≤ totalCost P x0 arr H D ∧
      ∀ k < H, 0 < D' k m2 t2 → D' k m1 t1 = traj x0 arr D' k m1 t1 := by
  have hle' : t2.val ≤ t1.val := Fin.le_def.mp hle
  have hne' : ¬ (m2.val = m1.val ∧ t2.val = t1.val) := by
    rintro ⟨a, b⟩
    exact hne (Prod.ext (Fin.ext a.symm) (Fin.ext b.symm))
  -- one interchange at epoch `n`
  have step : ∀ E : ℕ → Action M J, FeasibleSchedule P x0 arr H E → ∀ n < H,
      0 < E n m2 t2 → E n m1 t1 < traj x0 arr E n m1 t1 →
      ∃ E' : ℕ → Action M J, FeasibleSchedule P x0 arr H E' ∧
        totalCost P x0 arr H E' ≤ totalCost P x0 arr H E ∧
        (∀ i < n, E' i = E i) ∧ E' n m2 t2 < E n m2 t2 := by
    intro E hE n hn hpos hlt
    obtain ⟨k', hnk', hk'H, h1, hlate, hterm⟩ :=
      DTmain.exists_kp P x0 arr H E hE m1 t1 n hn hlt
    have h2 : t2.val + (k' - n) ≤ J := by omega
    obtain ⟨hF, -, hC⟩ := interchange_cost P hP x0 arr H E hE m1 m2 t1 t2 hdom hL n k' hnk'
      hk'H h1 h2 hpos hlt hlate hterm
    refine ⟨_, hF, hC, ?_, ?_⟩
    · intro i hi
      unfold interchange
      rw [if_neg (by omega), if_neg (by omega)]
    · unfold interchange
      rw [if_pos rfl]
      simp only [Pi.sub_apply, Pi.add_apply, unitAction]
      have : ¬ (m2 = m1 ∧ t2 = t1) := fun h => hne' ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩
      simp only [this, if_false, and_self, if_true]
      omega
  have main : ∀ n ≤ H, ∃ E : ℕ → Action M J, FeasibleSchedule P x0 arr H E ∧
      totalCost P x0 arr H E ≤ totalCost P x0 arr H D ∧
      ∀ i < n, 0 < E i m2 t2 → E i m1 t1 = traj x0 arr E i m1 t1 := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨D, hD, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨E0, hE0, hC0, hR0⟩ := ih (by omega)
      have inner : ∀ c, ∀ E : ℕ → Action M J, FeasibleSchedule P x0 arr H E →
          totalCost P x0 arr H E ≤ totalCost P x0 arr H D →
          (∀ i < n, 0 < E i m2 t2 → E i m1 t1 = traj x0 arr E i m1 t1) →
          E n m2 t2 ≤ c →
          ∃ E' : ℕ → Action M J, FeasibleSchedule P x0 arr H E' ∧
            totalCost P x0 arr H E' ≤ totalCost P x0 arr H D ∧
            ∀ i < n + 1, 0 < E' i m2 t2 → E' i m1 t1 = traj x0 arr E' i m1 t1 := by
        intro c
        induction c with
        | zero =>
          intro E hE hC hR hc
          refine ⟨E, hE, hC, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact hR i h
          · subst h; intro hp; omega
        | succ c ihc =>
          intro E hE hC hR hc
          by_cases hr : 0 < E n m2 t2 → E n m1 t1 = traj x0 arr E n m1 t1
          · refine ⟨E, hE, hC, fun i hi => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · exact hR i h
            · subst h; exact hr
          · push_neg at hr
            obtain ⟨hp, hne2⟩ := hr
            have hlt : E n m1 t1 < traj x0 arr E n m1 t1 :=
              lt_of_le_of_ne ((hE n (by omega)).1 m1 t1) hne2
            obtain ⟨E', hE', hC', hagree, hdec⟩ := step E hE n (by omega) hp hlt
            have htr := DTmain.traj_agree x0 arr E E' n hagree
            refine ihc E' hE' (le_trans hC' hC) ?_ (by omega)
            intro i hi hp'
            rw [hagree i hi, htr i hi.le] at *
            exact hR i hi hp'
      exact inner _ E0 hE0 hC0 hR0 le_rfl
  obtain ⟨E, hE, hC, hR⟩ := main H le_rfl
  exact ⟨E, hE, hC, hR⟩
