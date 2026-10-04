-- Prove2me | solution 1 for BJNAdAuctions.Basic.primal_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:32:57.367196+00:00
-- url     : https://prove2.me/submissions/98f6462a-e3d0-4596-a762-132147d31eae

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

set_option autoImplicit false

namespace BJNAdAuctions.Basic.PF8fead732

open BJNAdAuctions.Basic

variable {I : Type*} [Fintype I] {m : ℕ}

def Inv (inst : Instance I m) (s : State I m) (k : ℕ) : Prop :=
  (∀ i, 0 ≤ s.x i) ∧ (∀ j, 0 ≤ s.z j) ∧
  (∀ j : Fin m, j.val < k → ∀ i, inst.b i j ≤ inst.b i j * s.x i + s.z j)

lemma inv_zero (inst : Instance I m) : Inv inst (State.init : State I m) 0 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

open Classical in
lemma inv_step (inst : Instance I m) (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I)
    (hsel : IsArgmaxRule inst sel) (s : State I m) (k : ℕ) (hk : k < m)
    (hs : Inv inst s k) : Inv inst (step inst c sel s ⟨k, hk⟩) (k + 1) := by
  obtain ⟨hx, hz, hcov⟩ := hs
  have harg := hsel s.x ⟨k, hk⟩
  by_cases h : 1 ≤ s.x (sel s.x ⟨k, hk⟩)
  · have hst : step inst c sel s ⟨k, hk⟩ = s := by
      simp [step, h]
    rw [hst]
    refine ⟨hx, hz, ?_⟩
    intro j hj i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact hcov j hj i
    · have hjj : j = ⟨k, hk⟩ := Fin.ext hj
      subst hjj
      have h1 := harg i
      have hb0 := inst.b_nonneg (sel s.x ⟨k, hk⟩) ⟨k, hk⟩
      have h2 : inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ * (1 - s.x (sel s.x ⟨k, hk⟩)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb0 (by linarith)
      nlinarith [hz ⟨k, hk⟩]
  · have hxs : (step inst c sel s ⟨k, hk⟩).x = Function.update s.x (sel s.x ⟨k, hk⟩)
        (s.x (sel s.x ⟨k, hk⟩) * (1 + inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ / inst.B (sel s.x ⟨k, hk⟩))
          + inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ / ((c - 1) * inst.B (sel s.x ⟨k, hk⟩))) := by
      simp [step, h]
    have hzs : (step inst c sel s ⟨k, hk⟩).z = Function.update s.z ⟨k, hk⟩
        (inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ * (1 - s.x (sel s.x ⟨k, hk⟩))) := by
      simp [step, h]
    have hmono : ∀ i, s.x i ≤ (step inst c sel s ⟨k, hk⟩).x i := by
      intro i
      rw [hxs, Function.update_apply]
      split_ifs with hi
      · rw [hi]
        have hb := inst.b_nonneg (sel s.x ⟨k, hk⟩) ⟨k, hk⟩
        have hB := inst.B_pos (sel s.x ⟨k, hk⟩)
        have h1 : 0 ≤ inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ / inst.B (sel s.x ⟨k, hk⟩) :=
          div_nonneg hb hB.le
        have h2 : 0 ≤ inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ / ((c - 1) * inst.B (sel s.x ⟨k, hk⟩)) :=
          div_nonneg hb (mul_pos (by linarith) hB).le
        nlinarith [hx (sel s.x ⟨k, hk⟩)]
      · exact le_rfl
    refine ⟨fun i => le_trans (hx i) (hmono i), ?_, ?_⟩
    · intro j
      rw [hzs, Function.update_apply]
      split_ifs with hj
      · exact mul_nonneg (inst.b_nonneg _ _) (by linarith)
      · exact hz j
    · intro j hj i
      have hbi := inst.b_nonneg i j
      have hmi := hmono i
      have hprod : inst.b i j * s.x i ≤ inst.b i j * (step inst c sel s ⟨k, hk⟩).x i :=
        mul_le_mul_of_nonneg_left hmi hbi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · have hne : j ≠ ⟨k, hk⟩ := by
          intro e; rw [e] at hj; exact lt_irrefl _ hj
        have hzj : (step inst c sel s ⟨k, hk⟩).z j = s.z j := by
          rw [hzs, Function.update_of_ne hne]
        rw [hzj]
        linarith [hcov j hj i]
      · have hjj : j = ⟨k, hk⟩ := Fin.ext hj
        subst hjj
        have hzj : (step inst c sel s ⟨k, hk⟩).z ⟨k, hk⟩ =
            inst.b (sel s.x ⟨k, hk⟩) ⟨k, hk⟩ * (1 - s.x (sel s.x ⟨k, hk⟩)) := by
          rw [hzs, Function.update_self]
        rw [hzj]
        nlinarith [harg i]

lemma inv_runPrefix (inst : Instance I m) (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I)
    (hsel : IsArgmaxRule inst sel) :
    ∀ k, k ≤ m → Inv inst (runPrefix inst c sel k) k := by
  intro k
  induction k with
  | zero => intro _; simpa [runPrefix] using inv_zero inst
  | succ k ih =>
    intro hk
    have hk' : k < m := hk
    have := inv_step inst c hc sel hsel _ k hk' (ih hk'.le)
    simpa [runPrefix, hk'] using this

end BJNAdAuctions.Basic.PF8fead732

open BJNAdAuctions.Basic in
theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) (hsel : IsArgmaxRule inst sel) :
    CoveringFeasible inst (run inst c sel).x (run inst c sel).z := by
  obtain ⟨hx, hz, hcov⟩ :=
    BJNAdAuctions.Basic.PF8fead732.inv_runPrefix inst c hc sel hsel m le_rfl
  exact ⟨fun i j => hcov j j.isLt i, hx, hz⟩
