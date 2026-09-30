-- Prove2me | solution 1 for DelayedBCN.Controllability.card_controls_avoiding_eq_zeroed_pow
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:23:34.500368+00:00
-- url     : https://prove2.me/submissions/9b69a73e-6dc9-42f2-ac6f-595b92b7557f

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

open DelayedBCN.Controllability

theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Ct : Finset (Traj μ n)) (ya yb : Traj μ n) (k : ℕ) (hk : 0 < k) :
    numAvoiding F k ya yb Ct = (QZeroed F Ct ^ k) yb ya := by
  have hprefix : ∀ (k : ℕ) (U : Fin (k+1) → Input m) (i : ℕ), i ≤ k →
      trajAt F ya U i = trajAt F ya (fun j : Fin k => U j.castSucc) i := by
    intro k U i hi
    induction i with
    | zero => rfl
    | succ i ih =>
        have hik : i < k := Nat.lt_of_succ_le hi
        rw [trajAt, dif_pos (Nat.lt_succ_of_lt hik)]
        rw [trajAt, dif_pos hik]
        have hidx : U ⟨i, Nat.lt_succ_of_lt hik⟩
            = (fun j : Fin k => U j.castSucc) ⟨i, hik⟩ := rfl
        rw [hidx, ih (Nat.le_of_lt hik)]
  have htraj_snoc : ∀ (k : ℕ) (U' : Fin k → Input m) (u : Input m),
      trajAt F ya (Fin.snoc U' u) (k+1) = step F u (trajAt F ya U' k) := by
    intro k U' u
    rw [trajAt, dif_pos (Nat.lt_succ_self k)]
    have hlast : (Fin.snoc (α := fun _ => Input m) U' u) ⟨k, Nat.lt_succ_self k⟩ = u := by
      rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1)) = Fin.last k from Fin.ext rfl]
      exact Fin.snoc_last (α := fun _ => Input m) u U'
    rw [hlast]
    have hpref : (fun j : Fin k => (Fin.snoc (α := fun _ => Input m) U' u) j.castSucc) = U' := by
      funext j
      exact Fin.snoc_castSucc (α := fun _ => Input m) u U' j
    rw [hprefix k (Fin.snoc U' u) k (le_refl k), hpref]
  have hQ0 : ∀ (yb a : Traj μ n), a ∉ Ct →
      (∑ u : Input m, (if step F u a = yb ∧ step F u a ∉ Ct then (1:ℕ) else 0))
        = QZeroed F Ct yb a := by
    intro yb a ha
    by_cases hyb : yb ∈ Ct
    · have hzero : (∑ u : Input m,
          (if step F u a = yb ∧ step F u a ∉ Ct then (1:ℕ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rw [← h1] at hyb
        exact h2 hyb
      rw [hzero]
      simp only [QZeroed]
      rw [if_pos (Or.inl hyb)]
    · rw [show (∑ u : Input m, (if step F u a = yb ∧ step F u a ∉ Ct then (1:ℕ) else 0))
          = ∑ u : Input m, (if step F u a = yb then (1:ℕ) else 0) from by
        apply Finset.sum_congr rfl
        intro u _
        by_cases h : step F u a = yb
        · rw [if_pos ⟨h, by rw [h]; exact hyb⟩, if_pos h]
        · rw [if_neg (fun hh => h hh.1), if_neg h]]
      rw [show (∑ u : Input m, (if step F u a = yb then (1:ℕ) else 0)) = Q F yb a from by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        rfl]
      simp only [QZeroed]
      rw [if_neg]
      rintro (h | h)
      · exact hyb h
      · exact ha h
  have hrec : ∀ (k : ℕ) (yb : Traj μ n), numAvoiding F (k+1) ya yb Ct
      = ∑ a : Traj μ n, numAvoiding F k ya a Ct * QZeroed F Ct yb a := by
    intro k yb
    unfold numAvoiding
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [show (∑ U : Fin (k+1) → Input m,
          (if trajAt F ya U (k+1) = yb ∧
             ∀ i : Fin (k+2), trajAt F ya U i ∉ Ct then (1:ℕ) else 0))
        = ∑ p : Input m × (Fin k → Input m),
          (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb ∧
             ∀ i : Fin (k+2), trajAt F ya (Fin.snoc p.2 p.1) i ∉ Ct
             then (1:ℕ) else 0) from
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k+1) => Input m))
        (fun p : Input m × (Fin k → Input m) =>
          (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb ∧
             ∀ i : Fin (k+2), trajAt F ya (Fin.snoc p.2 p.1) i ∉ Ct
             then (1:ℕ) else 0))
        (fun U : Fin (k+1) → Input m =>
          (if trajAt F ya U (k+1) = yb ∧ ∀ i : Fin (k+2), trajAt F ya U i ∉ Ct
           then (1:ℕ) else 0))
        (fun p => rfl)).symm]
    rw [show (∑ p : Input m × (Fin k → Input m),
          (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb ∧
             ∀ i : Fin (k+2), trajAt F ya (Fin.snoc p.2 p.1) i ∉ Ct
             then (1:ℕ) else 0))
        = ∑ p : Input m × (Fin k → Input m),
          (if step F p.1 (trajAt F ya p.2 k) = yb ∧
             (∀ i : Fin (k+1), trajAt F ya p.2 i ∉ Ct) ∧
             step F p.1 (trajAt F ya p.2 k) ∉ Ct then (1:ℕ) else 0) from by
      apply Finset.sum_congr rfl
      intro p _
      have hpref2 : ∀ i : Fin (k+1),
          trajAt F ya (Fin.snoc p.2 p.1) i.castSucc = trajAt F ya p.2 i := by
        intro i
        change trajAt F ya (Fin.snoc p.2 p.1) i.val = trajAt F ya p.2 i.val
        rw [hprefix k (Fin.snoc p.2 p.1) i.val (Nat.le_of_lt_succ i.isLt)]
        have hpref : (fun j : Fin k =>
            (Fin.snoc (α := fun _ => Input m) p.2 p.1) j.castSucc) = p.2 := by
          funext j
          exact Fin.snoc_castSucc (α := fun _ => Input m) p.1 p.2 j
        rw [hpref]
      have hlast : trajAt F ya (Fin.snoc p.2 p.1) (Fin.last (k+1))
          = step F p.1 (trajAt F ya p.2 k) := by
        rw [show (Fin.last (k+1) : Fin (k+2))
              = ⟨k+1, Nat.lt_succ_self (k+1)⟩ from Fin.ext rfl]
        exact htraj_snoc k p.2 p.1
      have hiff : (trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb ∧
            ∀ i : Fin (k+2), trajAt F ya (Fin.snoc p.2 p.1) i ∉ Ct)
          ↔ (step F p.1 (trajAt F ya p.2 k) = yb ∧
            (∀ i : Fin (k+1), trajAt F ya p.2 i ∉ Ct) ∧
            step F p.1 (trajAt F ya p.2 k) ∉ Ct) := by
        rw [htraj_snoc k p.2 p.1]
        rw [Fin.forall_fin_succ']
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, ⟨fun i => by have hi := h2 i; rwa [hpref2 i] at hi, by
            rwa [hlast] at h3⟩⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, ⟨fun i => by rw [hpref2 i]; exact h2 i, by
            rw [hlast]; exact h3⟩⟩
      by_cases hp : (trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb ∧
             ∀ i : Fin (k+2), trajAt F ya (Fin.snoc p.2 p.1) i ∉ Ct)
      · rw [if_pos hp, if_pos (hiff.mp hp)]
      · rw [if_neg hp, if_neg (fun hh => hp (hiff.mpr hh))]]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have hprod : ∀ U' : Fin k → Input m,
        (∑ u : Input m, (if step F u (trajAt F ya U' k) = yb ∧
            (∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct) ∧
            step F u (trajAt F ya U' k) ∉ Ct then (1:ℕ) else 0))
        = (if (∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct) then (1:ℕ) else 0)
            * QZeroed F Ct yb (trajAt F ya U' k) := by
      intro U'
      by_cases hA : ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct
      · rw [if_pos hA, one_mul]
        have ha : trajAt F ya U' k ∉ Ct := hA (Fin.last k)
        rw [show (∑ u : Input m, (if step F u (trajAt F ya U' k) = yb ∧
              (∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct) ∧
              step F u (trajAt F ya U' k) ∉ Ct then (1:ℕ) else 0))
            = ∑ u : Input m, (if step F u (trajAt F ya U' k) = yb ∧
              step F u (trajAt F ya U' k) ∉ Ct then (1:ℕ) else 0) from by
          apply Finset.sum_congr rfl
          intro u _
          by_cases h : step F u (trajAt F ya U' k) = yb ∧
              step F u (trajAt F ya U' k) ∉ Ct
          · rw [if_pos ⟨h.1, hA, h.2⟩, if_pos h]
          · rw [if_neg (fun hh => h ⟨hh.1, hh.2.2⟩), if_neg h]]
        exact hQ0 yb (trajAt F ya U' k) ha
      · rw [if_neg hA, zero_mul]
        apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        rintro ⟨-, hA', -⟩
        exact hA hA'
    rw [Finset.sum_congr rfl (fun U' _ => hprod U')]
    rw [show (∑ U' : Fin k → Input m, (if (∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct)
          then (1:ℕ) else 0) * QZeroed F Ct yb (trajAt F ya U' k))
        = ∑ U' : Fin k → Input m, (if (∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct)
          then QZeroed F Ct yb (trajAt F ya U' k) else 0) from by
      apply Finset.sum_congr rfl
      intro U' _
      by_cases hA : ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct <;> simp [hA]]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin k → Input m)))
          (p := fun U' : Fin k → Input m => ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct)
          (f := fun U' => QZeroed F Ct yb (trajAt F ya U' k))]
    have hstep4 : (Finset.sum (Finset.univ.filter (fun U' : Fin k → Input m =>
          ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct))
          (fun U' => QZeroed F Ct yb (trajAt F ya U' k)))
        = ∑ a : Traj μ n, numAvoiding F k ya a Ct * QZeroed F Ct yb a := by
      rw [← Finset.sum_fiberwise_of_maps_to'
            (s := (Finset.univ.filter (fun U' : Fin k → Input m =>
              ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct)))
            (t := (Finset.univ : Finset (Traj μ n)))
            (g := fun U' => trajAt F ya U' k) (f := fun a => QZeroed F Ct yb a)
            (fun i _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_const]
      have hcard : (((Finset.univ.filter (fun U' : Fin k → Input m =>
            ∀ i : Fin (k+1), trajAt F ya U' i ∉ Ct))).filter
            (fun U' => trajAt F ya U' k = a)).card = numAvoiding F k ya a Ct := by
        unfold numAvoiding
        rw [Finset.filter_filter]
        congr 1
        apply Finset.ext
        intro U'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      rw [hcard]
      exact nsmul_eq_mul _ _
    rw [hstep4]
    rfl
  have hbase0 : ∀ a : Traj μ n,
      numAvoiding F 0 ya a Ct = if a = ya ∧ ya ∉ Ct then (1:ℕ) else 0 := by
    intro a
    haveI : Unique (Fin 0 → Input m) :=
      ⟨⟨fun i => i.elim0⟩, fun U => funext fun i => i.elim0⟩
    unfold numAvoiding
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_unique]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩
      rw [Fin.forall_fin_one] at h2
      exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, by rw [Fin.forall_fin_one]; exact h2⟩
  have main : ∀ j : ℕ, ∀ yb : Traj μ n,
      numAvoiding F (j+1) ya yb Ct = (QZeroed F Ct ^ (j+1)) yb ya := by
    intro j
    induction j with
    | zero =>
        intro yb
        rw [pow_one, hrec 0 yb]
        have h₁ : ∀ b ∈ (Finset.univ : Finset (Traj μ n)), b ≠ ya →
            numAvoiding F 0 ya b Ct * QZeroed F Ct yb b = 0 := by
          intro b _ hb
          have hnb : ¬ (b = ya ∧ ya ∉ Ct) := fun hh => hb hh.1
          rw [hbase0 b, if_neg hnb, zero_mul]
        have h₂ : ya ∉ (Finset.univ : Finset (Traj μ n)) →
            numAvoiding F 0 ya ya Ct * QZeroed F Ct yb ya = 0 := by
          intro h
          exact absurd (Finset.mem_univ ya) h
        rw [Finset.sum_eq_single (s := (Finset.univ : Finset (Traj μ n)))
              (f := fun a : Traj μ n => numAvoiding F 0 ya a Ct * QZeroed F Ct yb a)
              ya h₁ h₂]
        rw [hbase0 ya]
        by_cases hc : ya ∈ Ct
        · simp [QZeroed, hc]
        · rw [if_pos ⟨rfl, hc⟩, one_mul]
    | succ j ih =>
        intro yb
        rw [hrec (j+1) yb]
        rw [show (∑ a : Traj μ n, numAvoiding F (j+1) ya a Ct * QZeroed F Ct yb a)
            = ∑ a : Traj μ n, (QZeroed F Ct ^ (j+1)) a ya * QZeroed F Ct yb a from
          Finset.sum_congr rfl (fun a _ => by rw [ih a])]
        rw [show (∑ a : Traj μ n, (QZeroed F Ct ^ (j+1)) a ya * QZeroed F Ct yb a)
            = (QZeroed F Ct * QZeroed F Ct ^ (j+1)) yb ya from by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro a _
          rw [mul_comm]]
        rw [← pow_succ']
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact main j yb
