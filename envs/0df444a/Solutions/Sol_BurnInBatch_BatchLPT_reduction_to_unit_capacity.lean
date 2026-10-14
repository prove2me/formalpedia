-- Prove2me | solution 1 for BurnInBatch.BatchLPT.reduction_to_unit_capacity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:45:54.363754+00:00
-- url     : https://prove2.me/submissions/5fd5e583-22e1-4fdd-bab9-493dcc7d97c7

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT



namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling



lemma fa_spec {m : ℕ} (hm : 0 < m) (ℓ : Fin m → ℝ) :
    ∃ i0, firstAvailable ℓ = some i0 ∧ ∀ k, ℓ i0 ≤ ℓ k := by
  have hne : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty := by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ ℓ Finset.univ_nonempty
    exact ⟨i, by simpa using hi⟩
  refine ⟨(Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).min' hne, ?_, ?_⟩
  · unfold firstAvailable; rw [dif_pos hne]
  · have := Finset.min'_mem _ hne
    simpa using this

lemma ls_succ {m : ℕ} (q : ℕ → ℝ) (k : ℕ) (i0 : Fin m)
    (h : firstAvailable (lsLoads m q k) = some i0) (i : Fin m) :
    lsLoads m q (k+1) i = if i = i0 then lsLoads m q k i + q k else lsLoads m q k i := by
  show (if firstAvailable (lsLoads m q k) = some i then _ else _) = _
  rw [h]
  by_cases hi : i = i0
  · subst hi; simp
  · have : ¬ (some i0 = some i) := by
      intro h'; exact hi (Option.some.inj h').symm
    simp [this, hi]

lemma ls_sum {m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (k : ℕ) :
    ∑ i, lsLoads m q k i = ∑ j ∈ Finset.range k, q j := by
  induction k with
  | zero => simp [lsLoads]
  | succ k ih =>
    obtain ⟨i0, h0, -⟩ := fa_spec hm (lsLoads m q k)
    have : ∀ i, lsLoads m q (k+1) i = lsLoads m q k i + if i = i0 then q k else 0 := by
      intro i; rw [ls_succ q k i0 h0]; split_ifs <;> simp
    simp only [this, Finset.sum_add_distrib, ih, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_range_succ]

lemma ls_sigma {m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (k : ℕ) :
    ∃ σ : Fin k → Fin m, ∀ i, lsLoads m q k i = machineLoad q σ i := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => by simp [lsLoads, machineLoad]⟩
  | succ k ih =>
    obtain ⟨σ, hσ⟩ := ih
    obtain ⟨i0, h0, -⟩ := fa_spec hm (lsLoads m q k)
    refine ⟨Fin.snoc σ i0, fun i => ?_⟩
    rw [ls_succ q k i0 h0, hσ i]
    unfold machineLoad
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    by_cases hi : i = i0
    · subst hi; simp
    · simp [hi, Ne.symm hi]

lemma ml_eq {n m : ℕ} (q : ℕ → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    machineLoad q σ i = ∑ j ∈ Finset.univ.filter (fun j => σ j = i), q (j : ℕ) := by
  unfold machineLoad
  rw [Finset.sum_filter]

lemma ml_nonneg {n m : ℕ} (q : ℕ → ℝ) (hq : ∀ j < n, 0 ≤ q j) (σ : Fin n → Fin m) (i : Fin m) :
    0 ≤ machineLoad q σ i := by
  unfold machineLoad
  exact Finset.sum_nonneg (fun j _ => by split_ifs; exact hq _ j.2; exact le_rfl)

lemma ml_le_makespan {n m : ℕ} (q : ℕ → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    machineLoad q σ i ≤ makespan q σ :=
  le_ciSup (f := fun i => machineLoad q σ i) (Set.finite_range _).bddAbove i

lemma makespan_nonneg {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (hq : ∀ j < n, 0 ≤ q j)
    (σ : Fin n → Fin m) : 0 ≤ makespan q σ :=
  (ml_nonneg q hq σ ⟨0, hm⟩).trans (ml_le_makespan q σ _)

lemma opt_le {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (hq : ∀ j < n, 0 ≤ q j) (σ : Fin n → Fin m) :
    optMakespan n m q ≤ makespan q σ :=
  ciInf_le ⟨0, by rintro _ ⟨τ, rfl⟩; exact makespan_nonneg hm q hq τ⟩ σ

lemma le_opt {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (X : ℝ) (h : ∀ σ : Fin n → Fin m, X ≤ makespan q σ) :
    X ≤ optMakespan n m q := by
  haveI : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  exact le_ciInf h

lemma opt_nonneg {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (hq : ∀ j < n, 0 ≤ q j) :
    0 ≤ optMakespan n m q :=
  le_opt hm q 0 (fun σ => makespan_nonneg hm q hq σ)

lemma opt_mono {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (hq : ∀ j < n + 1, 0 ≤ q j) :
    optMakespan n m q ≤ optMakespan (n+1) m q := by
  apply le_opt hm q
  intro σ
  have h1 : optMakespan n m q ≤ makespan q (fun j : Fin n => σ j.castSucc) :=
    opt_le hm q (fun j hj => hq j (by omega)) _
  refine h1.trans ?_
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply ciSup_le
  intro i
  refine le_trans ?_ (ml_le_makespan q σ i)
  unfold machineLoad
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc]
  have : 0 ≤ (if σ (Fin.last n) = i then q (Fin.last n : ℕ) else 0) := by
    split_ifs
    · exact hq _ (Fin.last n).2
    · exact le_rfl
  linarith

lemma sum_ml {n m : ℕ} (q : ℕ → ℝ) (σ : Fin n → Fin m) :
    ∑ i, machineLoad q σ i = ∑ j : Fin n, q (j : ℕ) := by
  unfold machineLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma makespan_ge_avg {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) (σ : Fin n → Fin m) :
    (∑ j : Fin n, q (j : ℕ)) / m ≤ makespan q σ := by
  rw [div_le_iff₀ (by exact_mod_cast hm), ← sum_ml q σ]
  calc ∑ i, machineLoad q σ i ≤ ∑ _i : Fin m, makespan q σ :=
        Finset.sum_le_sum (fun i _ => ml_le_makespan q σ i)
    _ = makespan q σ * m := by simp [mul_comm]

lemma opt_ge_avg {n m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) :
    (∑ j : Fin n, q (j : ℕ)) / m ≤ optMakespan n m q :=
  le_opt hm q _ (fun σ => makespan_ge_avg hm q σ)

lemma card_lt_fin (n a : ℕ) : (Finset.univ.filter (fun j : Fin n => (j:ℕ) < a)).card = min n a := by
  rw [← Fin.card_filter_val_lt]

lemma card_le_fin (n a : ℕ) : (Finset.univ.filter (fun j : Fin n => (j:ℕ) ≤ a)).card = min n (a+1) := by
  rw [← card_lt_fin]
  congr 1
  ext j
  simp [Nat.lt_succ_iff]

lemma fib_sum_card {n m : ℕ} (σ : Fin n → Fin m) (P : Fin n → Prop) [DecidablePred P] :
    ∑ i : Fin m, (Finset.univ.filter (fun j => σ j = i ∧ P j)).card
      = (Finset.univ.filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := (Finset.univ : Finset (Fin m)))
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext j; simp [and_comm]

lemma ml_ge_card {n m : ℕ} (q : ℕ → ℝ) (σ : Fin n → Fin m) (i : Fin m) (c : ℝ)
    (hq : ∀ j : Fin n, σ j = i → c ≤ q j) (hnn : 0 ≤ c) (hq0 : ∀ j < n, 0 ≤ q j) :
    (Finset.univ.filter (fun j => σ j = i)).card • c ≤ machineLoad q σ i := by
  rw [ml_eq]
  apply Finset.card_nsmul_le_sum
  intro j hj
  exact hq j (by simpa using hj)

/-- Pigeonhole: min load of `k` jobs on `m` machines is at most `q a` when `k + a + 1 = 2m`,
`m ≤ k`. -/
lemma minload_le {m k a : ℕ} (q : ℕ → ℝ) (hmono : ∀ i j, i ≤ j → j < k → q j ≤ q i)
    (hnn : ∀ j < k, 0 ≤ q j) (hmk : m ≤ k) (hka : k + a + 1 = 2 * m)
    (σ : Fin k → Fin m) : ∃ i, machineLoad q σ i ≤ q a := by
  have hak : a < k := by omega
  by_contra hcon
  push_neg at hcon
  have key : ∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun j => σ j = i ∧ True)).card +
      (Finset.univ.filter (fun j : Fin k => σ j = i ∧ (j : ℕ) < a)).card := by
    intro i
    have h1 := hcon i
    rw [ml_eq] at h1
    have hc : (Finset.univ.filter (fun j => σ j = i ∧ True)) = Finset.univ.filter (fun j => σ j = i) := by
      ext j; simp
    rw [hc]
    by_cases h2 : 2 ≤ (Finset.univ.filter (fun j => σ j = i)).card
    · omega
    · have h3 : (Finset.univ.filter (fun j => σ j = i)).card = 0 ∨
          (Finset.univ.filter (fun j => σ j = i)).card = 1 := by omega
      rcases h3 with h3 | h3
      · rw [Finset.card_eq_zero] at h3
        rw [h3] at h1
        simp at h1
        linarith [hnn a hak]
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h3
        rw [hj] at h1
        simp only [Finset.sum_singleton] at h1
        have hja : (j : ℕ) < a := by
          by_contra hh
          push_neg at hh
          have := hmono a j hh j.2
          linarith
        have hmem : j ∈ Finset.univ.filter (fun j : Fin k => σ j = i ∧ (j : ℕ) < a) := by
          have : j ∈ Finset.univ.filter (fun j => σ j = i) := by rw [hj]; simp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
          exact ⟨this, hja⟩
        have := Finset.card_pos.2 ⟨j, hmem⟩
        omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => key i)
  rw [Finset.sum_add_distrib, fib_sum_card σ (fun _ => True), fib_sum_card σ (fun j => (j : ℕ) < a)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hca : (Finset.univ.filter (fun j : Fin k => (j : ℕ) < a)).card ≤ a := by
    rw [card_lt_fin]; exact min_le_right _ _
  simp at hsum
  omega

/-- Lower bound on any assignment of `k+1` jobs. -/
lemma lb_assign {m k a : ℕ} (q : ℕ → ℝ) (hmono : ∀ i j, i ≤ j → j ≤ k → q j ≤ q i)
    (hnn : ∀ j < k + 1, 0 ≤ q j) (hka : k + a + 1 = 2 * m) (hak : a ≤ k)
    (σ : Fin (k+1) → Fin m) :
    ∃ i, q a + q k ≤ machineLoad q σ i ∨ 3 * q k ≤ machineLoad q σ i := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ i : Fin m, (Finset.univ.filter (fun j => σ j = i ∧ True)).card +
      (Finset.univ.filter (fun j : Fin (k+1) => σ j = i ∧ (j : ℕ) ≤ a)).card ≤ 2 := by
    intro i
    obtain ⟨h1, h2⟩ := hcon i
    have hc : (Finset.univ.filter (fun j => σ j = i ∧ True)) = Finset.univ.filter (fun j => σ j = i) := by
      ext j; simp
    rw [hc]
    have hqk : 0 ≤ q k := hnn k (by omega)
    have h3 : (Finset.univ.filter (fun j => σ j = i)).card ≤ 2 := by
      by_contra h
      push_neg at h
      have := ml_ge_card q σ i (q k) (fun j _ => hmono j k (by omega) le_rfl) hqk hnn
      have h4 : (3 : ℕ) • q k ≤ (Finset.univ.filter (fun j => σ j = i)).card • q k :=
        nsmul_le_nsmul_left hqk h
      simp only [nsmul_eq_mul] at h4 this
      push_cast at h4 this
      linarith
    have hsub : (Finset.univ.filter (fun j : Fin (k+1) => σ j = i ∧ (j : ℕ) ≤ a)).card ≤
        (Finset.univ.filter (fun j => σ j = i)).card := by
      apply Finset.card_le_card
      intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.1
    have h5 : 2 ≤ (Finset.univ.filter (fun j => σ j = i)).card →
        (Finset.univ.filter (fun j : Fin (k+1) => σ j = i ∧ (j : ℕ) ≤ a)).card = 0 := by
      intro h2'
      by_contra hne
      obtain ⟨j0, hj0⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj0
      have hcard : 1 < (Finset.univ.filter (fun j => σ j = i)).card := by omega
      obtain ⟨j1, hj1, hne1⟩ := Finset.exists_mem_ne hcard j0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1
      have hsub2 : ({j0, j1} : Finset (Fin (k+1))) ⊆ Finset.univ.filter (fun j => σ j = i) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact hj0.1
        · exact hj1
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (f := fun j : Fin (k+1) => q (j : ℕ)) (fun j _ _ => hnn j j.2)
      rw [Finset.sum_pair (Ne.symm hne1)] at this
      rw [ml_eq] at h1
      have e3 := hmono (j0 : ℕ) a hj0.2 (by omega)
      have e4 := hmono (j1 : ℕ) k (by have := j1.2; omega) le_rfl
      linarith
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => key i)
  rw [Finset.sum_add_distrib, fib_sum_card σ (fun _ => True), fib_sum_card σ (fun j => (j : ℕ) ≤ a)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [card_le_fin] at hsum
  simp at hsum
  omega

lemma ls_step {m M k : ℕ} (hm : 0 < m) (q : ℕ → ℝ)
    (hnn : ∀ j, j < M → 0 ≤ q j) (hmono : ∀ i j, i ≤ j → j < M → q j ≤ q i) (hk : k < M)
    (i0 : Fin m) (h0 : ∀ i, lsLoads m q k i0 ≤ lsLoads m q k i) :
    lsLoads m q k i0 + q k ≤ (4/3 - 1/(3*(m:ℝ))) * optMakespan (k+1) m q := by
  have hnn' : ∀ j < k+1, 0 ≤ q j := fun j hj => hnn j (by omega)
  have hO0 : 0 ≤ optMakespan (k+1) m q := opt_nonneg hm q hnn'
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 1 ≤ 4/3 - 1/(3*(m:ℝ)) := by
    have : 1/(3*(m:ℝ)) ≤ 1/3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  obtain ⟨σ, hσ⟩ := ls_sigma hm q k
  have hqk0 : 0 ≤ q k := hnn k hk
  by_cases hc : q k ≤ optMakespan (k+1) m q / 3
  · have h1 : (m:ℝ) * lsLoads m q k i0 ≤ ∑ j ∈ Finset.range k, q j := by
      rw [← ls_sum hm q k]
      calc (m:ℝ) * _ = ∑ _i : Fin m, lsLoads m q k i0 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => h0 i)
    have h2 := opt_ge_avg (n := k+1) hm q
    rw [Fin.sum_univ_eq_sum_range (fun j => q j) (k+1), Finset.sum_range_succ,
      div_le_iff₀ hmR] at h2
    have hmρ : (m:ℝ) * (4/3 - 1/(3*(m:ℝ))) = (4*m - 1)/3 := by
      field_simp
    have h3 : (m:ℝ) * (lsLoads m q k i0 + q k) ≤ (m:ℝ) * ((4/3 - 1/(3*(m:ℝ))) * optMakespan (k+1) m q) := by
      have h4 := mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ m - 1)
      calc (m:ℝ) * (lsLoads m q k i0 + q k) ≤ optMakespan (k+1) m q * m + (m - 1) * q k := by
            nlinarith
        _ ≤ _ := by
            have : (m:ℝ) * ((4/3 - 1/(3*(m:ℝ))) * optMakespan (k+1) m q)
                = (4*m - 1)/3 * optMakespan (k+1) m q := by rw [← mul_assoc, hmρ]
            rw [this]; nlinarith
    exact le_of_mul_le_mul_left h3 hmR
  · push_neg at hc
    have hfin : lsLoads m q k i0 + q k ≤ optMakespan (k+1) m q := by
      by_cases hkm : k < m
      · -- an empty machine
        have : ∃ i1 : Fin m, ∀ j, σ j ≠ i1 := by
          by_contra hcon
          push_neg at hcon
          have hsurj : Function.Surjective σ := hcon
          have := Fintype.card_le_of_surjective σ hsurj
          simp only [Fintype.card_fin] at this; omega
        obtain ⟨i1, hi1⟩ := this
        have hz : lsLoads m q k i1 = 0 := by
          rw [hσ]; unfold machineLoad
          exact Finset.sum_eq_zero (fun j _ => by simp [hi1 j])
        have hl : lsLoads m q k i0 ≤ 0 := hz ▸ h0 i1
        have : q k ≤ optMakespan (k+1) m q := by
          apply le_opt hm q
          intro τ
          refine le_trans ?_ (ml_le_makespan q τ (τ (Fin.last k)))
          rw [ml_eq]
          have := Finset.single_le_sum (f := fun j : Fin (k+1) => q (j : ℕ))
            (s := Finset.univ.filter (fun j => τ j = τ (Fin.last k)))
            (fun j _ => hnn' j j.2) (a := Fin.last k) (by simp)
          simpa using this
        linarith
      · by_cases hk2 : 2 * m ≤ k
        · exfalso
          have : 3 * q k ≤ optMakespan (k+1) m q := by
            apply le_opt hm q
            intro τ
            obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
              (s := (Finset.univ : Finset (Fin (k+1)))) (t := (Finset.univ : Finset (Fin m)))
              (f := τ) (n := 2) (fun _ _ => Finset.mem_univ _) (by simp; omega)
            have := ml_ge_card q τ i (q k) (fun j _ => hmono j k (by have := j.2; omega) hk)
              hqk0 hnn'
            have h4 : (3 : ℕ) • q k ≤ (Finset.univ.filter (fun j => τ j = i)).card • q k :=
              nsmul_le_nsmul_left hqk0 (Nat.succ_le_of_lt (by simpa using hi))
            simp only [nsmul_eq_mul] at h4 this
            push_cast at h4 this
            linarith [ml_le_makespan q τ i]
          linarith
        · push_neg at hkm hk2
          have hmk : m ≤ k := by omega
          obtain ⟨i, hi⟩ := minload_le (m := m) (k := k) (a := 2*m-1-k) q
            (fun i j hij hj => hmono i j hij (by omega)) (fun j hj => hnn j (by omega)) hmk
            (by omega) σ
          have hl : lsLoads m q k i0 ≤ q (2*m-1-k) := by
            refine le_trans (h0 i) ?_
            rw [hσ]; exact hi
          have hlb : min (q (2*m-1-k) + q k) (3 * q k) ≤ optMakespan (k+1) m q := by
            apply le_opt hm q
            intro τ
            obtain ⟨i, hi⟩ := lb_assign (m := m) (k := k) (a := 2*m-1-k) q
              (fun i j hij hj => hmono i j hij (by omega)) hnn' (by omega) (by omega) τ
            refine le_trans ?_ (ml_le_makespan q τ i)
            rcases hi with hi | hi
            · exact le_trans (min_le_left _ _) hi
            · exact le_trans (min_le_right _ _) hi
          rcases min_le_iff.1 hlb with h | h
          · linarith
          · linarith
    nlinarith

theorem graham_core {M m : ℕ} (hm : 0 < m) (q : ℕ → ℝ)
    (hq_nonneg : ∀ k, k < M → 0 ≤ q k)
    (hq_noninc : ∀ k k', k ≤ k' → k' < M → q k' ≤ q k) :
    listMakespan M m q ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan M m q := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 0 ≤ 4/3 - 1/(3*(m:ℝ)) := by
    have : 1/(3*(m:ℝ)) ≤ 1/3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have key : ∀ k, k ≤ M → ∀ i, lsLoads m q k i ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan k m q := by
    intro k
    induction k with
    | zero =>
      intro _ i
      simp only [lsLoads]
      exact mul_nonneg hρ (opt_nonneg hm q (fun j hj => by omega))
    | succ k ih =>
      intro hk i
      obtain ⟨i0, h0, hmin⟩ := fa_spec hm (lsLoads m q k)
      rw [ls_succ q k i0 h0]
      have hmono := opt_mono (n := k) hm q (fun j hj => hq_nonneg j (by omega))
      by_cases hi : i = i0
      · subst hi
        simp only [if_true]
        exact ls_step hm q hq_nonneg hq_noninc (by omega) i hmin
      · simp only [hi, if_false]
        exact (ih (by omega) i).trans (mul_le_mul_of_nonneg_left hmono hρ)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ciSup_le (fun i => key M le_rfl i)




def ch {α : Type*} (B : ℕ) (L : List α) : List (List α) :=
  if h : L = [] ∨ B = 0 then (if L = [] then [] else [L]) else (L.take B) :: ch B (L.drop B)
termination_by L.length
decreasing_by
  push_neg at h
  have := List.length_pos_of_ne_nil h.1
  simp only [List.length_drop]
  omega

lemma ch_nil {α : Type*} (B : ℕ) : ch B ([] : List α) = [] := by
  rw [ch]; simp

lemma ch_cons {α : Type*} {B : ℕ} (hB : 0 < B) (L : List α) (hL : L ≠ []) :
    ch B L = L.take B :: ch B (L.drop B) := by
  rw [ch]; simp [hL, Nat.pos_iff_ne_zero.1 hB]

lemma go_spec {α : Type*} {B : ℕ} (hB : 0 < B) : ∀ (xs : List α) (a1 : Array α) (a2 : Array (List α)),
    0 < a1.size → a1.size ≤ B →
    List.toChunks.go B xs a1 a2 = a2.toList ++ ch B (a1.toList ++ xs) := by
  intro xs
  induction xs with
  | nil =>
    intro a1 a2 h1 h2
    simp only [List.toChunks.go, List.append_nil]
    have hne : a1.toList ≠ [] := by
      intro h; have h3 : a1.toList.length = 0 := by rw [h]; rfl
      rw [Array.length_toList] at h3; omega
    rw [ch_cons hB _ hne]
    have e1 : a1.toList.take B = a1.toList := List.take_of_length_le (by simpa using h2)
    have e2 : a1.toList.drop B = [] := List.drop_of_length_le (by simpa using h2)
    rw [e1, e2, ch_nil]; simp
  | cons x xs ih =>
    intro a1 a2 h1 h2
    simp only [List.toChunks.go]
    by_cases hs : a1.size = B
    · have hb : (a1.size == B) = true := by simpa using hs
      rw [if_pos hb, ih ((Array.mkEmpty B).push x) (a2.push a1.toList) (by simp) (by simp <;> omega)]
      have hne : a1.toList ++ x :: xs ≠ [] := by simp
      rw [ch_cons hB _ hne]
      have e1 : (a1.toList ++ x :: xs).take B = a1.toList := by
        rw [List.take_append_of_le_length (by simp [hs])]
        exact List.take_of_length_le (by simp [hs])
      have e2 : (a1.toList ++ x :: xs).drop B = x :: xs := by
        have : a1.toList.length = B := by simp [hs]
        rw [← this, List.drop_left]
      rw [e1, e2]; simp
    · have hb : ¬ (a1.size == B) = true := by simpa using hs
      rw [if_neg hb, ih (a1.push x) a2 (by simp) (by simp <;> omega)]
      simp

lemma toChunks_eq {α : Type*} {B : ℕ} (hB : 0 < B) (L : List α) : L.toChunks B = ch B L := by
  cases L with
  | nil => simp [List.toChunks, ch_nil]
  | cons x xs =>
    have : List.toChunks B (x :: xs) = List.toChunks.go B xs #[x] #[] := by
      unfold List.toChunks
      split <;> simp_all
    rw [this, go_spec hB xs #[x] #[] (by simp) (by simp; omega)]
    simp

lemma ch_flatten {α : Type*} {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (L : List α), L.length = n →
    (ch B L).flatten = L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL
    by_cases hne : L = []
    · subst hne; simp [ch_nil]
    · rw [ch_cons hB L hne]
      have hlen : (L.drop B).length < n := by
        have := List.length_pos_of_ne_nil hne
        simp only [List.length_drop]; omega
      simp only [List.flatten_cons]
      rw [ih _ hlen _ rfl, List.take_append_drop]

lemma ch_mem {α : Type*} {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (L : List α), L.length = n →
    ∀ c ∈ ch B L, c ≠ [] ∧ c.length ≤ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL c hc
    by_cases hne : L = []
    · subst hne; simp [ch_nil] at hc
    · rw [ch_cons hB L hne] at hc
      have hlen : (L.drop B).length < n := by
        have := List.length_pos_of_ne_nil hne
        simp only [List.length_drop]; omega
      rcases List.mem_cons.1 hc with rfl | hc
      · refine ⟨?_, by simp⟩
        intro h
        rcases List.take_eq_nil_iff.1 h with h | h
        · omega
        · exact hne h
      · exact ih _ hlen _ rfl c hc

lemma ch_get {α : Type*} {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (L : List α), L.length = n →
    ∀ k (h : k < (ch B L).length), (ch B L)[k] = (L.drop (k * B)).take B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL k h
    by_cases hne : L = []
    · subst hne; simp [ch_nil] at h
    · have hpos := List.length_pos_of_ne_nil hne
      have hlen : (L.drop B).length < n := by
        simp only [List.length_drop]; omega
      cases k with
      | zero => simp [ch_cons hB L hne]
      | succ k =>
        have h' : k < (ch B (L.drop B)).length := by
          rw [ch_cons hB L hne] at h; simpa using h
        have := ih _ hlen _ rfl k h'
        simp only [ch_cons hB L hne, List.getElem_cons_succ]
        rw [this, List.drop_drop]
        congr 3
        ring



lemma blpt_eq {n : ℕ} {B : ℕ} (hB : 0 < B) (l : List (Fin n)) :
    blptBatches B l = (ch B l).map List.toFinset := by
  unfold blptBatches; rw [toChunks_eq hB]

lemma sorted_get {n : ℕ} (p : Fin n → ℝ) (l : List (Fin n))
    (hs : l.Pairwise (fun a b => p b ≤ p a)) {i j : ℕ} (hij : i ≤ j) (hj : j < l.length) :
    p (l[j]'hj) ≤ p (l[i]'(lt_of_le_of_lt hij hj)) := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_rfl
  · exact List.pairwise_iff_getElem.1 hs i j (lt_of_le_of_lt hij hj) hj h

lemma blpt_isBatching {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (l : List (Fin n))
    (hl : IsLPTList p l) : IsBatching n B (blptBatches B l) := by
  have hnd : l.Nodup := hl.1.nodup_iff.2 (List.nodup_finRange n)
  have hfl := ch_flatten hB _ l rfl
  rw [blpt_eq hB]
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hP
    obtain ⟨hne, hlen⟩ := ch_mem hB _ l rfl c hc
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil c hne
      exact ⟨x, List.mem_toFinset.2 hx⟩
    · exact (List.toFinset_card_le c).trans hlen
  · rw [hfl.symm] at hnd
    have := (List.nodup_flatten.1 hnd).2
    refine List.Pairwise.map _ ?_ this
    intro a b hab
    exact List.disjoint_toFinset_iff_disjoint.2 hab
  · intro j
    have hj : j ∈ l := hl.1.mem_iff.2 (List.mem_finRange j)
    rw [← hfl] at hj
    obtain ⟨c, hc, hjc⟩ := List.mem_flatten.1 hj
    exact ⟨c.toFinset, List.mem_map.2 ⟨c, hc, rfl⟩, List.mem_toFinset.2 hjc⟩

lemma blpt_time {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (l : List (Fin n))
    (hl : IsLPTList p l) (k : ℕ) (hk : k < (blptBatches B l).length) :
    ∃ h : k * B < l.length, BurnInBatch.ListSched.batchTimes p (blptBatches B l) k = p (l[k * B]'h) := by
  have hk' : k < (ch B l).length := by rw [blpt_eq hB] at hk; simpa using hk
  have hget := ch_get hB _ l rfl k hk'
  have hmem : (ch B l)[k] ∈ ch B l := List.getElem_mem hk'
  obtain ⟨hne, -⟩ := ch_mem hB _ l rfl _ hmem
  rw [hget] at hne
  have hdne : l.drop (k * B) ≠ [] := fun h => hne (by rw [h]; simp)
  have hlt : k * B < l.length := by
    by_contra h
    exact hdne (List.drop_of_length_le (by omega))
  refine ⟨hlt, ?_⟩
  have hbt : BurnInBatch.ListSched.batchTimes p (blptBatches B l) k
      = BurnInBatch.ListSched.batchTime p (((l.drop (k * B)).take B).toFinset) := by
    unfold BurnInBatch.ListSched.batchTimes
    rw [dif_pos hk]
    simp only [blpt_eq hB, List.getElem_map, hget]
  rw [hbt]
  have hne' : ((l.drop (k * B)).take B).toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨x, List.mem_toFinset.2 hx⟩
  unfold BurnInBatch.ListSched.batchTime
  rw [dif_pos hne']
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rw [List.mem_toFinset] at hx
    have hx2 : x ∈ l.drop (k * B) := List.mem_of_mem_take hx
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx2
    simp only [List.getElem_drop]
    have := sorted_get p l hl.2 (Nat.le_add_right (k * B) t) (by simp at ht; omega)
    simpa using this
  · apply Finset.le_sup' p
    rw [List.mem_toFinset]
    have hpos : 0 < ((l.drop (k * B)).take B).length := List.length_pos_of_ne_nil hne
    have h0 : ((l.drop (k * B)).take B)[0] = l[k * B] := by simp
    rw [← h0]
    exact List.getElem_mem hpos

lemma blpt_top {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (l : List (Fin n))
    (hl : IsLPTList p l) (k : ℕ) (hlt : k * B < l.length) :
    (l.take (k * B + 1)).toFinset.card = k * B + 1 ∧
    ∀ y ∈ (l.take (k * B + 1)).toFinset, p (l[k * B]'hlt) ≤ p y := by
  have hnd : l.Nodup := hl.1.nodup_iff.2 (List.nodup_finRange n)
  constructor
  · rw [List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _))]
    simp; omega
  · intro y hy
    rw [List.mem_toFinset] at hy
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hy
    simp only [List.getElem_take]
    simp only [List.length_take] at ht
    exact sorted_get p l hl.2 (by omega) hlt



lemma batchTime_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (P : Finset (Fin n)) :
    0 ≤ BurnInBatch.ListSched.batchTime p P := by
  unfold BurnInBatch.ListSched.batchTime
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    exact (hp x).le.trans (Finset.le_sup' p hx)
  · exact le_rfl

lemma batchTimes_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (S : List (Finset (Fin n)))
    (k : ℕ) : 0 ≤ BurnInBatch.ListSched.batchTimes p S k := by
  unfold BurnInBatch.ListSched.batchTimes
  split_ifs
  · exact batchTime_nonneg p hp _
  · exact le_rfl

lemma dom_set {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (l : List (Fin n))
    (hl : IsLPTList p l) (S : List (Finset (Fin n))) (hS : IsBatching n B S)
    (k : ℕ) (hk : k < (blptBatches B l).length) :
    ∃ A : Finset (Fin S.length), k < A.card ∧
      ∀ t ∈ A, BurnInBatch.ListSched.batchTimes p (blptBatches B l) k ≤
        BurnInBatch.ListSched.batchTimes p S t := by
  classical
  obtain ⟨hlt, hTk⟩ := blpt_time hB p l hl k hk
  obtain ⟨hcard, hge⟩ := blpt_top hB p l hl k hlt
  have hf : ∀ j : Fin n, ∃ t : Fin S.length, j ∈ S.get t := by
    intro j
    obtain ⟨P, hP, hjP⟩ := hS.2.2 j
    obtain ⟨t, rfl⟩ := List.mem_iff_get.1 hP
    exact ⟨t, hjP⟩
  choose f hf using hf
  set Top := (l.take (k * B + 1)).toFinset with hTop
  refine ⟨Top.image f, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have h1 := Finset.card_le_mul_card_image (f := f) Top B (by
      intro t ht
      calc (Top.filter (fun x => f x = t)).card ≤ (S.get t).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [← hx.2]; exact hf x
        _ ≤ B := (hS.1 _ (List.get_mem S t)).2)
    have h2 : B * (Top.image f).card ≤ B * k := Nat.mul_le_mul_left B hcon
    rw [hcard] at h1
    nlinarith
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ht
    rw [hTk]
    refine (hge y hy).trans ?_
    unfold BurnInBatch.ListSched.batchTimes
    rw [dif_pos (f y).2]
    unfold BurnInBatch.ListSched.batchTime
    have hy' : y ∈ S[(f y : ℕ)] := by simpa using hf y
    have hne : S[(f y : ℕ)].Nonempty := ⟨y, hy'⟩
    rw [dif_pos hne]
    exact Finset.le_sup' p hy'

lemma dom_inj {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (l : List (Fin n))
    (hl : IsLPTList p l) (S : List (Finset (Fin n))) (hS : IsBatching n B S) :
    ∀ k ≤ (blptBatches B l).length, ∃ φ : ℕ → ℕ,
      (∀ i < k, φ i < S.length ∧ BurnInBatch.ListSched.batchTimes p (blptBatches B l) i ≤
        BurnInBatch.ListSched.batchTimes p S (φ i)) ∧
      (∀ i < k, ∀ j < k, φ i = φ j → i = j) := by
  classical
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => 0, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨φ, h1, h2⟩ := ih (by omega)
    obtain ⟨A, hA, hAt⟩ := dom_set hB p hp l hl S hS k (by omega)
    have hcardA' : (A.image (fun t : Fin S.length => (t : ℕ))).card = A.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have hI : ((Finset.range k).image φ).card ≤ k :=
      (Finset.card_image_le).trans (by simp)
    have : ∃ t' ∈ A.image (fun t : Fin S.length => (t : ℕ)), t' ∉ (Finset.range k).image φ := by
      by_contra hcon
      push_neg at hcon
      have := Finset.card_le_card (show A.image (fun t : Fin S.length => (t : ℕ)) ⊆ (Finset.range k).image φ from hcon)
      omega
    obtain ⟨t', ht'A, ht'I⟩ := this
    obtain ⟨t, htA, htt⟩ := Finset.mem_image.1 ht'A
    have htt' : t' = (t : ℕ) := htt.symm
    subst htt'
    clear ht'A htt
    refine ⟨fun i => if i = k then (t : ℕ) else φ i, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik
        simp only [if_true]
        exact ⟨t.2, hAt t htA⟩
      · simp only [hik, if_false]
        exact h1 i (by omega)
    · intro i hi j hj hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · omega
      · subst hik
        simp only [if_true, hjk, if_false] at hij
        exfalso; apply ht'I
        rw [Finset.mem_image]; exact ⟨j, Finset.mem_range.2 (by omega), hij.symm⟩
      · subst hjk
        simp only [if_true, hik, if_false] at hij
        exfalso; apply ht'I
        rw [Finset.mem_image]; exact ⟨i, Finset.mem_range.2 (by omega), hij⟩
      · simp only [hik, hjk, if_false] at hij
        exact h2 i (by omega) j (by omega) hij

lemma dominate {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (l : List (Fin n)) (hl : IsLPTList p l) (S : List (Finset (Fin n))) (hS : IsBatching n B S) :
    optMakespan (blptBatches B l).length m (BurnInBatch.ListSched.batchTimes p (blptBatches B l))
      ≤ optMakespan S.length m (BurnInBatch.ListSched.batchTimes p S) := by
  set K := (blptBatches B l).length with hK
  set T := BurnInBatch.ListSched.batchTimes p (blptBatches B l) with hT
  have hTnn : ∀ j < K, 0 ≤ T j := fun j _ => batchTimes_nonneg p hp _ j
  have hSnn : ∀ j < S.length, 0 ≤ BurnInBatch.ListSched.batchTimes p S j :=
    fun j _ => batchTimes_nonneg p hp _ j
  apply le_opt hm
  intro σ
  obtain ⟨φ, h1, h2⟩ := dom_inj hB p hp l hl S hS K le_rfl
  let ψ : Fin K → Fin S.length := fun i => ⟨φ i, (h1 i i.2).1⟩
  have hψ : Function.Injective ψ := by
    intro i j hij
    apply Fin.ext
    exact h2 i i.2 j j.2 (by simpa [ψ] using congrArg Fin.val hij)
  refine le_trans (opt_le hm T hTnn (fun i => σ (ψ i))) ?_
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply ciSup_le
  intro i
  refine le_trans ?_ (ml_le_makespan _ σ i)
  unfold machineLoad
  calc ∑ j : Fin K, (if σ (ψ j) = i then T j else 0)
      ≤ ∑ j : Fin K, (if σ (ψ j) = i then BurnInBatch.ListSched.batchTimes p S (ψ j) else 0) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact (h1 j j.2).2
        · exact le_rfl
    _ = ∑ t ∈ Finset.univ.image ψ, (if σ t = i then BurnInBatch.ListSched.batchTimes p S t else 0) := by
        rw [Finset.sum_image (fun x _ y _ h => hψ h)]
    _ ≤ ∑ t : Fin S.length, (if σ t = i then BurnInBatch.ListSched.batchTimes p S t else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro t _ _
        split_ifs
        · exact batchTimes_nonneg p hp _ _
        · exact le_rfl



theorem reduction_core {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    optBatchMakespan n m B p =
      optMakespan (blptBatches B l).length m (BurnInBatch.ListSched.batchTimes p (blptBatches B l)) := by
  apply le_antisymm
  · unfold optBatchMakespan
    exact ciInf_le (f := fun S : {S : List (Finset (Fin n)) // IsBatching n B S} =>
        optMakespan S.1.length m (BurnInBatch.ListSched.batchTimes p S.1))
      ⟨0, by
        rintro _ ⟨S, rfl⟩
        exact opt_nonneg hm _ (fun j _ => batchTimes_nonneg p hp _ j)⟩
      ⟨blptBatches B l, blpt_isBatching hB p l hl⟩
  · unfold optBatchMakespan
    haveI : Nonempty {S : List (Finset (Fin n)) // IsBatching n B S} :=
      ⟨⟨blptBatches B l, blpt_isBatching hB p l hl⟩⟩
    exact le_ciInf (fun S => dominate hm hB p hp l hl S.1 S.2)

theorem prop2_core {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    ∃ S : List (Finset (Fin n)), ∃ σ : Fin S.length → Fin m,
      IsBatching n B S ∧ S.Perm (blptBatches B l) ∧
      makespan (BurnInBatch.ListSched.batchTimes p S) σ = optBatchMakespan n m B p := by
  refine ⟨blptBatches B l, ?_⟩
  haveI : Nonempty (Fin (blptBatches B l).length → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  obtain ⟨σ, hσ⟩ := exists_eq_ciInf_of_finite
    (f := fun σ : Fin (blptBatches B l).length → Fin m =>
      makespan (BurnInBatch.ListSched.batchTimes p (blptBatches B l)) σ)
  refine ⟨σ, blpt_isBatching hB p l hl, List.Perm.refl _, ?_⟩
  rw [reduction_core hm hB p hp l hl]
  exact hσ

lemma bl_times {n B : ℕ} (hB : 0 < B) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (l : List (Fin n))
    (hl : IsLPTList p l) (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    BurnInBatch.ListSched.batchTimes p bl = BurnInBatch.ListSched.batchTimes p (blptBatches B l) := by
  obtain ⟨hperm, hsort⟩ := hbl
  have hlen := hperm.length_eq
  have hmap : (bl.map (BurnInBatch.ListSched.batchTime p)) =
      ((blptBatches B l).map (BurnInBatch.ListSched.batchTime p)) := by
    have H1 : (bl.map (BurnInBatch.ListSched.batchTime p)).Pairwise (fun a b : ℝ => b ≤ a) :=
      List.Pairwise.map _ (fun P Q h => h) hsort
    have H2 : ((blptBatches B l).map (BurnInBatch.ListSched.batchTime p)).Pairwise
        (fun a b : ℝ => b ≤ a) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.length_map] at hi hj
      simp only [List.getElem_map]
      obtain ⟨h1, e1⟩ := blpt_time hB p l hl i hi
      obtain ⟨h2, e2⟩ := blpt_time hB p l hl j hj
      have g1 : BurnInBatch.ListSched.batchTimes p (blptBatches B l) i =
          BurnInBatch.ListSched.batchTime p ((blptBatches B l)[i]) := by
        unfold BurnInBatch.ListSched.batchTimes; rw [dif_pos hi]
      have g2 : BurnInBatch.ListSched.batchTimes p (blptBatches B l) j =
          BurnInBatch.ListSched.batchTime p ((blptBatches B l)[j]) := by
        unfold BurnInBatch.ListSched.batchTimes; rw [dif_pos hj]
      rw [← g1, ← g2, e1, e2]
      exact sorted_get p l hl.2 (Nat.mul_le_mul_right B hij.le) h2
    exact List.Perm.eq_of_pairwise (fun a _ b _ h1 h2 => le_antisymm h2 h1) H1 H2 (hperm.map _)
  funext k
  unfold BurnInBatch.ListSched.batchTimes
  by_cases hk : k < bl.length
  · have hk2 : k < (blptBatches B l).length := hlen ▸ hk
    rw [dif_pos hk, dif_pos hk2]
    have := congrArg (fun L => L[k]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk2] at this
    simpa using this
  · have hk2 : ¬ k < (blptBatches B l).length := hlen ▸ hk
    rw [dif_neg hk, dif_neg hk2]

theorem prop3_core {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l)
    (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    blptMakespan m p bl ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optBatchMakespan n m B p := by
  have hlen := hbl.1.length_eq
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 0 ≤ 4/3 - 1/(3*(m:ℝ)) := by
    have : 1/(3*(m:ℝ)) ≤ 1/3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  unfold blptMakespan
  rw [bl_times hB p hp l hl bl hbl, hlen, reduction_core hm hB p hp l hl]
  apply graham_core hm
  · intro k _; exact batchTimes_nonneg p hp _ k
  · intro k k' hkk hk'
    obtain ⟨h1, e1⟩ := blpt_time hB p l hl k (by omega)
    obtain ⟨h2, e2⟩ := blpt_time hB p l hl k' hk'
    rw [e1, e2]
    exact sorted_get p l hl.2 (Nat.mul_le_mul_right B hkk) h2


end BurnInBatch.BatchLPT

open BurnInBatch.BatchLPT
open NumStochOpt.ListScheduling

theorem solution {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    optBatchMakespan n m B p =
      optMakespan (blptBatches B l).length m (BurnInBatch.ListSched.batchTimes p (blptBatches B l)) := by
  exact reduction_core hm hB p hp l hl
