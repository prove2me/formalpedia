-- Prove2me | solution 1 for BurnInBatch.BatchLPT.graham_lpt_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:37:25.450167+00:00
-- url     : https://prove2.me/submissions/719a7c8c-4505-4a80-a127-95d81373c6a2

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan



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

end BurnInBatch.BatchLPT

open BurnInBatch.BatchLPT
open NumStochOpt.ListScheduling

theorem solution {M m : ℕ} (hm : 0 < m) (q : ℕ → ℝ)
    (hq_nonneg : ∀ k, k < M → 0 ≤ q k)
    (hq_noninc : ∀ k k', k ≤ k' → k' < M → q k' ≤ q k) :
    listMakespan M m q ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan M m q := by
  exact graham_core hm q hq_nonneg hq_noninc
