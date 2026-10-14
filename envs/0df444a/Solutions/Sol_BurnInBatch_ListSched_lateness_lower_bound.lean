-- Prove2me | solution 1 for BurnInBatch.ListSched.lateness_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:48:01.034297+00:00
-- url     : https://prove2.me/submissions/ddf93e76-2cfe-4d2f-8630-1175b239af5b

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model



namespace BurnInBatch.ListSched

open NumStochOpt.ListScheduling

lemma fa_spec {m : ℕ} (hm : 0 < m) (ℓ : Fin m → ℝ) :
    ∃ i0, firstAvailable ℓ = some i0 ∧ ∀ k, ℓ i0 ≤ ℓ k := by
  have hne : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
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
  have : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
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
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
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


lemma batchTime_nonneg {n : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j) (P : Finset (Fin n)) :
    0 ≤ batchTime p P := by
  unfold batchTime
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hp j).le.trans (Finset.le_sup' p hj)
  · exact le_rfl

lemma le_batchTime {n : ℕ} {p : Fin n → ℝ} {P : Finset (Fin n)} {j : Fin n} (hj : j ∈ P) :
    p j ≤ batchTime p P := by
  unfold batchTime
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.le_sup' p hj

lemma batchTime_le {n : ℕ} {p : Fin n → ℝ} {P : Finset (Fin n)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ P, p j ≤ c) : batchTime p P ≤ c := by
  unfold batchTime
  split_ifs with hP
  · exact Finset.sup'_le _ _ h
  · exact hc

lemma batchTime_le_sum {n : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j) (P : Finset (Fin n)) :
    batchTime p P ≤ ∑ j ∈ P, p j := by
  apply batchTime_le (Finset.sum_nonneg (fun j _ => (hp j).le))
  intro j hj
  exact Finset.single_le_sum (f := p) (fun i _ => (hp i).le) hj

lemma sum_le_card_batchTime {n : ℕ} {p : Fin n → ℝ} (P : Finset (Fin n)) :
    ∑ j ∈ P, p j ≤ P.card * batchTime p P := by
  have := Finset.sum_le_card_nsmul P p (batchTime p P) (fun j hj => le_batchTime hj)
  simpa [nsmul_eq_mul] using this

lemma batchTimes_nonneg {n : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j)
    (S : List (Finset (Fin n))) (k : ℕ) : 0 ≤ batchTimes p S k := by
  unfold batchTimes
  split_ifs
  · exact batchTime_nonneg hp _
  · exact le_rfl

lemma mem_foldr_union {α : Type*} [DecidableEq α] (S : List (Finset α)) (j : α) :
    j ∈ S.foldr (· ∪ ·) ∅ ↔ ∃ P ∈ S, j ∈ P := by
  induction S with
  | nil => simp
  | cons P S ih => simp [ih]

lemma disjoint_foldr {α : Type*} [DecidableEq α] (S : List (Finset α)) (P : Finset α)
    (h : ∀ Q ∈ S, Disjoint P Q) : Disjoint P (S.foldr (· ∪ ·) ∅) := by
  induction S with
  | nil => simp
  | cons Q S ih =>
    simp only [List.foldr_cons]
    exact Finset.disjoint_union_right.2 ⟨h Q (by simp), ih (fun R hR => h R (by simp [hR]))⟩

lemma sum_foldr_union {α : Type*} [DecidableEq α] (S : List (Finset α))
    (hS : S.Pairwise Disjoint) (f : α → ℝ) :
    ∑ j ∈ S.foldr (· ∪ ·) ∅, f j = (S.map (fun P => ∑ j ∈ P, f j)).sum := by
  induction S with
  | nil => simp
  | cons P S ih =>
    rw [List.pairwise_cons] at hS
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_union (disjoint_foldr S P hS.1), ih hS.2]

lemma sum_fin_getElem {α : Type*} (S : List α) (F : α → ℝ) :
    ∑ i : Fin S.length, F S[i] = (S.map F).sum := by
  calc ∑ i : Fin S.length, F S[i]
      = (List.ofFn (fun i : Fin S.length => F S[i])).sum := by rw [List.sum_ofFn]
    _ = ((List.ofFn (fun i : Fin S.length => S[i])).map F).sum := by
        rw [List.map_ofFn]; rfl
    _ = (S.map F).sum := by simp

lemma exists_valid {n : ℕ} (B : ℕ) (hB : 0 < B) (J : Finset (Fin n)) :
    ∃ S, ValidBatching B J S := by
  refine ⟨J.toList.map (fun j => ({j} : Finset (Fin n))), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hP
    exact ⟨Finset.singleton_nonempty _, by rw [Finset.card_singleton]; exact hB⟩
  · rw [List.pairwise_map]
    exact J.nodup_toList.imp (fun h => Finset.disjoint_singleton.2 h)
  · ext j
    rw [mem_foldr_union]
    simp

lemma sum_batchTimes {n : ℕ} (p : Fin n → ℝ) (S : List (Finset (Fin n))) :
    ∑ k : Fin S.length, batchTimes p S k = (S.map (batchTime p)).sum := by
  rw [← sum_fin_getElem S (batchTime p)]
  apply Finset.sum_congr rfl
  intro k _
  unfold batchTimes
  rw [dif_pos k.2]
  rfl

lemma volume_valid {n : ℕ} (p : Fin n → ℝ) (B m : ℕ) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) (J : Finset (Fin n)) (S : List (Finset (Fin n)))
    (hS : ValidBatching B J S) :
    (∑ j ∈ J, p j) / ((m : ℝ) * (B : ℝ)) ≤
      optMakespan S.length m (batchTimes p S) := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hBR : (0:ℝ) < B := by exact_mod_cast hB
  have hsum : ∑ j ∈ J, p j ≤ B * (S.map (batchTime p)).sum := by
    rw [← h3, sum_foldr_union S h2]
    have : ∀ (T : List (Finset (Fin n))), (∀ P ∈ T, P.card ≤ B) →
        (T.map (fun P => ∑ j ∈ P, p j)).sum ≤ B * (T.map (batchTime p)).sum := by
      intro T
      induction T with
      | nil => intro _; simp
      | cons P T ih =>
        intro hT
        simp only [List.map_cons, List.sum_cons]
        have hP := hT P (by simp)
        have := ih (fun Q hQ => hT Q (by simp [hQ]))
        have h4 := sum_le_card_batchTime (p := p) P
        have h5 : (P.card : ℝ) * batchTime p P ≤ B * batchTime p P :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hP) (batchTime_nonneg hp _)
        nlinarith
    exact this S (fun P hP => (h1 P hP).2)
  apply le_opt hm
  intro σ
  have := makespan_ge_avg hm (batchTimes p S) σ
  rw [sum_batchTimes] at this
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hmR] at this
  nlinarith

lemma cmax_ge_vol {n : ℕ} (p : Fin n → ℝ) (B m : ℕ) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) (J : Finset (Fin n)) :
    (∑ j ∈ J, p j) / ((m : ℝ) * (B : ℝ)) ≤ CmaxStar p B m J := by
  obtain ⟨S0, hS0⟩ := exists_valid B hB J
  haveI : Nonempty { S : List (Finset (Fin n)) // ValidBatching B J S } := ⟨⟨S0, hS0⟩⟩
  exact le_ciInf (fun S => volume_valid p B m hB hm hp J S.val S.property)

theorem volume_core {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (hn : 0 < n) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) :
    (∑ j : Fin n, p j) / ((m : ℝ) * (B : ℝ)) ≤
      CmaxStar p B m Finset.univ :=
  cmax_ge_vol p B m hB hm hp Finset.univ


lemma bc_nonneg {n m : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) (k : Fin S.length) : 0 ≤ batchCompletion p S σ k := by
  unfold batchCompletion
  exact Finset.sum_nonneg (fun t _ => by split_ifs; exact batchTime_nonneg hp _; exact le_rfl)

lemma jc_nonneg {n m : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) (j : Fin n) : 0 ≤ jobCompletion p S σ j := by
  unfold jobCompletion
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    exact (bc_nonneg hp S σ k).trans (Finset.le_sup' (f := batchCompletion p S σ) hk)
  · exact le_rfl

lemma jc_ge_bc {n m : ℕ} {p : Fin n → ℝ} (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) (k : Fin S.length) (j : Fin n) (hj : j ∈ S[k]) :
    batchCompletion p S σ k ≤ jobCompletion p S σ j := by
  have hk : k ∈ Finset.univ.filter (fun k : Fin S.length => j ∈ S[k]) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  unfold jobCompletion
  rw [dif_pos ⟨k, hk⟩]
  exact Finset.le_sup' (f := batchCompletion p S σ) hk

lemma sl_ge {n m : ℕ} (p d : Fin n → ℝ) (J : Finset (Fin n)) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) (j : Fin n) (hj : j ∈ J) :
    jobCompletion p S σ j - d j ≤ scheduleLateness p d J S σ := by
  unfold scheduleLateness
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.le_sup' (f := fun j => jobCompletion p S σ j - d j) hj

lemma load_le_jc {n m : ℕ} {p : Fin n → ℝ} (hp : ∀ j, 0 < p j) {B : ℕ} {J : Finset (Fin n)}
    (G : ParallelSchedule B m J) (hJ : J.Nonempty) (i : Fin m) :
    ∃ j ∈ J, machineLoad (batchTimes p G.batches) G.machine i ≤
      jobCompletion p G.batches G.machine j := by
  obtain ⟨j0, hj0⟩ := hJ
  by_cases hA : (Finset.univ.filter (fun t : Fin G.batches.length => G.machine t = i)).Nonempty
  · set A := Finset.univ.filter (fun t : Fin G.batches.length => G.machine t = i) with hAdef
    obtain ⟨hne, -, hun⟩ := G.valid
    set k := A.max' hA with hk
    have hkA : k ∈ A := Finset.max'_mem A hA
    have hki : G.machine k = i := by simpa [hAdef] using hkA
    obtain ⟨j, hj⟩ := (hne _ (List.getElem_mem k.2)).1
    refine ⟨j, ?_, ?_⟩
    · have : j ∈ G.batches.foldr (· ∪ ·) ∅ := (mem_foldr_union _ _).2 ⟨_, List.getElem_mem k.2, hj⟩
      rwa [hun] at this
    · refine le_trans (le_of_eq ?_) (jc_ge_bc G.batches G.machine k j hj)
      unfold machineLoad batchCompletion
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : G.machine t = i
      · have htk : (t : ℕ) ≤ (k : ℕ) := by
          have : t ≤ k := Finset.le_max' A t (by simp [hAdef, ht])
          exact this
        simp [ht, hki, htk, batchTimes, t.2]
      · simp [ht, hki]
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    refine ⟨j0, hj0, ?_⟩
    have : machineLoad (batchTimes p G.batches) G.machine i = 0 := by
      unfold machineLoad
      apply Finset.sum_eq_zero
      intro t _
      have : ¬ G.machine t = i := by
        intro h
        have : t ∈ Finset.univ.filter (fun t : Fin G.batches.length => G.machine t = i) := by simp [h]
        rw [hA] at this; simp at this
      simp [this]
    rw [this]
    exact jc_nonneg hp _ _ _

lemma cmax_le_sched {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ) (J : Finset (Fin n)) (hn : 0 < n)
    (hJ : J.Nonempty) (hm : 0 < m) (hp : ∀ j, 0 < p j) (G : ParallelSchedule B m J) :
    CmaxStar p B m J ≤ scheduleLateness p d J G.batches G.machine + maxDue d hn := by
  have hq := fun k => batchTimes_nonneg hp G.batches k
  have h1 : CmaxStar p B m J ≤ optMakespan G.batches.length m (batchTimes p G.batches) := by
    unfold CmaxStar
    exact ciInf_le (f := fun S : { S : List (Finset (Fin n)) // ValidBatching B J S } =>
      optMakespan S.val.length m (batchTimes p S.val))
      ⟨0, by rintro _ ⟨S, rfl⟩; exact opt_nonneg hm _ (fun j _ => batchTimes_nonneg hp _ j)⟩
      ⟨G.batches, G.valid⟩
  refine h1.trans ((opt_le hm _ (fun j _ => hq j) G.machine).trans ?_)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply ciSup_le
  intro i
  obtain ⟨j, hj, hle⟩ := load_le_jc hp G hJ i
  refine hle.trans ?_
  have h2 := sl_ge p d J G.batches G.machine j hj
  have h3 : d j ≤ maxDue d hn := by
    unfold maxDue
    exact Finset.le_sup' d (Finset.mem_univ j)
  linarith

theorem lateness_core {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (hn : 0 < n) (hJ : J.Nonempty)
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j) :
    CmaxStar p B m J - maxDue d hn ≤ LStar p d B m J := by
  obtain ⟨S0, hS0⟩ := exists_valid B hB J
  have : Nonempty (ParallelSchedule B m J) := ⟨⟨S0, hS0, fun _ => ⟨0, hm⟩⟩⟩
  unfold LStar
  refine le_ciInf (fun G => ?_)
  have := cmax_le_sched p d B m J hn hJ hm hp G
  linarith
end BurnInBatch.ListSched

open BurnInBatch.ListSched


theorem solution {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (hn : 0 < n) (hJ : J.Nonempty)
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j) :
    CmaxStar p B m J - maxDue d hn ≤ LStar p d B m J := by
  exact lateness_core p d B m J hn hJ hB hm hp
