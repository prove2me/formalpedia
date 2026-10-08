-- Prove2me | solution 1 for CompetitivePaging.Marking.marking_competitive
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:23:30.740831+00:00
-- url     : https://prove2.me/submissions/1df49d69-5f76-42e3-aa61-41dd2736c261

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm
import Theorems.Thm_KServer_exists_lazy_injective_algorithm
import Theorems.Thm_CompetitivePaging_Marking_adversary_phase_cost_ge_half
import Theorems.Thm_CompetitivePaging_Marking_phase_expected_cost_le

namespace CompetitivePaging.Marking.Assembly

section Marks

variable {M : Type*} [DecidableEq M]

/-- The marks never exceed `k` vertices. -/
lemma marksAfter_card_le {k : ℕ} (hk : 1 ≤ k) (mk : Finset M) (r : M) (h : mk.card ≤ k) :
    (marksAfter k mk r).card ≤ k := by
  unfold marksAfter
  split_ifs with h1
  · simpa using hk
  · have := Finset.card_insert_le r mk
    omega

lemma foldl_marksAfter_card_le {k : ℕ} (hk : 1 ≤ k) (l : List M) :
    ∀ mk : Finset M, mk.card ≤ k → (l.foldl (marksAfter k) mk).card ≤ k := by
  induction l with
  | nil => intro mk h; simpa using h
  | cons r l ih =>
    intro mk h
    exact ih _ (marksAfter_card_le hk mk r h)

lemma marksAt_card_le {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card ≤ k) (σ : List M)
    (t : ℕ) : (marksAt k V σ t).card ≤ k :=
  foldl_marksAfter_card_le hk _ V hV

lemma marksAt_zero {k : ℕ} (V : Finset M) (σ : List M) : marksAt k V σ 0 = V := by
  simp [marksAt]

lemma marksAt_succ {k : ℕ} (V : Finset M) (σ : List M) (t : ℕ) (ht : t < σ.length) :
    marksAt k V σ (t + 1) = marksAfter k (marksAt k V σ t) (σ.get ⟨t, ht⟩) := by
  unfold marksAt
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append]
  rfl

lemma mem_marksAfter_self {k : ℕ} (mk : Finset M) (r : M) : r ∈ marksAfter k mk r := by
  unfold marksAfter
  split_ifs <;> simp

end Marks

section Law

variable {M : Type*} [DecidableEq M]

/-- The state invariant of the marking algorithm. -/
def StateInv (k : ℕ) (m : Finset M) (s : State M) : Prop :=
  s.marked = m ∧ s.marked ⊆ s.covered ∧ s.covered.card = k ∧ s.marked.card ≤ k

lemma step_inv {k : ℕ} (hk : 1 ≤ k) (m : Finset M) (s : State M) (r : M) (hs : StateInv k m s)
    (s' : State M) (hs' : s' ∈ (step k s r).support) : StateInv k (marksAfter k m r) s' := by
  obtain ⟨hm, h1, h2, h3⟩ := hs
  subst hm
  have hcard : (marksAfter k s.marked r).card ≤ k := marksAfter_card_le hk _ r h3
  have hrmk : r ∈ marksAfter k s.marked r := mem_marksAfter_self _ r
  unfold step at hs'
  simp only at hs'
  by_cases hr : r ∈ s.covered
  · rw [if_pos hr, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    refine ⟨rfl, ?_, h2, hcard⟩
    intro x hx
    show x ∈ s.covered
    unfold marksAfter at hx
    split_ifs at hx with hc
    · rw [Finset.mem_singleton] at hx; subst hx; exact hr
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hr
      · exact h1 hx
  · rw [if_neg hr] at hs'
    by_cases hne : (s.covered \ marksAfter k s.marked r).Nonempty
    · rw [dif_pos hne, PMF.support_map] at hs'
      obtain ⟨v, hv, rfl⟩ := hs'
      rw [PMF.support_uniformOfFinset] at hv
      have hv' := Finset.mem_sdiff.mp hv
      refine ⟨rfl, ?_, ?_, hcard⟩
      · intro x hx
        show x ∈ insert r (s.covered.erase v)
        by_cases hxr : x = r
        · exact Finset.mem_insert.mpr (Or.inl hxr)
        · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨?_, ?_⟩))
          · rintro rfl; exact hv'.2 hx
          · have hx' : x ∈ s.marked := by
              unfold marksAfter at hx
              split_ifs at hx with hc
              · rw [Finset.mem_singleton] at hx; exact absurd hx hxr
              · rcases Finset.mem_insert.mp hx with h | h
                · exact absurd h hxr
                · exact h
            exact h1 hx'
      · show (insert r (s.covered.erase v)).card = k
        rw [Finset.card_insert_of_notMem (fun h => hr (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hv'.1]
        have : 0 < s.covered.card := Finset.card_pos.mpr ⟨v, hv'.1⟩
        omega
    · exfalso
      have hsub : s.covered ⊆ marksAfter k s.marked r := by
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
        exact hne
      have : (insert r s.covered).card ≤ (marksAfter k s.marked r).card :=
        Finset.card_le_card (Finset.insert_subset hrmk hsub)
      rw [Finset.card_insert_of_notMem hr] at this
      omega

lemma foldl_law_inv {k : ℕ} (hk : 1 ≤ k) (l : List M) :
    ∀ (p : PMF (State M)) (m : Finset M), (∀ s ∈ p.support, StateInv k m s) →
      ∀ s ∈ (l.foldl (fun p r => p.bind (fun s => step k s r)) p).support,
        StateInv k (l.foldl (marksAfter k) m) s := by
  induction l with
  | nil => intro p m h s hs; simpa using h s hs
  | cons r l ih =>
    intro p m h s hs
    simp only [List.foldl_cons] at hs ⊢
    refine ih _ _ ?_ s hs
    intro s' hs'
    rw [PMF.mem_support_bind_iff] at hs'
    obtain ⟨b, hb, hs'⟩ := hs'
    exact step_inv hk m b r (h b hb) s' hs'

lemma lawAfter_inv {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (l : List M) :
    ∀ s ∈ (lawAfter k V l).support, StateInv k (l.foldl (marksAfter k) V) s := by
  unfold lawAfter
  refine foldl_law_inv hk l _ V ?_
  intro s hs
  rw [PMF.support_pure, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨rfl, Finset.Subset.refl _, hV, hV.le⟩

/-- A request to a marked vertex never faults. -/
lemma faultProb_eq_zero {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (l : List M)
    (r : M) (hr : r ∈ l.foldl (marksAfter k) V) : faultProb k V l r = 0 := by
  unfold faultProb
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro s hs hs'
  obtain ⟨hm, h1, -, -⟩ := lawAfter_inv hk V hV l s hs
  exact hs' (h1 (hm ▸ hr))

lemma faultProb_toReal_le_one {k : ℕ} (V : Finset M) (l : List M) (r : M) :
    (faultProb k V l r).toReal ≤ 1 := by
  have h1 : faultProb k V l r ≤ 1 := by
    unfold faultProb
    rw [← (lawAfter k V l).toOuterMeasure_apply_eq_one_iff Set.univ |>.mpr (Set.subset_univ _)]
    exact PMF.toOuterMeasure_mono _ (fun _ _ => Set.mem_univ _)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1

end Law


section Accounting

variable {n k : ℕ} {M : Type*} [DecidableEq M]

lemma initVertices_card (e : Fin n ≃ M) (hkn : k ≤ n) : (initVertices e hkn).card = k := by
  have hinj : Function.Injective (initConfig e hkn) :=
    fun a b h => Fin.castLE_injective hkn (e.injective h)
  unfold initVertices
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- The fault cost of the `t`-th request (zero beyond the end of `σ`). -/
noncomputable def fcost (k : ℕ) (V : Finset M) (σ : List M) (t : ℕ) : ℝ :=
  if h : t < σ.length then (faultProb k V (σ.take t) (σ.get ⟨t, h⟩)).toReal else 0

/-- `1` if the `t`-th request is to an unmarked vertex, and `0` otherwise. -/
def mcost (k : ℕ) (V : Finset M) (σ : List M) (t : ℕ) : ℕ :=
  if h : t < σ.length then (if σ.get ⟨t, h⟩ ∈ marksAt k V σ t then 0 else 1) else 0

lemma fcost_nonneg (k : ℕ) (V : Finset M) (σ : List M) (t : ℕ) : 0 ≤ fcost k V σ t := by
  unfold fcost
  split_ifs <;> simp

lemma fcost_le_mcost {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (σ : List M)
    (t : ℕ) : fcost k V σ t ≤ (mcost k V σ t : ℝ) := by
  unfold fcost mcost
  by_cases ht : t < σ.length
  · rw [dif_pos ht, dif_pos ht]
    by_cases hm : σ.get ⟨t, ht⟩ ∈ marksAt k V σ t
    · rw [if_pos hm, faultProb_eq_zero hk V hV _ _ hm]; simp
    · rw [if_neg hm]
      simpa using faultProb_toReal_le_one (k := k) V (σ.take t) (σ.get ⟨t, ht⟩)
  · simp [ht]

lemma fcost_eq_zero {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (σ : List M)
    (t : ℕ) (ht : t < σ.length) (hm : σ.get ⟨t, ht⟩ ∈ marksAt k V σ t) :
    fcost k V σ t = 0 := by
  unfold fcost
  rw [dif_pos ht, faultProb_eq_zero hk V hV _ _ hm]
  simp

lemma markingExpCost_eq (k : ℕ) (V : Finset M) (σ : List M) :
    markingExpCost k V σ = ∑ t ∈ Finset.range σ.length, fcost k V σ t := by
  unfold markingExpCost
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp [fcost]

lemma markingPhaseCost_eq (k : ℕ) (V : Finset M) (σ : List M) (i i' : ℕ)
    (h : i' ≤ σ.length) :
    markingPhaseCost k V σ i i' = ∑ t ∈ Finset.Ico i i', fcost k V σ t := by
  unfold markingPhaseCost
  have : ∑ t ∈ Finset.range σ.length, (if i ≤ t ∧ t < i' then fcost k V σ t else 0) =
      ∑ t : Fin σ.length, (if i ≤ t.val ∧ t.val < i' then
        (faultProb k V (σ.take t) (σ.get t)).toReal else 0) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [fcost]
  rw [← this, ← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- Before the first phase start the marks stay equal to `V` and no request faults. -/
lemma pre_phase {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (σ : List M) :
    ∀ N, N ≤ σ.length → (∀ t < N, ¬ IsPhaseStart k V σ t) →
      marksAt k V σ N = V ∧ ∑ t ∈ Finset.range N, fcost k V σ t = 0 := by
  intro N
  induction N with
  | zero => intro _ _; simp [marksAt_zero]
  | succ N ih =>
    intro hN hno
    have hNlt : N < σ.length := hN
    obtain ⟨hm, hs⟩ := ih (by omega) (fun t ht => hno t (by omega))
    have hnp := hno N (by omega)
    have hrV : σ.get ⟨N, hNlt⟩ ∈ V := by
      by_contra hrV
      apply hnp
      refine ⟨hNlt, ?_⟩
      rw [hm, Finset.card_insert_of_notMem hrV, hV]
    have hnc : ¬ (insert (σ.get ⟨N, hNlt⟩) V).card = k + 1 := by
      rw [Finset.insert_eq_of_mem hrV, hV]; omega
    refine ⟨?_, ?_⟩
    · rw [marksAt_succ V σ N hNlt, hm]
      unfold marksAfter
      rw [if_neg hnc, Finset.insert_eq_of_mem hrV]
    · rw [Finset.sum_range_succ, hs, fcost_eq_zero hk V hV σ N hNlt (by rw [hm]; exact hrV)]
      simp

/-- In the last (possibly incomplete) phase the marking algorithm pays at most `k`. -/
lemma tail_cost {k : ℕ} (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (σ : List M) (i : ℕ)
    (hi : IsPhaseStart k V σ i)
    (hno : ∀ w, i < w → w < σ.length → ¬ IsPhaseStart k V σ w) :
    ∑ t ∈ Finset.Ico i σ.length, fcost k V σ t ≤ k := by
  obtain ⟨hilt, hcard⟩ := hi
  have key : ∀ t, i + 1 ≤ t → t ≤ σ.length →
      (marksAt k V σ t).card = ∑ u ∈ Finset.Ico i t, mcost k V σ u := by
    intro t ht1
    induction t, ht1 using Nat.le_induction with
    | base =>
      intro _
      have hr : σ.get ⟨i, hilt⟩ ∉ marksAt k V σ i := by
        intro hmem
        have := marksAt_card_le hk V hV.le σ i
        rw [Finset.insert_eq_of_mem hmem] at hcard
        omega
      rw [marksAt_succ V σ i hilt, Nat.Ico_succ_singleton, Finset.sum_singleton]
      unfold marksAfter
      rw [if_pos hcard]
      simp only [mcost, dif_pos hilt, if_neg hr, Finset.card_singleton]
    | succ t ht ih =>
      intro hle
      have htl : t < σ.length := by omega
      have hnp := hno t (by omega) htl
      have hnc : ¬ (insert (σ.get ⟨t, htl⟩) (marksAt k V σ t)).card = k + 1 :=
        fun h => hnp ⟨htl, h⟩
      rw [marksAt_succ V σ t htl, Finset.sum_Ico_succ_top (by omega : i ≤ t), ← ih (by omega)]
      unfold marksAfter
      rw [if_neg hnc]
      by_cases hm : σ.get ⟨t, htl⟩ ∈ marksAt k V σ t
      · rw [Finset.insert_eq_of_mem hm]
        simp only [mcost, dif_pos htl, if_pos hm, add_zero]
      · rw [Finset.card_insert_of_notMem hm]
        simp only [mcost, dif_pos htl, if_neg hm]
  have h1 := key σ.length (by omega) le_rfl
  have h2 := marksAt_card_le hk V hV.le σ σ.length
  calc ∑ t ∈ Finset.Ico i σ.length, fcost k V σ t
      ≤ ∑ t ∈ Finset.Ico i σ.length, (mcost k V σ t : ℝ) :=
        Finset.sum_le_sum (fun t _ => fcost_le_mcost hk V hV σ t)
    _ = ((marksAt k V σ σ.length).card : ℝ) := by rw [h1]; push_cast; rfl
    _ ≤ k := by exact_mod_cast h2

end Accounting

section Lazy

variable {k : ℕ} {M : Type*} [MetricSpace M]

lemma moveCost_nonneg (C C' : KServer.Config k M) : 0 ≤ KServer.moveCost C C' :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

open scoped Classical in
/-- An arbitrary schedule serving `σ` from an injective configuration can be replaced by a
lazy schedule of no larger cost. -/
lemma exists_lazy_schedule (hk : 1 ≤ k) (C0 : KServer.Config k M)
    (hC0 : Function.Injective C0) (σ : List M) (S0 : ℕ → KServer.Config k M)
    (hS0 : KServer.ServesFrom C0 σ S0) :
    ∃ S : ℕ → KServer.Config k M, IsLazySchedule σ S ∧
      ∑ t ∈ Finset.range σ.length, KServer.moveCost (S t) (S (t + 1)) ≤
        ∑ t ∈ Finset.range σ.length, KServer.moveCost (S0 t) (S0 (t + 1)) := by
  let A : KServer.OnlineAlgorithm k M :=
    { conf := fun l => if l <+: σ then S0 l.length else
        fun _ => l.getLast?.getD (C0 ⟨0, hk⟩)
      serves := by
        intro l r
        by_cases hp : (l ++ [r]) <+: σ
        · have hj : l.length < σ.length := by
            have := hp.length_le
            simp at this
            omega
          obtain ⟨i, hi⟩ := hS0.2 ⟨l.length, hj⟩
          refine ⟨i, ?_⟩
          have hr : σ.get ⟨l.length, hj⟩ = r := by
            have := hp.getElem (i := l.length) (by simp)
            simpa using this.symm
          rw [if_pos hp]
          simp only [List.length_append, List.length_singleton]
          rw [← hr]
          exact hi
        · refine ⟨⟨0, hk⟩, ?_⟩
          simp [hp] }
  have hA : ∀ j ≤ σ.length, A.conf (σ.take j) = S0 j := by
    intro j hj
    show (if σ.take j <+: σ then S0 (σ.take j).length else _) = S0 j
    rw [if_pos (List.take_prefix _ _), List.length_take, min_eq_left hj]
  have hinj : Function.Injective (A.conf []) := by
    have : A.conf [] = C0 := by
      have := hA 0 (Nat.zero_le _)
      simp only [List.take_zero] at this
      rw [this]; exact hS0.1
    rw [this]; exact hC0
  obtain ⟨B, hB0, hBcost, hBinj, hBlazy, hBupd⟩ :=
    KServer.exists_lazy_injective_algorithm k M A hinj
  refine ⟨fun t => B.conf (σ.take t), ?_, ?_⟩
  · intro j
    have htake : σ.take (j + 1) = σ.take j ++ [σ.get j] := by
      rw [List.take_add_one, List.getElem?_eq_getElem j.2, Option.toList_some]
      rfl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · show B.conf (σ.take (j + 1)) = B.conf (σ.take j)
      rw [htake]
      exact hBlazy _ _ h
    · show ∃ i, B.conf (σ.take (j + 1)) = Function.update (B.conf (σ.take j)) i (σ.get j)
      rw [htake]
      exact hBupd _ _
  · have h1 := hBcost σ
    have h2 : A.cost σ = ∑ t ∈ Finset.range σ.length, KServer.moveCost (S0 t) (S0 (t + 1)) := by
      unfold KServer.OnlineAlgorithm.cost
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' := Finset.mem_range.mp hj
      rw [hA j (by omega), hA (j + 1) (by omega)]
    rw [← h2]
    exact h1

end Lazy


section Main

variable {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]

/-- Number of servers of the schedule `S` outside the marked set at time `t`
(the quantity `d` of the paper). -/
noncomputable def dcount (k : ℕ) (V : Finset M) (σ : List M) (S : ℕ → KServer.Config k M)
    (t : ℕ) : ℝ :=
  ((Finset.univ.filter (fun j : Fin k => S t j ∉ marksAt k V σ t)).card : ℝ)

omit [MetricSpace M] in
lemma dcount_nonneg (k : ℕ) (V : Finset M) (σ : List M) (S : ℕ → KServer.Config k M)
    (t : ℕ) : 0 ≤ dcount k V σ S t := by
  unfold dcount; positivity

omit [MetricSpace M] in
lemma dcount_le (k : ℕ) (V : Finset M) (σ : List M) (S : ℕ → KServer.Config k M)
    (t : ℕ) : dcount k V σ S t ≤ k := by
  unfold dcount
  have : (Finset.univ.filter (fun j : Fin k => S t j ∉ marksAt k V σ t)).card ≤ k := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k))
      (fun j : Fin k => S t j ∉ marksAt k V σ t)
  exact_mod_cast this

/-- The marking algorithm against a lazy schedule: summing the phases. -/
lemma marking_le_of_lazy (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (S : ℕ → KServer.Config k M)
    (hlazy : IsLazySchedule σ S) :
    markingExpCost k (initVertices e hkn) σ ≤
      (harmonic k : ℝ) *
        (2 * ∑ t ∈ Finset.range σ.length, KServer.moveCost (S t) (S (t + 1)) + k) + k := by
  classical
  set V := initVertices e hkn with hVdef
  have hV : V.card = k := initVertices_card e hkn
  have hH : 0 ≤ (harmonic k : ℝ) := by exact_mod_cast (harmonic_pos (by omega : k ≠ 0)).le
  have hcnn : ∀ N, 0 ≤ ∑ t ∈ Finset.range N, KServer.moveCost (S t) (S (t + 1)) :=
    fun N => Finset.sum_nonneg (fun t _ => moveCost_nonneg _ _)
  -- the potential inequality at every phase start
  have hP : ∀ i, IsPhaseStart k V σ i →
      ∑ t ∈ Finset.range i, fcost k V σ t ≤
        (harmonic k : ℝ) * (2 * ∑ t ∈ Finset.range i, KServer.moveCost (S t) (S (t + 1))
          + k - dcount k V σ S i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hile : i ≤ σ.length := hi.1.le
      by_cases hex : ∃ u, u < i ∧ IsPhaseStart k V σ u
      · obtain ⟨u0, hu0, hu0p⟩ := hex
        set u := Nat.findGreatest (fun w => IsPhaseStart k V σ w) (i - 1) with hu
        have hup : IsPhaseStart k V σ u :=
          Nat.findGreatest_spec (P := fun w => IsPhaseStart k V σ w) (by omega : u0 ≤ i - 1) hu0p
        have hule : u ≤ i - 1 := Nat.findGreatest_le _
        have hui : u < i := by omega
        have hphase : IsCompletePhase k V σ u i :=
          ⟨hup, hi, hui, fun w hw1 hw2 =>
            Nat.findGreatest_is_greatest (P := fun w => IsPhaseStart k V σ w)
              (by omega : u < w) (by omega : w ≤ i - 1)⟩
        have h1 := ih u hui hup
        obtain ⟨hA1, hA2⟩ := adversary_phase_cost_ge_half e hdist hk hkn σ S hlazy u i hphase
        obtain ⟨hB1, hB2⟩ := phase_expected_cost_le e hk hkn σ u i hphase
        rw [markingPhaseCost_eq k V σ u i hile] at hB1
        have hA : (((phaseRequested σ u i \ marksAt k V σ u).card : ℝ)
            - dcount k V σ S u + dcount k V σ S i) / 2 ≤
            ∑ t ∈ Finset.Ico u i, KServer.moveCost (S t) (S (t + 1)) := hA2.trans hA1
        have hB : ∑ t ∈ Finset.Ico u i, fcost k V σ t ≤
            ((phaseRequested σ u i \ marksAt k V σ u).card : ℝ) * (harmonic k : ℝ) :=
          hB1.trans hB2
        rw [← Finset.sum_range_add_sum_Ico _ hui.le,
          ← Finset.sum_range_add_sum_Ico (fun t => KServer.moveCost (S t) (S (t + 1))) hui.le]
        have hm := mul_le_mul_of_nonneg_left
          (show ((phaseRequested σ u i \ marksAt k V σ u).card : ℝ) - dcount k V σ S u
            + dcount k V σ S i ≤
            2 * ∑ t ∈ Finset.Ico u i, KServer.moveCost (S t) (S (t + 1)) by linarith) hH
        nlinarith [hm, h1, hB]
      · obtain ⟨-, hs⟩ := pre_phase hk V hV σ i hile (fun t ht hts => hex ⟨t, ht, hts⟩)
        rw [hs]
        exact mul_nonneg hH (by
          linarith [hcnn i, dcount_le k V σ S i])
  rw [markingExpCost_eq]
  by_cases hex : ∃ u, IsPhaseStart k V σ u
  · obtain ⟨u0, hu0⟩ := hex
    have hu0lt : u0 < σ.length := hu0.1
    set u := Nat.findGreatest (fun w => IsPhaseStart k V σ w) σ.length with hu
    have hup : IsPhaseStart k V σ u :=
      Nat.findGreatest_spec (P := fun w => IsPhaseStart k V σ w) hu0lt.le hu0
    have hult : u < σ.length := hup.1
    have hno : ∀ w, u < w → w < σ.length → ¬ IsPhaseStart k V σ w :=
      fun w h1 h2 => Nat.findGreatest_is_greatest (P := fun w => IsPhaseStart k V σ w) h1 h2.le
    have hT := tail_cost hk V hV σ u hup hno
    have hPu := hP u hup
    have hcmono : ∑ t ∈ Finset.range u, KServer.moveCost (S t) (S (t + 1)) ≤
        ∑ t ∈ Finset.range σ.length, KServer.moveCost (S t) (S (t + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hult.le)
        (fun _ _ _ => moveCost_nonneg _ _)
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * ∑ t ∈ Finset.range u, KServer.moveCost (S t) (S (t + 1)) + k
          - dcount k V σ S u ≤
        2 * ∑ t ∈ Finset.range σ.length, KServer.moveCost (S t) (S (t + 1)) + k by
        linarith [dcount_nonneg k V σ S u]) hH
    rw [← Finset.sum_range_add_sum_Ico _ hult.le]
    linarith
  · obtain ⟨-, hs⟩ := pre_phase hk V hV σ σ.length le_rfl (fun t _ h => hex ⟨t, h⟩)
    rw [hs]
    exact add_nonneg (mul_nonneg hH (by linarith [hcnn σ.length])) (by positivity)

end Main

end CompetitivePaging.Marking.Assembly

open CompetitivePaging.Marking in
theorem solution {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ a : ℝ, ∀ σ : List M,
      markingExpCost k (initVertices e hkn) σ
        ≤ 2 * (harmonic k : ℝ) * KServer.offlineCost (initConfig e hkn) σ + a := by
  open CompetitivePaging.Marking.Assembly in
  have hH : 0 < (harmonic k : ℝ) := by exact_mod_cast harmonic_pos (by omega)
  refine ⟨(harmonic k : ℝ) * k + k, fun σ => ?_⟩
  have hC0 : Function.Injective (initConfig e hkn) :=
    fun a b h => Fin.castLE_injective hkn (e.injective h)
  set T : Set ℝ := {c : ℝ | ∃ S : ℕ → KServer.Config k M,
    KServer.ServesFrom (initConfig e hkn) σ S ∧
      c = ∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1))} with hT
  have hne : T.Nonempty := by
    refine ⟨_, fun j => match j with
      | 0 => initConfig e hkn
      | j + 1 => fun _ => σ.getD j (initConfig e hkn ⟨0, hk⟩), ?_, rfl⟩
    refine ⟨rfl, fun j => ⟨⟨0, hk⟩, ?_⟩⟩
    simp [List.getD_eq_getElem?_getD]
  have hbound : ∀ x ∈ T, markingExpCost k (initVertices e hkn) σ ≤
      2 * (harmonic k : ℝ) * x + ((harmonic k : ℝ) * k + k) := by
    rintro x ⟨S0, hS0, rfl⟩
    obtain ⟨S, hS, hcost⟩ :=
      Assembly.exists_lazy_schedule hk (initConfig e hkn) hC0 σ S0 hS0
    have := Assembly.marking_le_of_lazy e hdist hk hkn σ S hS
    nlinarith [mul_le_mul_of_nonneg_left hcost hH.le]
  have hle : (markingExpCost k (initVertices e hkn) σ - ((harmonic k : ℝ) * k + k))
      / (2 * (harmonic k : ℝ)) ≤ KServer.offlineCost (initConfig e hkn) σ := by
    unfold KServer.offlineCost
    refine le_csInf hne (fun x hx => ?_)
    rw [div_le_iff₀ (by positivity)]
    linarith [hbound x hx]
  rw [div_le_iff₀ (by positivity)] at hle
  linarith
