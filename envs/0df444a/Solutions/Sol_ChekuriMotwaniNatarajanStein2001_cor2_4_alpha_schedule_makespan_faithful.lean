-- Prove2me | solution 1 for ChekuriMotwaniNatarajanStein2001.cor2_4_alpha_schedule_makespan_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:23:36.997833+00:00
-- url     : https://prove2.me/submissions/7f6c24fe-d385-4716-be8a-40dbd7101675

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

open MeasureTheory AvgCompletionSched.BestAlpha Set

namespace CH85

variable {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)

def A (j : Fin n) : Set ℝ := {s | P.σ s = some j}

theorem vol_lt (j : Fin n) (t : ℝ) : volume (A P j ∩ Ico 0 t) < ⊤ :=
  lt_of_le_of_lt (measure_mono inter_subset_left) (by rw [A, P.total j]; exact ENNReal.ofReal_lt_top)

theorem done_mono (j : Fin n) {s t : ℝ} (h : s ≤ t) : P.done j s ≤ P.done j t := by
  unfold PreemptiveSchedule.done
  exact ENNReal.toReal_mono (vol_lt P j t).ne
    (measure_mono (inter_subset_inter_right _ (Ico_subset_Ico_right h)))

theorem done_lip (j : Fin n) {s t : ℝ} (h : s ≤ t) : P.done j t ≤ P.done j s + (t - s) := by
  unfold PreemptiveSchedule.done
  have hsub : {s' | P.σ s' = some j} ∩ Ico 0 t ⊆ ({s' | P.σ s' = some j} ∩ Ico 0 s) ∪ Ico s t := by
    intro x ⟨hx1, hx2⟩
    rcases lt_or_ge x s with hxs | hxs
    · exact Or.inl ⟨hx1, hx2.1, hxs⟩
    · exact Or.inr ⟨hxs, hx2.2⟩
  have h1 := (measure_mono hsub).trans (measure_union_le (μ := volume) _ _)
  rw [Real.volume_Ico] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(vol_lt P j s).ne, ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add (vol_lt P j s).ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)] at h2
  exact h2

theorem done_nonneg (j : Fin n) (t : ℝ) : 0 ≤ P.done j t := ENNReal.toReal_nonneg

theorem done_le_r (j : Fin n) {t : ℝ} (ht : t ≤ I.r j) : P.done j t = 0 := by
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Ico 0 t = ∅ := by
    ext x; simp only [mem_inter_iff, mem_setOf_eq, mem_Ico, mem_empty_iff_false, iff_false]
    intro ⟨h1, h2⟩; have := P.released x j h1; linarith [h2.2]
  rw [this]; simp

theorem done_big (j : Fin n) : ∃ T0 : ℝ, ∀ t ≥ T0, P.done j t = I.p j := by
  obtain ⟨T0, hT0⟩ := P.bounded j
  refine ⟨T0, fun t ht => ?_⟩
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Ico 0 t = {s | P.σ s = some j} := by
    apply inter_eq_left.mpr
    intro x hx; exact ⟨P.nonneg x j hx, (hT0 x hx).trans_le ht⟩
  rw [this, P.total j, ENNReal.toReal_ofReal (I.p_pos j).le]

/-- the level set `{t | c ≤ done j t}` -/
theorem lvl_nonempty (j : Fin n) {c : ℝ} (hc : c ≤ I.p j) : {t | c ≤ P.done j t}.Nonempty := by
  obtain ⟨T0, h⟩ := done_big P j
  exact ⟨T0, by simp only [mem_setOf_eq]; rw [h T0 le_rfl]; exact hc⟩

theorem lvl_bdd (j : Fin n) {c : ℝ} (hc : 0 < c) : BddBelow {t | c ≤ P.done j t} := by
  refine ⟨I.r j, fun t ht => ?_⟩
  by_contra h
  simp only [mem_setOf_eq] at ht
  rw [done_le_r P j (le_of_lt (not_le.mp h))] at ht; linarith

theorem r_le_lvl (j : Fin n) {c : ℝ} (hc : 0 < c) (hcp : c ≤ I.p j) :
    I.r j ≤ sInf {t | c ≤ P.done j t} := by
  apply le_csInf (lvl_nonempty P j hcp)
  intro t ht
  by_contra h
  simp only [mem_setOf_eq] at ht
  rw [done_le_r P j (le_of_lt (not_le.mp h))] at ht; linarith

theorem done_at_lvl (j : Fin n) {c : ℝ} (hc : 0 < c) (hcp : c ≤ I.p j) :
    c ≤ P.done j (sInf {t | c ≤ P.done j t}) := by
  set τ := sInf {t | c ≤ P.done j t}
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs, hsl⟩ := (csInf_lt_iff (lvl_bdd P j hc) (lvl_nonempty P j hcp)).mp
    (show τ < τ + ε by linarith)
  simp only [mem_setOf_eq] at hs
  have h1 := done_mono P j (le_of_lt hsl)
  have h2 := done_lip P j (show τ ≤ τ + ε by linarith)
  linarith

theorem done_le_lvl (j : Fin n) {c : ℝ} (hc : 0 < c) (hcp : c ≤ I.p j) {t : ℝ}
    (ht : t ≤ sInf {t | c ≤ P.done j t}) : P.done j t ≤ c := by
  by_contra h
  push_neg at h
  set ε := (P.done j t - c) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have h1 := done_lip P j (show t - ε ≤ t by linarith)
  have hmem : t - ε ∈ {t | c ≤ P.done j t} := by
    simp only [mem_setOf_eq]; simp only [ε] at h1 ⊢; linarith
  have := csInf_le (lvl_bdd P j hc) hmem
  linarith

theorem CPα_eq (j : Fin n) (α : ℝ) : P.CPα j α = sInf {t | α * I.p j ≤ P.done j t} := rfl
theorem CP_eq (j : Fin n) : P.CP j = sInf {t | I.p j ≤ P.done j t} := rfl

theorem CPα_le_CP (j : Fin n) {α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) : P.CPα j α ≤ P.CP j := by
  have hp := I.p_pos j
  apply csInf_le_csInf (lvl_bdd P j (by nlinarith [hα.1])) (lvl_nonempty P j le_rfl)
  intro t ht; simp only [mem_setOf_eq] at ht ⊢; nlinarith [hα.2]

/-- total processing of a set of jobs in `[t,u)` is at most `u - t` -/
theorem sum_done (J : Finset (Fin n)) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ∑ j ∈ J, (P.done j u - P.done j t) ≤ u - t := by
  have hj : ∀ j, P.done j u - P.done j t = (volume (A P j ∩ Ico t u)).toReal := by
    intro j
    unfold PreemptiveSchedule.done
    have hun : A P j ∩ Ico 0 u = (A P j ∩ Ico 0 t) ∪ (A P j ∩ Ico t u) := by
      rw [← inter_union_distrib_left, Ico_union_Ico_eq_Ico ht htu]
    have hdis : Disjoint (A P j ∩ Ico 0 t) (A P j ∩ Ico t u) := by
      apply Disjoint.inter_right' ; apply Disjoint.inter_left'
      rw [Set.disjoint_left]; intro x h1 h2; exact absurd h2.1 (not_le.mpr h1.2)
    have hm : MeasurableSet (A P j ∩ Ico t u) := (P.measurableSet_run j).inter measurableSet_Ico
    change (volume (A P j ∩ Ico 0 u)).toReal - (volume (A P j ∩ Ico 0 t)).toReal = _
    rw [hun, measure_union hdis hm, ENNReal.toReal_add (vol_lt P j t).ne]
    · ring
    · exact (lt_of_le_of_lt (measure_mono inter_subset_left) (by rw [A, P.total j]; exact ENNReal.ofReal_lt_top)).ne
  simp_rw [hj]
  have hfin : ∀ j ∈ J, volume (A P j ∩ Ico t u) ≠ ⊤ := fun j _ =>
    (lt_of_le_of_lt (measure_mono inter_subset_left) (by rw [A, P.total j]; exact ENNReal.ofReal_lt_top)).ne
  rw [← ENNReal.toReal_sum hfin, ← measure_biUnion_finset]
  · have := measure_mono (μ := volume) (show (⋃ j ∈ J, A P j ∩ Ico t u) ⊆ Ico t u from
      iUnion₂_subset fun _ _ => inter_subset_right)
    rw [Real.volume_Ico] at this
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal (by linarith)] at h2
  · intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, _⟩ ⟨h2, _⟩
    change P.σ x = some i at h1
    change P.σ x = some j at h2
    rw [h1] at h2; exact hij (Option.some_injective _ h2)
  · intro j _; exact (P.measurableSet_run j).inter measurableSet_Ico

theorem done_zero (j : Fin n) : P.done j 0 = 0 := done_le_r P j (I.r_nonneg j)

end CH85


open MeasureTheory AvgCompletionSched.BestAlpha Set

namespace CH85

variable {n : ℕ} {I : Instance n}

def seg (n m k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => m ≤ l.val ∧ l.val < k)

theorem list_bound (π : Fin n ≃ Fin n) : ∀ k (hk : k < n), ∃ m, ∃ hm : m ≤ k,
    listFinish I π (k + 1) ≤ I.r (π ⟨m, by omega⟩) + ∑ l ∈ seg n m (k + 1), I.p (π l) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨0, le_rfl, ?_⟩
    have hs : seg n 0 1 = {⟨0, hk⟩} := by
      ext l; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; ext; simp; omega
      · intro h; rw [h]; simp
    rw [hs, Finset.sum_singleton]
    simp only [listFinish, dif_pos hk]
    rw [max_eq_left (I.r_nonneg _)]
  | succ k ih =>
    intro hk
    obtain ⟨m, hm, h⟩ := ih (by omega)
    have e : listFinish I π (k + 1 + 1) =
        max (I.r (π ⟨k + 1, hk⟩)) (listFinish I π (k + 1)) + I.p (π ⟨k + 1, hk⟩) := by
      rw [listFinish, dif_pos hk]
    rw [e]
    rcases le_total (listFinish I π (k + 1)) (I.r (π ⟨k + 1, hk⟩)) with hle | hle
    · refine ⟨k + 1, le_rfl, ?_⟩
      have hs : seg n (k + 1) (k + 1 + 1) = {⟨k + 1, hk⟩} := by
        ext l; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; ext; simp; omega
        · intro h; rw [h]; simp
      rw [hs, Finset.sum_singleton, max_eq_left hle]
    · refine ⟨m, by omega, ?_⟩
      have hs : seg n m (k + 1 + 1) = insert ⟨k + 1, hk⟩ (seg n m (k + 1)) := by
        ext l; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h; by_cases hl : l.val = k + 1
          · left; ext; simp [hl]
          · right; omega
        · rintro (h | h)
          · rw [h]; simp; omega
          · omega
      rw [hs, Finset.sum_insert (by simp [seg]), max_eq_right hle]
      linarith

end CH85


open MeasureTheory AvgCompletionSched.BestAlpha Set CH85

theorem solution {n : ℕ}
    {I : Instance n} (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∀ j, P.CP j ≤ T) :
    listFinish I π n ≤ (1 + α) * T := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [listFinish]; nlinarith [hα.1]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, hm, h⟩ := list_bound (I := I) π k (by omega)
  set jm := π ⟨m, by omega⟩
  set t := P.CPα jm α
  set J := seg (k + 1) m (k + 1)
  have hpos : ∀ j, 0 < α * I.p j := fun j => mul_pos hα.1 (I.p_pos j)
  have hle : ∀ j, α * I.p j ≤ I.p j := fun j => by nlinarith [hα.2, I.p_pos j]
  have hrt : I.r jm ≤ t := r_le_lvl P jm (hpos jm) (hle jm)
  have ht0 : 0 ≤ t := (I.r_nonneg jm).trans hrt
  have htT : t ≤ T := (CPα_le_CP P jm hα).trans (hT jm)
  have hlow : ∀ l ∈ J, P.done (π l) t ≤ α * I.p (π l) := by
    intro l hl
    have hml : (⟨m, by omega⟩ : Fin (k + 1)) ≤ l := by
      simp only [J, seg, Finset.mem_filter] at hl; exact Fin.mk_le_of_le_val hl.2.1
    exact done_le_lvl P (π l) (hpos _) (hle _) (hπ _ _ hml)
  have hup : ∀ l ∈ J, I.p (π l) ≤ P.done (π l) T := by
    intro l _
    exact (done_at_lvl P (π l) (I.p_pos _) le_rfl).trans (done_mono P _ (hT _))
  have hs1 := sum_done P (J.image π) ht0 htT
  have hs2 := sum_done P (J.image π) le_rfl hT0
  rw [Finset.sum_image (fun a _ b _ h => π.injective h)] at hs1 hs2
  simp only [done_zero, sub_zero] at hs2
  have hA : ∑ l ∈ J, I.p (π l) ≤ T :=
    (Finset.sum_le_sum hup).trans hs2
  have hB : ∑ l ∈ J, (I.p (π l) - α * I.p (π l)) ≤ T - t :=
    (Finset.sum_le_sum fun l hl => by linarith [hup l hl, hlow l hl]).trans hs1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hB
  nlinarith [hα.1]
