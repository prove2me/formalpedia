-- Prove2me | solution 1 for DeterioratingJobs.Makespan.eq2_completion_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:06:38.573831+00:00
-- url     : https://prove2.me/submissions/59d4e974-8057-426c-83b2-e0551aaaa775

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum
import Definitions.Def_DeterioratingJobs_Makespan_Model



namespace DeterioratingJobs.Makespan

open MeasureTheory

theorem eq2_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    completionTime X α π k ω =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k),
          (1 + α (π r)) := by
  induction k with
  | zero => simp [completionTime]
  | succ k ih =>
    have hkN : k < N := hk
    have ih' := ih hkN.le
    have hstep : completionTime X α π (k+1) ω =
        completionTime X α π k ω +
          actualProcessingTime X α (π ⟨k, hkN⟩)
            (completionTime X α π k ω) ω := by
      simp [completionTime, hkN]
    rw [hstep, ih']
    unfold actualProcessingTime
    have hs : (Finset.univ.filter (fun i : Fin N => i.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega
    rw [hs, Finset.sum_insert (by simp)]
    have hp : ∀ i : Fin N, i.val < k →
        (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k)) := by
      intro i hi
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.lt_def]; omega
    have hp0 : (Finset.univ.filter (fun r : Fin N => (⟨k, hkN⟩ : Fin N) < r ∧ r.val < k+1)) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Fin.lt_def]; omega
    rw [hp0, Finset.prod_empty, mul_one]
    have : ∀ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k+1), (1 + α (π r)) =
        (X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k), (1 + α (π r))) * (1 + α (π ⟨k, hkN⟩)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hp i hi, Finset.prod_insert (by simp)]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    ring

theorem expmk_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    expectedMakespan P X α π =
      lemma1Sum (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) π := by
  unfold expectedMakespan lemma1Sum makespan
  have h : ∀ ω, completionTime X α π N ω = ∑ i : Fin N, X (π i) ω * ∏ r ∈ Finset.Ioi i, (1 + α (π r)) := by
    intro ω
    rw [eq2_core X α π N le_rfl ω]
    have hu : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ := by ext; simp
    rw [hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext r; simp
  simp_rw [h]
  rw [integral_finsetSum _ (fun i _ => (hX (π i)).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const]

/-! list formulation -/
section lists
variable {ι : Type*}

noncomputable def Fl (μ γ : ι → ℝ) : List ι → ℝ
  | [] => 0
  | a :: t => μ a * (t.map γ).prod + Fl μ γ t

lemma prod_pos' (γ : ι → ℝ) (hγ : ∀ i, 1 < γ i) (l : List ι) : 0 < (l.map γ).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
  linarith [hγ x]

lemma move_front (μ γ : ι → ℝ) (hγ : ∀ i, 1 < γ i) (b : ι) :
    ∀ (l1 l2 : List ι), (∀ x ∈ l1, μ b / (γ b - 1) ≤ μ x / (γ x - 1)) →
      Fl μ γ (b :: (l1 ++ l2)) ≤ Fl μ γ (l1 ++ b :: l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 _; simp
  | cons a t ih =>
    intro l2 h
    have h1 := ih l2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hab := h a List.mem_cons_self
    have hΓ := prod_pos' γ hγ (t ++ l2)
    have hmap : ((t ++ b :: l2).map γ).prod = γ b * ((t ++ l2).map γ).prod := by
      simp [List.prod_append]; ring
    have hcross : μ b * (γ a - 1) ≤ μ a * (γ b - 1) := by
      have := (div_le_div_iff₀ (by linarith [hγ b]) (by linarith [hγ a])).1 hab
      linarith
    have key := mul_le_mul_of_nonneg_right hcross hΓ.le
    simp only [Fl, List.cons_append, List.map_cons, List.prod_cons] at h1 ⊢
    rw [hmap]
    nlinarith [key, h1]

lemma sorted_le (μ γ : ι → ℝ) (hγ : ∀ i, 1 < γ i) :
    ∀ (l' l : List ι), l'.Pairwise (fun a b => μ a / (γ a - 1) ≤ μ b / (γ b - 1)) →
      l'.Perm l → Fl μ γ l' ≤ Fl μ γ l := by
  intro l'
  induction l' with
  | nil => intro l _ hp; rw [List.perm_nil.1 hp.symm]
  | cons b s ih =>
    intro l hs hp
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem (hp.subset List.mem_cons_self)
    have hp2 : (b :: s).Perm (b :: (l1 ++ l2)) := hp.trans List.perm_middle
    have hp3 : s.Perm (l1 ++ l2) := hp2.cons_inv
    obtain ⟨hb, hs'⟩ := List.pairwise_cons.1 hs
    have hbound : ∀ x ∈ l1, μ b / (γ b - 1) ≤ μ x / (γ x - 1) := by
      intro x hx
      have : x ∈ b :: s := hp.symm.subset (List.mem_append_left _ hx)
      rcases List.mem_cons.1 this with rfl | h
      · exact le_rfl
      · exact hb x h
    have hprod : (s.map γ).prod = ((l1 ++ l2).map γ).prod := (hp3.map γ).prod_eq
    have h1 := ih (l1 ++ l2) hs' hp3
    calc Fl μ γ (b :: s) = μ b * (s.map γ).prod + Fl μ γ s := rfl
      _ ≤ μ b * ((l1 ++ l2).map γ).prod + Fl μ γ (l1 ++ l2) := by rw [hprod]; linarith
      _ = Fl μ γ (b :: (l1 ++ l2)) := rfl
      _ ≤ _ := move_front μ γ hγ b l1 l2 hbound

lemma Fl_ofFn (μ γ : ι → ℝ) : ∀ (n : ℕ) (f : Fin n → ι),
    Fl μ γ (List.ofFn f) = ∑ i : Fin n, μ (f i) * ∏ r ∈ Finset.Ioi i, γ (f r) := by
  intro n
  induction n with
  | zero => intro f; simp [Fl]
  | succ n ih =>
    intro f
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    simp only [Fl]
    have e0 : ∏ r ∈ Finset.Ioi (0 : Fin (n+1)), γ (f r) = ∏ r : Fin n, γ (f r.succ) := by
      simpa using Fin.prod_Ioi_zero (fun r => γ (f r))
    have e1 : ∀ i : Fin n, ∏ r ∈ Finset.Ioi i.succ, γ (f r) = ∏ r ∈ Finset.Ioi i, γ (f r.succ) := by
      intro i; simpa using Fin.prod_Ioi_succ (fun r => γ (f r)) i
    rw [ih (fun i => f i.succ), e0]
    simp only [e1]
    have : (List.ofFn fun i : Fin n => f i.succ).map γ = List.ofFn fun i : Fin n => γ (f i.succ) := by
      simp [List.map_ofFn]; rfl
    rw [this, List.prod_ofFn]

end lists

lemma min_part {N : ℕ} (μ γ : Fin N → ℝ) (hγ : ∀ i, 1 < γ i) (π : Equiv.Perm (Fin N))
    (hm : Monotone (fun k : Fin N => μ (π k) / (γ (π k) - 1))) (σ : Equiv.Perm (Fin N)) :
    lemma1Sum μ γ π ≤ lemma1Sum μ γ σ := by
  have e : ∀ τ : Equiv.Perm (Fin N), lemma1Sum μ γ τ = Fl μ γ (List.ofFn τ) := fun τ => by
    rw [Fl_ofFn]; rfl
  rw [e, e]
  apply sorted_le μ γ hγ
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hm hij.le
  · have h1 : (List.ofFn π).Nodup := List.nodup_ofFn.2 π.injective
    have h2 : (List.ofFn σ).Nodup := List.nodup_ofFn.2 σ.injective
    rw [List.perm_ext_iff_of_nodup h1 h2]
    intro x
    simp only [List.mem_ofFn, Set.mem_range]
    constructor
    · intro _; exact ⟨σ.symm x, by simp⟩
    · intro _; exact ⟨π.symm x, by simp⟩

theorem lemma1_core {N : ℕ} (μ γ : Fin N → ℝ) (hγ : ∀ i, 1 < γ i)
    (π : Equiv.Perm (Fin N)) :
    (Monotone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ π ≤ lemma1Sum μ γ σ) ∧
      (Antitone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ σ ≤ lemma1Sum μ γ π) := by
  refine ⟨fun hm σ => min_part μ γ hγ π hm σ, fun ha σ => ?_⟩
  have hm : Monotone (fun k : Fin N => (-μ) (π k) / (γ (π k) - 1)) := by
    intro i j hij
    have := ha hij
    simp only [Pi.neg_apply, neg_div] at this ⊢
    linarith
  have := min_part (-μ) γ hγ π hm σ
  have e : ∀ τ : Equiv.Perm (Fin N), lemma1Sum (-μ) γ τ = - lemma1Sum μ γ τ := by
    intro τ; simp [lemma1Sum, Finset.sum_neg_distrib]
  rw [e, e] at this
  linarith

theorem index_rule_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (hα : ∀ i, 0 < α i) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (fun k : Fin N => (∫ ω, X (π k) ω ∂P) / α (π k))) :
    ∀ σ : Equiv.Perm (Fin N), expectedMakespan P X α π ≤ expectedMakespan P X α σ := by
  intro σ
  rw [expmk_core P X hX α π, expmk_core P X hX α σ]
  refine (lemma1_core (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) (fun i => by linarith [hα i]) π).1 ?_ σ
  simpa using hπ

end DeterioratingJobs.Makespan

open DeterioratingJobs.Makespan


theorem solution {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    completionTime X α π k ω =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k),
          (1 + α (π r)) := by
  exact eq2_core X α π k hk ω
