-- Prove2me | solution 1 for FlowJobHardness.ColoringReduction.coloring_reduction_gap
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:25:53.357881+00:00
-- url     : https://prove2.me/submissions/ca7e8e8e-90b1-44ec-93ef-1953c01df789

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule
import Theorems.Thm_FlowJobHardness_ColoringReduction_remark_3_6
import Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_7
import Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_9

open JobShopLTAS.Core

namespace CGAux
open FlowJobHardness.ColoringReduction

theorem lexlt {a b x y m : ℕ} (hx : x < m) (hy : y < m) (h : a * m + x < b * m + y) :
    a < b ∨ (a = b ∧ x < y) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact Or.inl h1
  · subst h1; exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right _ h1
    nlinarith

theorem lexeq {a b x y m : ℕ} (hx : x < m) (hy : y < m) (h : a * m + x = b * m + y) :
    a = b ∧ x = y := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exfalso
    have : (a + 1) * m ≤ b * m := Nat.mul_le_mul_right _ h1
    nlinarith
  · subst h1; exact ⟨rfl, by omega⟩
  · exfalso
    have : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right _ h1
    nlinarith

theorem div_eq_iff' {x k a : ℕ} (hk : 0 < k) : x / k = a ↔ a * k ≤ x ∧ x < a * k + k := by
  constructor
  · rintro rfl
    have h1 := Nat.div_add_mod' x k
    have h2 := Nat.mod_lt x hk
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have : x / k < a + 1 := (Nat.div_lt_iff_lt_mul hk).2 (by linarith [Nat.add_mul a 1 k])
      omega
    · exact (Nat.le_div_iff_mul_le hk).2 h1

variable {n d : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d)) {r : ℕ}

theorem pos_of_fin (q : Fin (size r d n)) : 0 < n ∧ 0 < R r d := by
  have := q.isLt
  unfold size at this
  constructor
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at this
    · exact h
  · rcases Nat.eq_zero_or_pos (R r d) with h | h
    · simp [h] at this
    · exact h

theorem freq_pos (v : Fin n) : 1 ≤ freq c v := by unfold freq; omega
theorem freq_le (v : Fin n) : freq c v ≤ d := by unfold freq; have := (c v).isLt; omega

theorem kl_eq (f : ℕ) (hf : f ≤ d) : r ^ (2 * f) * r ^ (2 * (d - f)) = R r d := by
  unfold R; rw [← pow_add]; congr 1; omega

theorem machVtx_val (p : Fin (size r d n)) : (machVtx p).val = p.val % n := rfl
theorem jobVtx_val (q : Fin (size r d n)) : (jobVtx q).val = q.val / R r d := rfl

theorem kpos (q : Fin (size r d n)) : 0 < r ^ (2 * jobFreq c q) := by
  have h := (pos_of_fin q).2
  rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)] at h
  exact Nat.pos_of_mul_pos_right h

theorem lpos (q : Fin (size r d n)) : 0 < r ^ (2 * (d - jobFreq c q)) := by
  have h := (pos_of_fin q).2
  rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)] at h
  exact Nat.pos_of_mul_pos_left h

theorem isLong_iff (q p : Fin (size r d n)) :
    IsLong c q p ↔ machVtx p = jobVtx q ∧
      (p.val / n) / r ^ (2 * jobFreq c q) = jobLocal q / r ^ (2 * jobFreq c q) := by
  unfold IsLong jobGroup FlowJobHardness.FlowShopGap.machGroup
  simp only [Nat.add_sub_cancel]
  rw [div_eq_iff' (kpos c q)]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩

/-! machine keys -/

theorem key_parts (p : Fin (size r d n)) :
    d - freq c (machVtx p) < d ∧ p.val % n < n := by
  have h1 := freq_pos c (machVtx p)
  have h2 := freq_le c (machVtx p)
  exact ⟨by omega, Nat.mod_lt _ (pos_of_fin p).1⟩

theorem machKey_inj {p p' : Fin (size r d n)} (h : machKey c p = machKey c p') : p = p' := by
  unfold machKey at h
  obtain ⟨a1, b1⟩ := key_parts c p
  obtain ⟨a2, b2⟩ := key_parts c p'
  obtain ⟨h1, h2⟩ := lexeq b1 b2 h
  obtain ⟨h3, -⟩ := lexeq a1 a2 h1
  apply Fin.ext
  rw [← Nat.div_add_mod' p.val n, ← Nat.div_add_mod' p'.val n, h3, h2]

theorem machBefore_of_key_lt {p p' : Fin (size r d n)} (h : machKey c p < machKey c p') :
    MachBefore c p p' := by
  unfold machKey at h
  obtain ⟨a1, b1⟩ := key_parts c p
  obtain ⟨a2, b2⟩ := key_parts c p'
  have f1 := freq_pos c (machVtx p)
  have f2 := freq_le c (machVtx p)
  have f3 := freq_pos c (machVtx p')
  have f4 := freq_le c (machVtx p')
  unfold MachBefore FlowJobHardness.FlowShopGap.machGroup
  rcases lexlt b1 b2 h with h1 | ⟨h1, h2⟩
  · rcases lexlt a1 a2 h1 with h3 | ⟨h3, h4⟩
    · left; omega
    · right; left; exact ⟨by omega, by omega⟩
  · obtain ⟨h3, h4⟩ := lexeq a1 a2 h1
    right; right
    refine ⟨by omega, by omega, ?_⟩
    rw [Fin.lt_def, machVtx_val, machVtx_val]; exact h2

/-! the operation list -/

theorem opList_pairwise (q : Fin (size r d n)) :
    (opList c q).Pairwise (fun a b => machKey c a ≤ machKey c b) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (machKey c a ≤ machKey c b))
    (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) (jobMachines c q).toList
  unfold opList
  simpa using this

theorem opList_nodup (q : Fin (size r d n)) : (opList c q).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem mem_opList (q p : Fin (size r d n)) : p ∈ opList c q ↔ p ∈ jobMachines c q := by
  unfold opList; rw [List.mem_mergeSort, Finset.mem_toList]

theorem key_strict (q : Fin (size r d n)) {i j : Fin (opList c q).length} (h : i < j) :
    machKey c ((opList c q).get i) < machKey c ((opList c q).get j) := by
  have h1 := List.pairwise_iff_get.1 (opList_pairwise c q) i j h
  have h2 : (opList c q).get i ≠ (opList c q).get j := by
    intro e; rw [(opList_nodup c q).get_inj_iff] at e; exact absurd e (ne_of_lt h)
  rcases lt_or_eq_of_le h1 with h3 | h3
  · exact h3
  · exact absurd (machKey_inj c h3) h2

theorem key_lt_iff (q : Fin (size r d n)) {i j : Fin (opList c q).length} :
    machKey c ((opList c q).get i) < machKey c ((opList c q).get j) ↔ i < j := by
  constructor
  · intro h
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact h1
    · subst h1; omega
    · have := key_strict c q h1; omega
  · exact key_strict c q

theorem get_mem (q : Fin (size r d n)) (i : Fin (opList c q).length) :
    (opList c q).get i ∈ jobMachines c q := (mem_opList c q _).1 (List.get_mem _ _)

theorem part_a (r : ℕ) : ∀ q : Fin (size r d n), ∀ i i' : Fin ((inst G c r).μ q), i < i' →
    MachBefore c ((inst G c r).π q i) ((inst G c r).π q i') := by
  intro q i i' h
  exact machBefore_of_key_lt c (key_strict c q h)


end CGAux

open FlowJobHardness.ColoringReduction in
theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d))
    (r : ℕ) (hr : 8 ≤ r) :
    (∀ q : Fin (size r d n), ∀ i i' : Fin ((inst G c r).μ q), i < i' →
        MachBefore c ((inst G c r).π q i) ((inst G c r).π q i')) ∧
    (∀ q : Fin (size r d n), (inst G c r).jobLength q = (R r d : ℝ)) ∧
    (∀ p : Fin (size r d n), (inst G c r).load p = (R r d : ℝ)) ∧
    (∀ K : ℕ, G.Colorable K →
      ∃ s : (inst G c r).Op → ℝ,
        (inst G c r).IsFeasibleSchedule Finset.univ s ∧
        (inst G c r).makespan Finset.univ s ≤ 2 * (K : ℝ) * (R r d : ℝ)) ∧
    (∀ L : ℝ, 0 < L → L ≤ r →
      (∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → (I.card : ℝ) < (n : ℝ) / (8 * L)) →
      ∀ s : (inst G c r).Op → ℝ, (inst G c r).IsFeasibleSchedule Finset.univ s →
        2 * (finishedCount G c r s L : ℝ) < (size r d n : ℝ)) := by
  classical
  have h36 := FlowJobHardness.ColoringReduction.remark_3_6 G c r
  refine ⟨CGAux.part_a c r, h36.1, h36.2.1, fun K hK => FlowJobHardness.ColoringReduction.lemma_3_7 G c r K hK, ?_⟩
  intro L hL0 hLr hind s hs
  by_contra hcon
  push_neg at hcon
  obtain ⟨I, hI, hcard⟩ := FlowJobHardness.ColoringReduction.lemma_3_9 G c r hr L hL0 hLr s hs hcon
  have := hind I hI
  linarith
