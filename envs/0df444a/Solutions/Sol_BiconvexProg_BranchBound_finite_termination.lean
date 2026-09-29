-- Prove2me | solution 1 for BiconvexProg.BranchBound.finite_termination
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:48:58.733264+00:00
-- url     : https://prove2.me/submissions/865c4133-44a2-45ba-b7e6-828763321218

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

lemma aux_ft_le_upd {n : ℕ} {x L : Fin n → ℝ} {I : Fin n} {a : ℝ}
    (h : x ≤ Function.update L I a) (ha : a ≤ L I) : x ≤ L := by
  intro j
  have hj := h j
  by_cases hjI : j = I
  · subst hjI
    simp at hj
    linarith
  · rwa [Function.update_of_ne hjI] at hj

lemma aux_ft_upd_le {n : ℕ} {x l : Fin n → ℝ} {I : Fin n} {a : ℝ}
    (h : Function.update l I a ≤ x) (ha : l I ≤ a) : l ≤ x := by
  intro j
  have hj := h j
  by_cases hjI : j = I
  · subst hjI
    simp at hj
    linarith
  · rwa [Function.update_of_ne hjI] at hj

lemma aux_ft_le_upd' {n : ℕ} {x L : Fin n → ℝ} {I : Fin n} {a : ℝ}
    (h : x ≤ L) (ha : x I ≤ a) : x ≤ Function.update L I a := by
  intro j
  by_cases hjI : j = I
  · subst hjI
    simpa using ha
  · rw [Function.update_of_ne hjI]
    exact h j

lemma aux_ft_upd_le' {n : ℕ} {x l : Fin n → ℝ} {I : Fin n} {a : ℝ}
    (h : l ≤ x) (ha : a ≤ x I) : Function.update l I a ≤ x := by
  intro j
  by_cases hjI : j = I
  · subst hjI
    simpa using ha
  · rw [Function.update_of_ne hjI]
    exact h j

lemma aux_ft_child_sub {n : ℕ} (B : Box n) (I : Fin n) (a b : ℝ)
    (ha1 : B.l I ≤ a) (ha2 : a ≤ B.L I) (hb1 : B.m I ≤ b) (hb2 : b ≤ B.M I) (c : Fin 4) :
    (B.child I a b c).toSet ⊆ B.toSet := by
  intro w hw
  fin_cases c <;>
    simp only [Box.child, Box.toSet, Set.mem_prod, Set.mem_Icc, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val] at hw ⊢
  · exact ⟨⟨hw.1.1, aux_ft_le_upd hw.1.2 ha2⟩, ⟨hw.2.1, aux_ft_le_upd hw.2.2 hb2⟩⟩
  · exact ⟨⟨aux_ft_upd_le hw.1.1 ha1, hw.1.2⟩, ⟨hw.2.1, aux_ft_le_upd hw.2.2 hb2⟩⟩
  · exact ⟨⟨aux_ft_upd_le hw.1.1 ha1, hw.1.2⟩, ⟨aux_ft_upd_le hw.2.1 hb1, hw.2.2⟩⟩
  · exact ⟨⟨hw.1.1, aux_ft_le_upd hw.1.2 ha2⟩, ⟨aux_ft_upd_le hw.2.1 hb1, hw.2.2⟩⟩

lemma aux_ft_child_cover {n : ℕ} (B : Box n) (I : Fin n) (a b : ℝ)
    (w : (Fin n → ℝ) × (Fin n → ℝ)) (hw : w ∈ B.toSet) :
    ∃ c : Fin 4, w ∈ (B.child I a b c).toSet := by
  simp only [Box.toSet, Set.mem_prod, Set.mem_Icc] at hw
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
  rcases le_total (w.1 I) a with hx | hx <;> rcases le_total (w.2 I) b with hy | hy
  · refine ⟨0, ?_⟩
    simp only [Box.child, Box.toSet, Set.mem_prod, Set.mem_Icc, Matrix.cons_val]
    exact ⟨⟨h1, aux_ft_le_upd' h2 hx⟩, ⟨h3, aux_ft_le_upd' h4 hy⟩⟩
  · refine ⟨3, ?_⟩
    simp only [Box.child, Box.toSet, Set.mem_prod, Set.mem_Icc, Matrix.cons_val]
    exact ⟨⟨h1, aux_ft_le_upd' h2 hx⟩, ⟨aux_ft_upd_le' h3 hy, h4⟩⟩
  · refine ⟨1, ?_⟩
    simp only [Box.child, Box.toSet, Set.mem_prod, Set.mem_Icc, Matrix.cons_val]
    exact ⟨⟨aux_ft_upd_le' h1 hx, h2⟩, ⟨h3, aux_ft_le_upd' h4 hy⟩⟩
  · refine ⟨2, ?_⟩
    simp only [Box.child, Box.toSet, Set.mem_prod, Set.mem_Icc, Matrix.cons_val]
    exact ⟨⟨aux_ft_upd_le' h1 hx, h2⟩, ⟨aux_ft_upd_le' h3 hy, h4⟩⟩

lemma aux_ft_mem_split {n : ℕ} (B : Box n) (I : Fin n) (a b : ℝ) (c : Fin 4) :
    B.child I a b c ∈ B.split I a b := by
  fin_cases c <;> simp [Box.split]

lemma aux_ft_of_mem_split {n : ℕ} (B C : Box n) (I : Fin n) (a b : ℝ)
    (h : C ∈ B.split I a b) : ∃ c : Fin 4, C = B.child I a b c := by
  simp only [Box.split, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at h
  rcases h with h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

lemma aux_ft_env_le {n : ℕ} (B : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ B.toSet) :
    convexEnvelope B.toSet bilin z ≤ bilin z := by
  unfold convexEnvelope
  apply csSup_le
  · have hc : IsCompact B.toSet := isCompact_Icc.prod isCompact_Icc
    have hcont : Continuous (bilin : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) := by
      unfold bilin
      fun_prop
    obtain ⟨c, hc'⟩ := hc.bddBelow_image hcont.continuousOn
    refine ⟨c, fun _ => c, convexOn_const c ((convex_Icc _ _).prod (convex_Icc _ _)), ?_, rfl⟩
    intro w hw
    exact hc' ⟨w, hw, rfl⟩
  · rintro r ⟨g, -, hg, rfl⟩
    exact hg z hz

open Classical in
lemma aux_ft_cover {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n}
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    ∀ k, ∀ z ∈ Ω.toSet, ∃ B ∈ nodes k, z ∈ B.toSet := by
  intro k
  induction k with
  | zero =>
    intro z hz
    exact ⟨Ω, by rw [hrun.init]; simp, hz⟩
  | succ k ih =>
    intro z hz
    obtain ⟨B, hB, hzB⟩ := ih z hz
    rw [hrun.step k]
    by_cases hBs : B = sel k
    · subst hBs
      obtain ⟨c, hc⟩ := aux_ft_child_cover (sel k) (idx k) ((pt k).1 (idx k)) ((pt k).2 (idx k)) z hzB
      exact ⟨_, Multiset.mem_add.2 (Or.inr (aux_ft_mem_split _ _ _ _ c)), hc⟩
    · exact ⟨B, Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hBs).2 hB)), hzB⟩

open Classical in
lemma aux_ft_sub {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n}
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    ∀ k, ∀ B ∈ nodes k, B.toSet ⊆ Ω.toSet := by
  intro k
  induction k with
  | zero =>
    intro B hB
    rw [hrun.init, Multiset.mem_singleton] at hB
    subst hB
    exact subset_rfl
  | succ k ih =>
    intro B hB
    rw [hrun.step k, Multiset.mem_add] at hB
    rcases hB with hB | hB
    · exact ih B (Multiset.mem_of_mem_erase hB)
    · obtain ⟨c, rfl⟩ := aux_ft_of_mem_split _ _ _ _ _ hB
      have hp := (hrun.pt_mem k).2
      simp only [Box.toSet, Set.mem_prod, Set.mem_Icc] at hp
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
      exact (aux_ft_child_sub _ _ _ _ (h1 (idx k)) (h2 (idx k)) (h3 (idx k)) (h4 (idx k)) c).trans
        (ih _ (hrun.sel_mem k))

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (k l : ℕ) (hl : l ≤ k) (hVl : objective f g (pt l) = bestUpper f g pt k)
    (heq : bestLower f g sel pt k = bestUpper f g pt k) :
    pt l ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) (pt l) := by
  refine ⟨⟨(hrun.pt_mem l).1, aux_ft_sub hrun l (sel l) (hrun.sel_mem l) (hrun.pt_mem l).2⟩, ?_⟩
  rw [isMinOn_iff]
  intro z hz
  obtain ⟨B, hB, hzB⟩ := aux_ft_cover hrun k z hz.2
  have h1 := hrun.best_bound k B hB z ⟨hz.1, hzB⟩
  have h2 := aux_ft_env_le B z hzB
  rw [hVl, ← heq]
  unfold bestLower
  calc nodeFun f g (sel k) (pt k) ≤ nodeFun f g B z := h1
    _ ≤ objective f g z := by
      unfold nodeFun objective
      linarith
