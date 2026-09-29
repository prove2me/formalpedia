-- Prove2me | solution 1 for BiconvexProg.BranchBound.bound_chain
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:11:56.860291+00:00
-- url     : https://prove2.me/submissions/a3c897ba-b1ce-4fba-baff-8f828019954e

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

lemma aux_bc_upd_ge {n : ℕ} {f w : Fin n → ℝ} {I : Fin n} {a : ℝ} (hf : f ≤ w) (ha : a ≤ w I) :
    Function.update f I a ≤ w := by
  intro i
  by_cases hi : i = I
  · subst hi; simpa using ha
  · simp [Function.update_of_ne hi, hf i]

lemma aux_bc_upd_le {n : ℕ} {f w : Fin n → ℝ} {I : Fin n} {a : ℝ} (hf : w ≤ f) (ha : w I ≤ a) :
    w ≤ Function.update f I a := by
  intro i
  by_cases hi : i = I
  · subst hi; simpa using ha
  · simp [Function.update_of_ne hi, hf i]

lemma aux_bc_toSet_convex {n : ℕ} (B : Box n) : Convex ℝ B.toSet :=
  (convex_Icc _ _).prod (convex_Icc _ _)

lemma aux_bc_bddBelow {n : ℕ} (B : Box n) : ∃ c : ℝ, ∀ w ∈ B.toSet, c ≤ bilin w := by
  have hc : IsCompact B.toSet := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (bilin : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) := by
    unfold bilin
    fun_prop
  obtain ⟨c, hc'⟩ := hc.bddBelow_image hcont.continuousOn
  exact ⟨c, fun w hw => hc' ⟨w, hw, rfl⟩⟩

lemma aux_bc_env_nonempty {n : ℕ} (B : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    {r : ℝ | ∃ g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ, ConvexOn ℝ B.toSet g ∧
      (∀ w ∈ B.toSet, g w ≤ bilin w) ∧ r = g z}.Nonempty := by
  obtain ⟨c, hc⟩ := aux_bc_bddBelow B
  exact ⟨c, fun _ => c, convexOn_const c (aux_bc_toSet_convex B), hc, rfl⟩

lemma aux_bc_env_bdd {n : ℕ} (B : Box n) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ B.toSet) :
    BddAbove {r : ℝ | ∃ g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ, ConvexOn ℝ B.toSet g ∧
      (∀ w ∈ B.toSet, g w ≤ bilin w) ∧ r = g z} := by
  refine ⟨bilin z, ?_⟩
  rintro r ⟨g, -, hle, rfl⟩
  exact hle z hz

lemma aux_bc_env_le {n : ℕ} (B : Box n) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ B.toSet) :
    convexEnvelope B.toSet bilin z ≤ bilin z := by
  unfold convexEnvelope
  apply csSup_le (aux_bc_env_nonempty B z)
  rintro r ⟨g, -, hle, rfl⟩
  exact hle z hz

lemma aux_bc_env_mono {n : ℕ} {B C : Box n} (hCB : C.toSet ⊆ B.toSet)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ C.toSet) :
    convexEnvelope B.toSet bilin z ≤ convexEnvelope C.toSet bilin z := by
  unfold convexEnvelope
  apply csSup_le_csSup (aux_bc_env_bdd C hz) (aux_bc_env_nonempty B z)
  rintro r ⟨g, hg, hle, rfl⟩
  exact ⟨g, hg.subset hCB (aux_bc_toSet_convex C), fun w hw => hle w (hCB hw), rfl⟩

lemma aux_bc_split_sub {n : ℕ} {B C : Box n} {I : Fin n} {a b : ℝ}
    (ha : a ∈ Set.Icc (B.l I) (B.L I)) (hb : b ∈ Set.Icc (B.m I) (B.M I))
    (hC : C ∈ B.split I a b) : C.toSet ⊆ B.toSet := by
  have h1 : B.l ≤ Function.update B.l I a := aux_bc_upd_le le_rfl ha.1
  have h2 : Function.update B.L I a ≤ B.L := aux_bc_upd_ge le_rfl ha.2
  have h3 : B.m ≤ Function.update B.m I b := aux_bc_upd_le le_rfl hb.1
  have h4 : Function.update B.M I b ≤ B.M := aux_bc_upd_ge le_rfl hb.2
  simp only [Box.split, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hC
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  rcases hC with rfl | rfl | rfl | rfl
  · exact ⟨⟨hx1, hx2.trans h2⟩, ⟨hy1, hy2.trans h4⟩⟩
  · exact ⟨⟨h1.trans hx1, hx2⟩, ⟨hy1, hy2.trans h4⟩⟩
  · exact ⟨⟨h1.trans hx1, hx2⟩, ⟨h3.trans hy1, hy2⟩⟩
  · exact ⟨⟨hx1, hx2.trans h2⟩, ⟨h3.trans hy1, hy2⟩⟩

lemma aux_bc_split_cover {n : ℕ} {B : Box n} {I : Fin n} {a b : ℝ}
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ B.toSet) :
    ∃ C ∈ B.split I a b, z ∈ C.toSet := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hz
  rcases le_total (z.1 I) a with hxa | hxa <;> rcases le_total (z.2 I) b with hyb | hyb
  · exact ⟨B.child I a b 0, by simp [Box.split],
      ⟨⟨hx1, aux_bc_upd_le hx2 hxa⟩, ⟨hy1, aux_bc_upd_le hy2 hyb⟩⟩⟩
  · exact ⟨B.child I a b 3, by simp [Box.split],
      ⟨⟨hx1, aux_bc_upd_le hx2 hxa⟩, ⟨aux_bc_upd_ge hy1 hyb, hy2⟩⟩⟩
  · exact ⟨B.child I a b 1, by simp [Box.split],
      ⟨⟨aux_bc_upd_ge hx1 hxa, hx2⟩, ⟨hy1, aux_bc_upd_le hy2 hyb⟩⟩⟩
  · exact ⟨B.child I a b 2, by simp [Box.split],
      ⟨⟨aux_bc_upd_ge hx1 hxa, hx2⟩, ⟨aux_bc_upd_ge hy1 hyb, hy2⟩⟩⟩

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (zstar : (Fin n → ℝ) × (Fin n → ℝ)) (hzs : zstar ∈ S ∩ Ω.toSet)
    (hmin : IsMinOn (objective f g) (S ∩ Ω.toSet) zstar) :
    Monotone (bestLower f g sel pt) ∧ Antitone (bestUpper f g pt) ∧
      ∀ k, bestLower f g sel pt k ≤ objective f g zstar ∧
        objective f g zstar ≤ bestUpper f g pt k := by
  classical
  have hab : ∀ k, (pt k).1 (idx k) ∈ Set.Icc ((sel k).l (idx k)) ((sel k).L (idx k)) ∧
      (pt k).2 (idx k) ∈ Set.Icc ((sel k).m (idx k)) ((sel k).M (idx k)) := by
    intro k
    have hpt := (hrun.pt_mem k).2
    exact ⟨⟨hpt.1.1 _, hpt.1.2 _⟩, ⟨hpt.2.1 _, hpt.2.2 _⟩⟩
  have hinv : ∀ k, (∀ B ∈ nodes k, B.toSet ⊆ Ω.toSet) ∧ ∃ B ∈ nodes k, zstar ∈ B.toSet := by
    intro k
    induction k with
    | zero =>
      rw [hrun.init]
      refine ⟨fun B hB => ?_, Ω, Multiset.mem_singleton_self _, hzs.2⟩
      rw [Multiset.mem_singleton] at hB
      subst hB
      exact le_rfl
    | succ k ih =>
      obtain ⟨hsub, B, hB, hzB⟩ := ih
      rw [hrun.step k]
      refine ⟨fun C hC => ?_, ?_⟩
      · rcases Multiset.mem_add.1 hC with h | h
        · exact hsub C (Multiset.mem_of_mem_erase h)
        · exact (aux_bc_split_sub (hab k).1 (hab k).2 h).trans (hsub _ (hrun.sel_mem k))
      · by_cases hBs : B = sel k
        · rw [hBs] at hzB
          obtain ⟨C, hC, hzC⟩ := aux_bc_split_cover (I := idx k) (a := (pt k).1 (idx k))
            (b := (pt k).2 (idx k)) hzB
          exact ⟨C, Multiset.mem_add.2 (Or.inr hC), hzC⟩
        · exact ⟨B, Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hBs).2 hB)), hzB⟩
  refine ⟨?_, ?_, fun k => ⟨?_, ?_⟩⟩
  · apply monotone_nat_of_le_succ
    intro k
    unfold bestLower
    have hsel := hrun.sel_mem (k + 1)
    rw [hrun.step k] at hsel
    rcases Multiset.mem_add.1 hsel with h | h
    · exact hrun.best_bound k _ (Multiset.mem_of_mem_erase h) _ (hrun.pt_mem (k + 1))
    · have hsub := aux_bc_split_sub (hab k).1 (hab k).2 h
      have hz := hrun.pt_mem (k + 1)
      calc nodeFun f g (sel k) (pt k) ≤ nodeFun f g (sel k) (pt (k + 1)) :=
            hrun.best_bound k _ (hrun.sel_mem k) _ ⟨hz.1, hsub hz.2⟩
        _ ≤ nodeFun f g (sel (k + 1)) (pt (k + 1)) := by
            unfold nodeFun
            have := aux_bc_env_mono hsub hz.2
            linarith
  · intro i j hij
    unfold bestUpper
    exact Finset.inf'_mono _ (Finset.range_subset_range.2 (by omega)) _
  · obtain ⟨-, B, hB, hzB⟩ := hinv k
    unfold bestLower
    calc nodeFun f g (sel k) (pt k) ≤ nodeFun f g B zstar :=
          hrun.best_bound k B hB zstar ⟨hzs.1, hzB⟩
      _ ≤ objective f g zstar := by
        unfold nodeFun objective
        have := aux_bc_env_le B hzB
        linarith
  · unfold bestUpper
    apply Finset.le_inf'
    intro l _
    have hsub := (hinv l).1 _ (hrun.sel_mem l)
    exact isMinOn_iff.1 hmin _ ⟨(hrun.pt_mem l).1, hsub (hrun.pt_mem l).2⟩
