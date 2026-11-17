-- Prove2me | solution 1 for DetANN.HPIM.build_struct
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:18:30.788722+00:00
-- url     : https://prove2.me/submissions/ef53ceee-25b5-443f-8b0c-bb9bd1d56ff5

import Mathlib
import Definitions.Def_DetANN_HPIMBuild

namespace DetANN.HPIM

variable {m : ℕ}

/-! ## Boxes -/

lemma inBox_split {lo hi q : Fin m → ℝ} (k : Fin m) (x : ℝ) (hq : InBox lo hi q) :
    InBox lo (setCoord hi k x) q ∨ InBox (setCoord lo k x) hi q := by
  rcases le_or_gt (q k) x with h | h
  · left
    intro j
    refine ⟨(hq j).1, ?_⟩
    unfold setCoord
    split_ifs with hj
    · have : j = k := Fin.ext hj
      subst this; exact h
    · exact (hq j).2
  · right
    intro j
    refine ⟨?_, (hq j).2⟩
    unfold setCoord
    split_ifs with hj
    · have : j = k := Fin.ext hj
      subst this; exact h.le
    · exact (hq j).1

section Carve

variable (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m)

lemma carve_box (hb : ∀ lo hi, (bld lo hi).box = (lo, hi)) :
    ∀ d k lo hi, (carve tlo thi bld d k lo hi).box = (lo, hi) := by
  intro d
  induction d with
  | zero => intro k lo hi; exact hb lo hi
  | succ d ih =>
    intro k lo hi
    simp only [carve]
    split_ifs <;> first | rfl | exact ih _ _ _ | exact hb _ _

lemma carve_covers (hb : ∀ lo hi, (bld lo hi).box = (lo, hi)) :
    ∀ d k lo hi, (∀ B ∈ carveBoxes tlo thi d k lo hi, (bld B.1 B.2).Covers) →
      (carve tlo thi bld d k lo hi).Covers := by
  intro d
  induction d with
  | zero => intro k lo hi h; simpa [carve, carveBoxes] using h
  | succ d ih =>
    intro k lo hi h
    simp only [carve]
    simp only [carveBoxes] at h
    by_cases hk : k < m
    · rw [dif_pos hk] at h ⊢
      set kk : Fin m := ⟨k, hk⟩
      by_cases hlow : lo kk < tlo kk
      · simp only [if_pos hlow] at h ⊢
        have h0 := h _ (List.mem_cons_self ..)
        have h' : ∀ B ∈ (if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) (setCoord lo k (tlo kk)) (setCoord hi k (thi kk)) ++
              [(setCoord (setCoord lo k (tlo kk)) k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) (setCoord lo k (tlo kk)) hi), (bld B.1 B.2).Covers :=
          fun B hB => h B (List.mem_cons_of_mem _ hB)
        refine ⟨fun q hq => ?_, h0, ?_⟩
        · have hrest : (if hi kk > thi kk then
              BSP.cut (setCoord lo k (tlo kk)) hi
                (carve tlo thi bld d (k + 1) (setCoord lo k (tlo kk)) (setCoord hi k (thi kk)))
                (bld (setCoord (setCoord lo k (tlo kk)) k (thi kk)) hi)
            else carve tlo thi bld d (k + 1) (setCoord lo k (tlo kk)) hi).box =
              (setCoord lo k (tlo kk), hi) := by
            split_ifs <;> first | rfl | exact carve_box tlo thi bld hb _ _ _ _
          rw [hb, hrest]
          exact inBox_split kk (tlo kk) hq
        · split_ifs with hhi
          · simp only [if_pos hhi] at h'
            refine ⟨fun q hq => ?_, ih _ _ _ fun B hB => h' B (List.mem_append_left _ hB),
              h' _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
            rw [carve_box tlo thi bld hb, hb]
            exact inBox_split kk (thi kk) hq
          · simp only [if_neg hhi] at h'
            exact ih _ _ _ h'
      · simp only [if_neg hlow] at h ⊢
        split_ifs with hhi
        · simp only [if_pos hhi] at h
          refine ⟨fun q hq => ?_, ih _ _ _ fun B hB => h B (List.mem_append_left _ hB),
            h _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
          rw [carve_box tlo thi bld hb, hb]
          exact inBox_split kk (thi kk) hq
        · simp only [if_neg hhi] at h
          exact ih _ _ _ h
    · rw [dif_neg hk] at h ⊢
      exact h _ (List.mem_singleton_self _)

lemma carve_certified {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) :
    ∀ d k lo hi, (∀ B ∈ carveBoxes tlo thi d k lo hi, (bld B.1 B.2).Certified pts r c) →
      (carve tlo thi bld d k lo hi).Certified pts r c := by
  intro d
  induction d with
  | zero => intro k lo hi h; simpa [carve, carveBoxes] using h
  | succ d ih =>
    intro k lo hi h
    simp only [carve]
    simp only [carveBoxes] at h
    by_cases hk : k < m
    · rw [dif_pos hk] at h ⊢
      set kk : Fin m := ⟨k, hk⟩
      have hrest : ∀ lo', (∀ B ∈ (if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi kk)) ++
              [(setCoord lo' k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) lo' hi), (bld B.1 B.2).Certified pts r c) →
          (if hi kk > thi kk then
              BSP.cut lo' hi (carve tlo thi bld d (k + 1) lo' (setCoord hi k (thi kk)))
                (bld (setCoord lo' k (thi kk)) hi)
            else carve tlo thi bld d (k + 1) lo' hi).Certified pts r c := by
        intro lo' h'
        split_ifs with hhi
        · simp only [if_pos hhi] at h'
          exact ⟨ih _ _ _ fun B hB => h' B (List.mem_append_left _ hB),
            h' _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
        · simp only [if_neg hhi] at h'
          exact ih _ _ _ h'
      by_cases hlow : lo kk < tlo kk
      · simp only [if_pos hlow] at h ⊢
        exact ⟨h _ (List.mem_cons_self ..), hrest _ fun B hB => h B (List.mem_cons_of_mem _ hB)⟩
      · simp only [if_neg hlow] at h ⊢
        exact hrest _ h
    · rw [dif_neg hk] at h ⊢
      exact h _ (List.mem_singleton_self _)

end Carve

/-! ## M2a -/

section Build

variable {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ)

theorem build_box : ∀ f lo hi, (build pts r c f lo hi).box = (lo, hi) := by
  intro f
  induction f with
  | zero => intro lo hi; simp [build, BSP.box]
  | succ f ih =>
    intro lo hi
    simp only [build]
    split_ifs
    · rfl
    · exact carve_box _ _ _ ih _ _ _ _
    · split <;> rfl
    · rfl

theorem build_covers : ∀ f lo hi, (build pts r c f lo hi).Covers := by
  intro f
  induction f with
  | zero => intro lo hi; simp [build, BSP.Covers]
  | succ f ih =>
    intro lo hi
    simp only [build]
    split_ifs
    · trivial
    · exact carve_covers _ _ _ (build_box pts r c f) _ _ _ _ fun B _ => ih _ _
    · split
      · trivial
      · rename_i k _
        refine ⟨fun q hq => ?_, ih _ _, ih _ _⟩
        rw [build_box, build_box]
        exact inBox_split k _ hq
    · trivial

theorem build_certified : ∀ f lo hi, ¬ Starves pts r c f lo hi →
    (build pts r c f lo hi).Certified pts r c := by
  intro f
  induction f with
  | zero => intro lo hi h; exact absurd trivial h
  | succ f ih =>
    intro lo hi hs
    simp only [Starves] at hs
    simp only [build]
    split_ifs at hs ⊢ with hn hg hσ
    · -- an IN leaf
      refine ⟨Fin.isLt _, ?_⟩
      have := Finset.min'_mem _ hg
      exact (Finset.mem_filter.1 this).2
    · -- carve
      refine carve_certified _ _ _ pts r c _ _ _ _ fun B hB => ih _ _ fun h => hs ⟨B, hB, h⟩
    · -- split at the longest axis
      rcases hk : longestAxis lo hi with _ | k
      · simp only [hk] at hs; exact absurd trivial hs
      · simp only [hk] at hs ⊢
        push Not at hs
        exact ⟨ih _ _ hs.1, ih _ _ hs.2⟩
    · -- no near point: an OUT leaf
      intro i
      by_contra h
      push Not at h
      exact hn ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

end Build

end DetANN.HPIM

open DetANN.HPIM in
theorem solution {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) (f : ℕ) (lo hi : Fin m → ℝ) :
    (build pts r c f lo hi).box = (lo, hi) ∧ (build pts r c f lo hi).Covers ∧
      (¬ Starves pts r c f lo hi → (build pts r c f lo hi).Certified pts r c) :=
  ⟨build_box pts r c f lo hi, build_covers pts r c f lo hi, build_certified pts r c f lo hi⟩
