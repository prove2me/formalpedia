-- Prove2me | solution 1 for ChanPangGQVI.Contraction.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:58:01.825289+00:00
-- url     : https://prove2.me/submissions/b7f38072-b1c2-4507-afd7-5cb12c80f748

import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic
import Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap
set_option autoImplicit false
open ChanPangGQVI.Shared ChanPangGQVI.Contraction
open scoped InnerProductSpace

private theorem nearest_exists {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hne : S.Nonempty) (hc : IsClosed S) (hcv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ∃ p, IsProj S z p := by
  letI : Nonempty S := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : S => ‖z - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv z
  refine ⟨p, hp, ?_⟩
  intro y hy
  rw [norm_sub_rev p z, norm_sub_rev y z, hmin]
  exact ciInf_le hb ⟨y, hy⟩

private theorem proj_spec {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) (he : ∃ p, IsProj S z p) : IsProj S z (proj S z) := by
  classical
  simpa only [proj, dif_pos he] using he.choose_spec

private theorem nearest_inner {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (z p : EuclideanSpace ℝ (Fin n)) (hp : IsProj S z p) :
    ∀ q ∈ S, inner ℝ (z-p) (q-p) ≤ 0 := by
  letI : Nonempty S := ⟨⟨p,hp.1⟩⟩
  have hb : BddBelow (Set.range (fun y : S => ‖z-y‖)) := ⟨0, by
    rintro _ ⟨y,rfl⟩
    exact norm_nonneg _⟩
  apply (norm_eq_iInf_iff_real_inner_le_zero hcv hp.1).mp
  apply le_antisymm
  · apply le_ciInf
    intro q
    simpa only [norm_sub_rev z p, norm_sub_rev z q] using hp.2 q q.2
  · exact ciInf_le hb ⟨p,hp.1⟩

private theorem nearest_unique {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (z p q : EuclideanSpace ℝ (Fin n))
    (hp : IsProj S z p) (hq : IsProj S z q) : p=q := by
  have h1 := nearest_inner S hcv z p hp q hq.1
  have h2 := nearest_inner S hcv z q hq p hp.1
  have hh : inner ℝ (p-q) (p-q) ≤ 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm q p] at *
    linarith
  have hn : ‖p-q‖=0 := by
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem solution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (xs ys : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsGQVISolution K f xs ys ↔
      (ChanPangGQVI.Shared.IsProj (K xs) (xs - ys) xs ∧ ys ∈ f xs) := by
  constructor
  · rintro ⟨hx,hy,hineq⟩
    refine ⟨⟨hx,?_⟩,hy⟩
    intro q hq
    have hi := hineq q hq
    have he : q-(xs-ys) = (q-xs)+ys := by abel
    rw [sub_sub_cancel, he]
    have hn := norm_add_sq_real (q-xs) ys
    nlinarith [norm_nonneg ((q-xs)+ys), norm_nonneg ys, sq_nonneg ‖q-xs‖]
  · rintro ⟨hp,hy⟩
    refine ⟨hp.1,hy,?_⟩
    intro q hq
    have h := nearest_inner (K xs) (hK_convex xs) (xs-ys) xs hp q hq
    have he : xs-ys-xs = -ys := by abel
    rw [he, inner_neg_left] at h
    have hic : inner ℝ ys (q-xs) = inner ℝ (q-xs) ys := real_inner_comm _ _
    linarith
