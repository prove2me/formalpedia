-- Prove2me | solution 1 for ChanPangGQVI.Contraction.proj_translate
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:54:30.369574+00:00
-- url     : https://prove2.me/submissions/8dd15736-01fc-47d0-be2b-94415c28fd20

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
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.proj (Kmap m Ktil x) y =
      m x + ChanPangGQVI.Shared.proj Ktil (y - m x) := by
  have hp := proj_spec Ktil (y-m x) (nearest_exists Ktil hK_ne hK_closed hK_convex (y-m x))
  have he : ∃ q, IsProj (Kmap m Ktil x) y q := by
    refine ⟨m x + proj Ktil (y-m x), ⟨_, hp.1, rfl⟩, ?_⟩
    rintro q ⟨k,hk,rfl⟩
    have hid (a : EuclideanSpace ℝ (Fin n)) : m x + a - y = a - (y-m x) := by abel
    rw [hid, hid]
    exact hp.2 k hk
  have hq := proj_spec (Kmap m Ktil x) y he
  have hback : IsProj Ktil (y-m x) (proj (Kmap m Ktil x) y - m x) := by
    constructor
    · obtain ⟨k,hk,hkeq⟩ := hq.1
      rw [hkeq]
      simpa using hk
    · intro k hk
      have h := hq.2 (m x+k) ⟨k,hk,rfl⟩
      have hleft : proj (Kmap m Ktil x) y - m x - (y-m x) = proj (Kmap m Ktil x) y - y := by abel
      have hright : k - (y-m x) = m x+k-y := by abel
      simpa only [hleft, hright] using h
  have hh := nearest_unique Ktil hK_convex (y-m x) _ _ hback hp
  rw [← hh]
  abel
