-- Prove2me | solution 1 for ConvexSDDP.Det.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:01:18.464983+00:00
-- url     : https://prove2.me/submissions/eec34bb5-b0ee-4abd-a2d7-133d97d0637d

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic

set_option autoImplicit false
open ConvexSDDP.Det

theorem csd_ereal_le_of_forall {z : EReal} {r : ℝ} (h : ∀ ε : ℝ, 0 < ε → z ≤ ((r + ε : ℝ) : EReal)) :
    z ≤ (r : EReal) := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  induction a using EReal.rec with
  | bot => exact absurd ha (not_lt_bot)
  | top => exact le_top
  | coe s =>
    have hs : r < s := by exact_mod_cast ha
    have := h (s - r) (by linarith)
    simpa using this

theorem solution {d p : ℕ}
    (J : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p) → EReal)
    (hJbot : ∀ x u, J x u ≠ ⊥)
    (hJ : EConvex (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => J z.1 z.2))
    (U : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin p)))
    (hU : ConvexMultifunction U) :
    EConvex (fun x => ⨅ u ∈ U x, J x u) ∧
      ((∀ x, LowerSemicontinuous (J x)) → (∀ x, IsCompact (U x) ∧ (U x).Nonempty) →
        ∀ x, ∃ u ∈ U x, J x u = ⨅ v ∈ U x, J x v) := by
  refine ⟨?_, ?_⟩
  · intro P hP Q hQ a b ha hb hab
    simp only [Set.mem_setOf_eq] at hP hQ ⊢
    obtain ⟨x1, r1⟩ := P
    obtain ⟨x2, r2⟩ := Q
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hP hQ ⊢
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      subst hb1; rw [← ha0]; simpa using hQ
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have ha1 : a = 1 := by linarith
      subst ha1; rw [← hb0]; simpa using hP
    -- main case
    have hb1 : b < 1 := by linarith
    have ha' : a = 1 - b := by linarith
    apply csd_ereal_le_of_forall
    intro ε hε
    have hP' : (⨅ u ∈ U x1, J x1 u) < ((r1 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hP (by exact_mod_cast (by linarith : r1 < r1 + ε))
    have hQ' : (⨅ u ∈ U x2, J x2 u) < ((r2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hQ (by exact_mod_cast (by linarith : r2 < r2 + ε))
    simp only [iInf_lt_iff] at hP' hQ'
    obtain ⟨u1, hu1, hJ1⟩ := hP'
    obtain ⟨u2, hu2, hJ2⟩ := hQ'
    have hmem := hJ (show ((x1, u1), r1 + ε) ∈ {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) × ℝ | J q.1.1 q.1.2 ≤ (q.2 : EReal)} from hJ1.le)
      (show ((x2, u2), r2 + ε) ∈ {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) × ℝ | J q.1.1 q.1.2 ≤ (q.2 : EReal)} from hJ2.le)
      ha hb hab
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
    have hu : a • u1 + b • u2 ∈ U (a • x1 + b • x2) := by
      have := hU x1 x2 u1 hu1 u2 hu2 b hb0 hb1
      rw [← ha'] at this
      exact this
    calc (⨅ u ∈ U (a • x1 + b • x2), J (a • x1 + b • x2) u)
        ≤ J (a • x1 + b • x2) (a • u1 + b • u2) := iInf₂_le _ hu
      _ ≤ ((a * (r1 + ε) + b * (r2 + ε) : ℝ) : EReal) := hmem
      _ = ((a * r1 + b * r2 + ε : ℝ) : EReal) := by
          congr 1; nlinarith
  · intro hl hc x
    obtain ⟨u, hu, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hc x).2 (hc x).1
      ((hl x).lowerSemicontinuousOn _)
    refine ⟨u, hu, le_antisymm (le_iInf₂ fun v hv => ?_) (iInf₂_le u hu)⟩
    exact hmin hv
