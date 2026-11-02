-- Prove2me | solution 1 for EthierKurtz.oblique_boundary_local_solver_general_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:29:16.932467+00:00
-- url     : https://prove2.me/submissions/92e64aff-100a-47f2-a9f3-5c91bcfd51da

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

section Comp2

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Second derivative of `g ∘ f`: `(v, w) ↦ Dg (D2f v w) + D2g (Df v) (Df w)`. -/
noncomputable def D2comp (Dg : F →L[ℝ] G) (D2g : F →L[ℝ] F →L[ℝ] G) (Df : E →L[ℝ] F)
    (D2f : E →L[ℝ] E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] G :=
  (ContinuousLinearMap.compL ℝ E F G Dg).comp D2f +
    ((ContinuousLinearMap.compL ℝ E F G).flip Df).comp (D2g.comp Df)

lemma D2comp_apply (Dg : F →L[ℝ] G) (D2g : F →L[ℝ] F →L[ℝ] G) (Df : E →L[ℝ] F)
    (D2f : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    D2comp Dg D2g Df D2f v w = Dg (D2f v w) + D2g (Df v) (Df w) := by
  simp [D2comp]

lemma hasFDerivAt_Dcomp {f : E → F} {Df : E → E →L[ℝ] F} {Dg : F → F →L[ℝ] G}
    {D2f : E →L[ℝ] E →L[ℝ] F} {D2g : F →L[ℝ] F →L[ℝ] G} {x : E}
    (hf : HasFDerivAt f (Df x) x) (hDf : HasFDerivAt Df D2f x) (hDg : HasFDerivAt Dg D2g (f x)) :
    HasFDerivAt (fun y => (Dg (f y)).comp (Df y)) (D2comp (Dg (f x)) D2g (Df x) D2f) x := by
  have h1 : HasFDerivAt (fun y => Dg (f y)) (D2g.comp (Df x)) x := hDg.comp x hf
  exact h1.clm_comp hDf

lemma D2comp_norm_le {Dg : F →L[ℝ] G} {D2g : F →L[ℝ] F →L[ℝ] G} {Df : E →L[ℝ] F}
    {D2f : E →L[ℝ] E →L[ℝ] F} {A1 A2 B1 B2 : ℝ} (hA1 : ‖Dg‖ ≤ A1) (hA2 : ‖D2g‖ ≤ A2)
    (hB1 : ‖Df‖ ≤ B1) (hB2 : ‖D2f‖ ≤ B2) :
    ‖D2comp Dg D2g Df D2f‖ ≤ A1 * B2 + A2 * B1 ^ 2 := by
  have hA1' := (norm_nonneg _).trans hA1
  have hA2' := (ContinuousLinearMap.opNorm_nonneg _).trans hA2
  have hB1' := (norm_nonneg _).trans hB1
  have hB2' := (ContinuousLinearMap.opNorm_nonneg _).trans hB2
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [D2comp_apply]
  have t1 : ‖Dg (D2f v w)‖ ≤ A1 * B2 * ‖v‖ * ‖w‖ := by
    calc ‖Dg (D2f v w)‖ ≤ ‖Dg‖ * ‖D2f v w‖ := Dg.le_opNorm _
      _ ≤ A1 * (B2 * ‖v‖ * ‖w‖) := by
          refine mul_le_mul hA1 ?_ (norm_nonneg _) hA1'
          exact (D2f.le_opNorm₂ v w).trans (by gcongr)
      _ = _ := by ring
  have t2 : ‖D2g (Df v) (Df w)‖ ≤ A2 * B1 ^ 2 * ‖v‖ * ‖w‖ := by
    calc ‖D2g (Df v) (Df w)‖ ≤ ‖D2g‖ * ‖Df v‖ * ‖Df w‖ := D2g.le_opNorm₂ _ _
      _ ≤ A2 * (B1 * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df.le_opNorm v).trans (by gcongr)
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  calc ‖Dg (D2f v w) + D2g (Df v) (Df w)‖ ≤ ‖Dg (D2f v w)‖ + ‖D2g (Df v) (Df w)‖ := norm_add_le _ _
    _ ≤ _ := by have := add_le_add t1 t2; linarith

lemma D2comp_sub_le {Dg Dg' : F →L[ℝ] G} {D2g D2g' : F →L[ℝ] F →L[ℝ] G} {Df Df' : E →L[ℝ] F}
    {D2f D2f' : E →L[ℝ] E →L[ℝ] F} {A1 A2 B1 B2 : ℝ} (hA1 : ‖Dg'‖ ≤ A1) (hA2 : ‖D2g'‖ ≤ A2)
    (hB1 : ‖Df‖ ≤ B1) (hB1' : ‖Df'‖ ≤ B1) (hB2 : ‖D2f‖ ≤ B2) :
    ‖D2comp Dg D2g Df D2f - D2comp Dg' D2g' Df' D2f'‖ ≤
      ‖Dg - Dg'‖ * B2 + A1 * ‖D2f - D2f'‖ + ‖D2g - D2g'‖ * B1 ^ 2 + 2 * (A2 * B1 * ‖Df - Df'‖) := by
  have hA1' := (norm_nonneg _).trans hA1
  have hA2' := (ContinuousLinearMap.opNorm_nonneg _).trans hA2
  have hB1n := (norm_nonneg _).trans hB1
  have hB2' := (ContinuousLinearMap.opNorm_nonneg _).trans hB2
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, D2comp_apply, D2comp_apply]
  have e : Dg (D2f v w) + D2g (Df v) (Df w) - (Dg' (D2f' v w) + D2g' (Df' v) (Df' w)) =
      (Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w) +
      D2g' ((Df - Df') v) (Df w) + D2g' (Df' v) ((Df - Df') w) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
  rw [e]
  have nv := norm_nonneg v
  have nw := norm_nonneg w
  have t1 : ‖(Dg - Dg') (D2f v w)‖ ≤ ‖Dg - Dg'‖ * B2 * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖Dg - Dg'‖ * ‖D2f v w‖ := (Dg - Dg').le_opNorm _
      _ ≤ ‖Dg - Dg'‖ * (B2 * ‖v‖ * ‖w‖) := by
          gcongr; exact (D2f.le_opNorm₂ v w).trans (by gcongr)
      _ = _ := by ring
  have t2 : ‖Dg' ((D2f - D2f') v w)‖ ≤ A1 * ‖D2f - D2f'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖Dg'‖ * ‖(D2f - D2f') v w‖ := Dg'.le_opNorm _
      _ ≤ A1 * (‖D2f - D2f'‖ * ‖v‖ * ‖w‖) := mul_le_mul hA1 ((D2f - D2f').le_opNorm₂ v w)
          (norm_nonneg _) hA1'
      _ = _ := by ring
  have t3 : ‖(D2g - D2g') (Df v) (Df w)‖ ≤ ‖D2g - D2g'‖ * B1 ^ 2 * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g - D2g'‖ * ‖Df v‖ * ‖Df w‖ := (D2g - D2g').le_opNorm₂ _ _
      _ ≤ ‖D2g - D2g'‖ * (B1 * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df.le_opNorm v).trans (by gcongr)
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  have t4 : ‖D2g' ((Df - Df') v) (Df w)‖ ≤ A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g'‖ * ‖(Df - Df') v‖ * ‖Df w‖ := D2g'.le_opNorm₂ _ _
      _ ≤ A2 * (‖Df - Df'‖ * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df - Df').le_opNorm v
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  have t5 : ‖D2g' (Df' v) ((Df - Df') w)‖ ≤ A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g'‖ * ‖Df' v‖ * ‖(Df - Df') w‖ := D2g'.le_opNorm₂ _ _
      _ ≤ A2 * (B1 * ‖v‖) * (‖Df - Df'‖ * ‖w‖) := by
          gcongr
          · exact (Df'.le_opNorm v).trans (by gcongr)
          · exact (Df - Df').le_opNorm w
      _ = _ := by ring
  have n1 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w) +
      D2g' ((Df - Df') v) (Df w)) (D2g' (Df' v) ((Df - Df') w))
  have n2 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w))
      (D2g' ((Df - Df') v) (Df w))
  have n3 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w)) ((D2g - D2g') (Df v) (Df w))
  have n4 := norm_add_le ((Dg - Dg') (D2f v w)) (Dg' ((D2f - D2f') v w))
  have : (‖Dg - Dg'‖ * B2 + A1 * ‖D2f - D2f'‖ + ‖D2g - D2g'‖ * B1 ^ 2 + 2 * (A2 * B1 * ‖Df - Df'‖)) *
      ‖v‖ * ‖w‖ = ‖Dg - Dg'‖ * B2 * ‖v‖ * ‖w‖ + A1 * ‖D2f - D2f'‖ * ‖v‖ * ‖w‖ +
      ‖D2g - D2g'‖ * B1 ^ 2 * ‖v‖ * ‖w‖ + A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ +
      A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by ring
  rw [this]; linarith

/-- `ε ≤ R` converts a Lipschitz bound to a `μ`-Hölder one. -/
lemma lip_le_hol {t R μ : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    t ≤ R ^ (1 - μ) * t ^ μ := by
  rcases ht.eq_or_lt with h | h
  · subst h; exact mul_nonneg (rpow_nonneg htR _) (rpow_nonneg le_rfl _)
  have : t = t ^ (1 - μ) * t ^ μ := by rw [← rpow_add h]; simp
  calc t = t ^ (1 - μ) * t ^ μ := this
    _ ≤ R ^ (1 - μ) * t ^ μ := by gcongr

/-- Uniform `C^{2,μ}`-type bounds of `(f, Df, D2f)` on a set `T` with one constant `K`. -/
structure C2B (T : Set E) (μ K : ℝ) (f : E → F) (Df : E → E →L[ℝ] F)
    (D2f : E → E →L[ℝ] E →L[ℝ] F) : Prop where
  hK : 0 ≤ K
  lip : ∀ x ∈ T, ∀ y ∈ T, ‖f x - f y‖ ≤ K * ‖x - y‖
  b1 : ∀ x ∈ T, ‖Df x‖ ≤ K
  lip1 : ∀ x ∈ T, ∀ y ∈ T, ‖Df x - Df y‖ ≤ K * ‖x - y‖
  b2 : ∀ x ∈ T, ‖D2f x‖ ≤ K
  hol2 : ∀ x ∈ T, ∀ y ∈ T, ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ

/-- Composition of `C2B` data on a bounded set. -/
theorem C2B.comp {T : Set E} {T' : Set F} {μ K K' R : ℝ} {f : E → F} {Df : E → E →L[ℝ] F}
    {D2f : E → E →L[ℝ] E →L[ℝ] F} {g : F → G} {Dg : F → F →L[ℝ] G} {D2g : F → F →L[ℝ] F →L[ℝ] G}
    (hg : C2B T' μ K' g Dg D2g) (hf : C2B T μ K f Df D2f) (hmap : ∀ x ∈ T, f x ∈ T')
    (hR : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ R) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ K'', C2B T μ K'' (g ∘ f) (fun x => (Dg (f x)).comp (Df x))
      (fun x => D2comp (Dg (f x)) (D2g (f x)) (Df x) (D2f x)) := by
  have hK := hf.hK
  have hK' := hg.hK
  have hR0 : ∀ x ∈ T, ∀ y ∈ T, 0 ≤ R := fun x hx y hy => (norm_nonneg _).trans (hR x hx y hy)
  -- `R⁺ = max R 0` so that the constant is nonnegative even for empty `T`
  set Rp := max R 0 with hRp
  have hRp0 : 0 ≤ Rp := le_max_right _ _
  have hRR : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ Rp := fun x hx y hy => (hR x hx y hy).trans (le_max_left _ _)
  have hRμ : 0 ≤ Rp ^ (1 - μ) := rpow_nonneg hRp0 _
  have hconv : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ Rp ^ (1 - μ) * ‖x - y‖ ^ μ := fun x hx y hy =>
    lip_le_hol (norm_nonneg _) (hRR x hx y hy) hμ0.le hμ1
  have p1 : 0 ≤ K' * K := mul_nonneg hK' hK
  have p2 : 0 ≤ K' * K ^ 2 := mul_nonneg hK' (sq_nonneg K)
  set Ch := K' * K * K * Rp ^ (1 - μ) + K' * K + K' * K ^ μ * K ^ 2 + 2 * (K' * K * K * Rp ^ (1 - μ))
    with hCh
  have pCh : 0 ≤ Ch := by have := rpow_nonneg hK μ; positivity
  refine ⟨K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch, ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx y hy
    have : ‖g (f x) - g (f y)‖ ≤ K' * K * ‖x - y‖ := by
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ = _ := by ring
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro x hx
    have : ‖(Dg (f x)).comp (Df x)‖ ≤ K' * K :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hg.b1 _ (hmap x hx)) (hf.b1 x hx) (norm_nonneg _) hK')
    linarith
  · intro x hx y hy
    have e : (Dg (f x)).comp (Df x) - (Dg (f y)).comp (Df y) =
        (Dg (f x) - Dg (f y)).comp (Df x) + (Dg (f y)).comp (Df x - Df y) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
    rw [e]
    have a1 : ‖(Dg (f x) - Dg (f y)).comp (Df x)‖ ≤ K' * K * ‖x - y‖ * K := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ (hf.b1 x hx) (norm_nonneg _)
        (by positivity))
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip1 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ = _ := by ring
    have a2 : ‖(Dg (f y)).comp (Df x - Df y)‖ ≤ K' * (K * ‖x - y‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hg.b1 _ (hmap y hy)) (hf.lip1 x hx y hy) (norm_nonneg _) hK')
    have h3 : K' * K * ‖x - y‖ * K + K' * (K * ‖x - y‖) = (K' * K * K + K' * K) * ‖x - y‖ := by ring
    have h4 : (K' * K * K + K' * K) * ‖x - y‖ ≤ (K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    have := add_le_add a1 a2
    exact (norm_add_le _ _).trans (by linarith)
  · intro x hx
    have := D2comp_norm_le (hg.b1 _ (hmap x hx)) (hg.b2 _ (hmap x hx)) (hf.b1 x hx) (hf.b2 x hx)
    linarith
  · intro x hx y hy
    have hxy := hconv x hx y hy
    have hn := norm_nonneg (x - y)
    have hnμ : 0 ≤ ‖x - y‖ ^ μ := rpow_nonneg hn _
    refine (D2comp_sub_le (hg.b1 _ (hmap y hy)) (hg.b2 _ (hmap y hy)) (hf.b1 x hx) (hf.b1 y hy)
      (hf.b2 x hx)).trans ?_
    have c1 : ‖Dg (f x) - Dg (f y)‖ ≤ K' * K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) := by
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip1 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ ≤ K' * (K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ)) := by gcongr
        _ = _ := by ring
    have c2 : ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ := hf.hol2 x hx y hy
    have c3 : ‖D2g (f x) - D2g (f y)‖ ≤ K' * (K ^ μ * ‖x - y‖ ^ μ) := by
      calc _ ≤ K' * ‖f x - f y‖ ^ μ := hg.hol2 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) ^ μ := by
            gcongr; exact hf.lip x hx y hy
        _ = _ := by rw [mul_rpow hK hn]
    have c4 : ‖Df x - Df y‖ ≤ K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) :=
      (hf.lip1 x hx y hy).trans (by gcongr)
    have d1 := mul_le_mul_of_nonneg_right c1 hK
    have d2 := mul_le_mul_of_nonneg_left c2 hK'
    have d3 := mul_le_mul_of_nonneg_right c3 (sq_nonneg K)
    have d4 := mul_le_mul_of_nonneg_left c4 (mul_nonneg hK' hK)
    have e1 : K' * K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) * K + K' * (K * ‖x - y‖ ^ μ) +
        K' * (K ^ μ * ‖x - y‖ ^ μ) * K ^ 2 + 2 * (K' * K * (K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ))) =
        Ch * ‖x - y‖ ^ μ := by rw [hCh]; ring
    have h5 : Ch * ‖x - y‖ ^ μ ≤ (K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch) * ‖x - y‖ ^ μ :=
      mul_le_mul_of_nonneg_right (by linarith) hnμ
    nlinarith

end Comp2

section Glue

variable {n : ℕ}

lemma eu_expand (v : Eu n) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
  exact h.symm

end Glue

section IFT

variable {d : ℕ}

end IFT

section OpTrans

variable {d : ℕ}

lemma lin_expand (A : Eu d →L[ℝ] ℝ) (w : Eu d) : A w = ∑ k, w k * A (EuclideanSpace.single k (1 : ℝ)) := by
  conv_lhs => rw [eu_expand w]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma bil_expand (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (v w : Eu d) :
    B v w = ∑ k, ∑ l, v k * w l * B (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
  rw [lin_expand (B v) w]
  conv_lhs => rw [eu_expand v]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end OpTrans

section CutHelp

variable {d : ℕ}

/-- piecewise-linear cutoff. -/
noncomputable def cutR (c : Eu d) (ρ : ℝ) (z : Eu d) : ℝ := min 1 (max 0 (2 - 2 * ‖z - c‖ / ρ))

lemma cutR_nonneg (c : Eu d) (ρ : ℝ) (z : Eu d) : 0 ≤ cutR c ρ z :=
  le_min zero_le_one (le_max_left _ _)

lemma cutR_le_one (c : Eu d) (ρ : ℝ) (z : Eu d) : cutR c ρ z ≤ 1 := min_le_left _ _

lemma cutR_eq_one {c : Eu d} {ρ : ℝ} (hρ : 0 < ρ) {z : Eu d} (hz : ‖z - c‖ ≤ ρ / 2) :
    cutR c ρ z = 1 := by
  unfold cutR
  have h : 2 * ‖z - c‖ / ρ ≤ 1 := by rw [div_le_one hρ]; linarith
  exact min_eq_left (le_max_of_le_right (by linarith))

lemma cutR_eq_zero {c : Eu d} {ρ : ℝ} (hρ : 0 < ρ) {z : Eu d} (hz : ρ ≤ ‖z - c‖) :
    cutR c ρ z = 0 := by
  unfold cutR
  have h : 2 ≤ 2 * ‖z - c‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

lemma clamp_lip (a a' : ℝ) : |min 1 (max 0 a) - min 1 (max 0 a')| ≤ |a - a'| := by
  have key : ∀ a a' : ℝ, min 1 (max 0 a) - min 1 (max 0 a') ≤ |a - a'| := by
    intro a a'
    simp only [min_def, max_def]
    split_ifs <;> linarith [le_abs_self (a - a'), neg_le_abs (a - a'), abs_nonneg (a - a')]
  refine abs_sub_le_iff.mpr ⟨key a a', ?_⟩
  rw [abs_sub_comm]; exact key a' a

lemma cutR_lip (c : Eu d) {ρ : ℝ} (hρ : 0 < ρ) (z z' : Eu d) :
    |cutR c ρ z - cutR c ρ z'| ≤ (2 / ρ) * ‖z - z'‖ := by
  refine (clamp_lip _ _).trans ?_
  have h1 : (2 - 2 * ‖z - c‖ / ρ) - (2 - 2 * ‖z' - c‖ / ρ) = (2 / ρ) * (‖z' - c‖ - ‖z - c‖) := by
    field_simp; ring
  rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ρ)]
  gcongr
  have := abs_norm_sub_norm_le (z' - c) (z - c)
  rw [show z' - c - (z - c) = z' - z by abel, norm_sub_rev z' z] at this
  exact this

lemma cutR_hol (c : Eu d) {ρ μ : ℝ} (hρ : 0 < ρ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (z z' : Eu d) :
    |cutR c ρ z - cutR c ρ z'| ≤ (2 / ρ) ^ μ * ‖z - z'‖ ^ μ := by
  set a : ℝ := (2 / ρ) * ‖z - z'‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hl := cutR_lip c hρ z z'
  rw [← ha] at hl
  have h1 : |cutR c ρ z - cutR c ρ z'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [cutR_nonneg c ρ z, cutR_nonneg c ρ z', cutR_le_one c ρ z, cutR_le_one c ρ z']
  rw [← Real.mul_rpow (by positivity) (norm_nonneg _), ← ha]
  rcases le_or_gt a 1 with h | h
  · rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0] at hl ⊢; exact hl.trans (Real.rpow_nonneg le_rfl _)
    · refine hl.trans ?_
      have := Real.rpow_le_rpow_of_exponent_ge h0 h hμ1
      rwa [Real.rpow_one] at this
  · exact h1.trans (Real.one_le_rpow h.le hμ0)

/-- cutoff of data that is bounded and Hölder on `T ∩ closedBall c ρ`. -/
theorem cut_hb {T : Set (Eu d)} {c : Eu d} {ρ μ M H : ℝ} (hρ : 0 < ρ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) {f : Eu d → ℝ} (hM : ∀ z ∈ T, ‖z - c‖ ≤ ρ → |f z| ≤ M)
    (hH : ∀ z ∈ T, ‖z - c‖ ≤ ρ → ∀ z' ∈ T, ‖z' - c‖ ≤ ρ → |f z - f z'| ≤ H * ‖z - z'‖ ^ μ) :
    (∀ z ∈ T, |cutR c ρ z * f z| ≤ M) ∧
    ∀ z ∈ T, ∀ z' ∈ T, |cutR c ρ z * f z - cutR c ρ z' * f z'| ≤ (H + M * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by
  have hP : 0 ≤ (2 / ρ) ^ μ * ‖(0 : Eu d)‖ := by simp
  refine ⟨fun z hz => ?_, fun z hz z' hz' => ?_⟩
  · by_cases hzc : ‖z - c‖ ≤ ρ
    · rw [abs_mul, abs_of_nonneg (cutR_nonneg c ρ z)]
      calc cutR c ρ z * |f z| ≤ 1 * M := by
            gcongr
            · exact cutR_le_one c ρ z
            · exact hM z hz hzc
        _ = M := one_mul M
    · rw [cutR_eq_zero hρ (le_of_not_ge hzc), zero_mul, abs_zero]; exact hM0
  · have hch := cutR_hol c hρ hμ0 hμ1 z z'
    have ht : 0 ≤ ‖z - z'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have hq : 0 ≤ (2 / ρ) ^ μ := Real.rpow_nonneg (by positivity) _
    by_cases hzc : ‖z - c‖ ≤ ρ <;> by_cases hzc' : ‖z' - c‖ ≤ ρ
    · have e1 : cutR c ρ z * f z - cutR c ρ z' * f z' =
          cutR c ρ z * (f z - f z') + (cutR c ρ z - cutR c ρ z') * f z' := by ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (cutR_nonneg c ρ z)]
      have hf := hH z hz hzc z' hz' hzc'
      have hm := hM z' hz' hzc'
      calc cutR c ρ z * |f z - f z'| + |cutR c ρ z - cutR c ρ z'| * |f z'|
          ≤ 1 * (H * ‖z - z'‖ ^ μ) + ((2 / ρ) ^ μ * ‖z - z'‖ ^ μ) * M := by
            gcongr
            exact cutR_le_one c ρ z
        _ = (H + M * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by ring
    · have h0 : cutR c ρ z' = 0 := cutR_eq_zero hρ (le_of_not_ge hzc')
      have e1 : cutR c ρ z * f z - cutR c ρ z' * f z' = (cutR c ρ z - cutR c ρ z') * f z := by
        rw [h0]; ring
      rw [e1, abs_mul]
      calc |cutR c ρ z - cutR c ρ z'| * |f z| ≤ ((2 / ρ) ^ μ * ‖z - z'‖ ^ μ) * M := by
            gcongr; exact hM z hz hzc
        _ ≤ (H + M * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by nlinarith [mul_nonneg hH0 ht]
    · have h0 : cutR c ρ z = 0 := cutR_eq_zero hρ (le_of_not_ge hzc)
      have e1 : cutR c ρ z * f z - cutR c ρ z' * f z' = (cutR c ρ z - cutR c ρ z') * f z' := by
        rw [h0]; ring
      rw [e1, abs_mul]
      calc |cutR c ρ z - cutR c ρ z'| * |f z'| ≤ ((2 / ρ) ^ μ * ‖z - z'‖ ^ μ) * M := by
            gcongr; exact hM z' hz' hzc'
        _ ≤ (H + M * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by nlinarith [mul_nonneg hH0 ht]
    · rw [cutR_eq_zero hρ (le_of_not_ge hzc), cutR_eq_zero hρ (le_of_not_ge hzc')]
      simp only [zero_mul, sub_self, abs_zero]
      exact mul_nonneg (add_nonneg hH0 (mul_nonneg hM0 hq)) ht

end CutHelp

structure ObChart {d : ℕ} (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (r0 K : ℝ) (e b : Eu d)
    (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d) (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d) : Prop where
  hr0 : 0 < r0
  he : ‖e‖ = 1
  hb : inner ℝ b e = 0
  strict : ∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x
  hd2 : ∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x
  h0 : Θ x0 = 0
  hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (Eu d)
  side : ∀ x ∈ Metric.ball x0 r0, (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)
  obl : ∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)
  c2b : C2B (Metric.ball x0 r0 ∩ closure Ω) μ K Θ DΘ D2Θ

section ObChartS

end ObChartS

section VarDef

end VarDef

section Pull

variable {d : ℕ}

lemma ObChart.mem_closure_iff {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ}
    {e b : Eu d} {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d}
    {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d} (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {x : Eu d} (hx : x ∈ Metric.ball x0 r0) : x ∈ closure Ω ↔ 0 ≤ inner ℝ (Θ x) e := by
  constructor
  · intro h
    by_cases hΩ : x ∈ Ω
    · exact ((hch.side x hx).1.mp hΩ).le
    · have hf : x ∈ frontier Ω := ⟨h, fun hi => hΩ (interior_subset hi)⟩
      exact ((hch.side x hx).2.mp hf).ge
  · intro h
    rcases h.lt_or_eq with h | h
    · exact subset_closure ((hch.side x hx).1.mpr h)
    · exact frontier_subset_closure ((hch.side x hx).2.mpr h.symm)

lemma comp_sub_norm_le {A A' : Eu d →L[ℝ] ℝ} {B B' : Eu d →L[ℝ] Eu d} :
    ‖A.comp B - A'.comp B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have : A.comp B - A'.comp B' = (A - A').comp B + A'.comp (B - B') := by
    ext v; simp
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

lemma two_rpow_le {μ t : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ht : 0 ≤ t) : (2 * t) ^ μ ≤ 2 * t ^ μ := by
  rw [Real.mul_rpow (by norm_num) ht]
  gcongr
  calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
    _ = 2 := Real.rpow_one 2

/-- pull-back Hölder bounds of first and second derivatives of `v ∘ Θ` at two points. -/
theorem pull_hol {μ K D a1 a2 h1 h2 : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hK : 0 ≤ K)
    {x x' z z' : Eu d} {L L' : Eu d →L[ℝ] Eu d} {Q Q' : Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    {v1 v1' : Eu d →L[ℝ] ℝ} {v2 v2' : Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hz : ‖z - z'‖ ≤ 2 * ‖x - x'‖) (hD : ‖x - x'‖ ≤ D)
    (hL : ‖L‖ ≤ K) (hL' : ‖L'‖ ≤ K) (hQ : ‖Q‖ ≤ K) (hLL : ‖L - L'‖ ≤ K * ‖x - x'‖)
    (hQQ : ‖Q - Q'‖ ≤ K * ‖x - x'‖ ^ μ)
    (ha1 : ‖v1'‖ ≤ a1) (ha2 : ‖v2'‖ ≤ a2) (hv1 : ‖v1 - v1'‖ ≤ h1 * ‖z - z'‖ ^ μ)
    (hv2 : ‖v2 - v2'‖ ≤ h2 * ‖z - z'‖ ^ μ) (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2) :
    ‖v1.comp L - v1'.comp L'‖ ≤ (2 * h1 * K + a1 * K * D ^ (1 - μ)) * ‖x - x'‖ ^ μ ∧
    ‖D2comp v1 v2 L Q - D2comp v1' v2' L' Q'‖ ≤
      (2 * h1 * K + a1 * K + 2 * h2 * K ^ 2 + 2 * a2 * K ^ 2 * D ^ (1 - μ)) * ‖x - x'‖ ^ μ := by
  have ht := norm_nonneg (x - x')
  have hD0 : 0 ≤ D := ht.trans hD
  have ha1' : 0 ≤ a1 := (norm_nonneg _).trans ha1
  have ha2' : 0 ≤ a2 := (ContinuousLinearMap.opNorm_nonneg _).trans ha2
  have hzt : ‖z - z'‖ ^ μ ≤ 2 * ‖x - x'‖ ^ μ :=
    (Real.rpow_le_rpow (norm_nonneg _) hz hμ0).trans (two_rpow_le hμ0 hμ1 ht)
  have hlh : ‖x - x'‖ ≤ D ^ (1 - μ) * ‖x - x'‖ ^ μ := lip_le_hol ht hD hμ0 hμ1
  have htm : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg ht _
  have hDm : 0 ≤ D ^ (1 - μ) := Real.rpow_nonneg hD0 _
  constructor
  · refine comp_sub_norm_le.trans ?_
    calc ‖v1 - v1'‖ * ‖L‖ + ‖v1'‖ * ‖L - L'‖ ≤ (h1 * (2 * ‖x - x'‖ ^ μ)) * K +
          a1 * (K * (D ^ (1 - μ) * ‖x - x'‖ ^ μ)) := by
          gcongr
          · exact hv1.trans (by gcongr)
          · exact hLL.trans (by gcongr)
      _ = (2 * h1 * K + a1 * K * D ^ (1 - μ)) * ‖x - x'‖ ^ μ := by ring
  · refine (D2comp_sub_le ha1 ha2 hL hL' hQ).trans ?_
    calc ‖v1 - v1'‖ * K + a1 * ‖Q - Q'‖ + ‖v2 - v2'‖ * K ^ 2 + 2 * (a2 * K * ‖L - L'‖)
        ≤ (h1 * (2 * ‖x - x'‖ ^ μ)) * K + a1 * (K * ‖x - x'‖ ^ μ) +
          (h2 * (2 * ‖x - x'‖ ^ μ)) * K ^ 2 + 2 * (a2 * K * (K * (D ^ (1 - μ) * ‖x - x'‖ ^ μ))) := by
          gcongr
          · exact hv1.trans (by gcongr)
          · exact hv2.trans (by gcongr)
          · exact hLL.trans (by gcongr)
      _ = (2 * h1 * K + a1 * K + 2 * h2 * K ^ 2 + 2 * a2 * K ^ 2 * D ^ (1 - μ)) * ‖x - x'‖ ^ μ := by ring

end Pull

section NormA

variable {d : ℕ}

end NormA

section VarA

variable {d : ℕ}

/-- Variable-coefficient half-space solvability with principal part `½ Σ A0_ij ∂_ij`, `A0` positive definite. -/
def VarModelA (d : ℕ) (μ : ℝ) : Prop :=
  ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
  ∀ e b : Eu d, ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : Eu d → Fin d → Fin d → ℝ) (β : Eu d → Fin d → ℝ),
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : Eu d, 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x : Eu d, 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : Eu d, inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e → ∀ v w : Eu d,
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : Eu d,
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)

lemma sum4_comm (f : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm

end VarA

section PullA

variable {d : ℕ}

/-- second-order coefficient of the pulled-back operator relative to `½ A0`. -/
noncomputable def alTA (L : Eu d →L[ℝ] Eu d) (a : Matrix (Fin d) (Fin d) ℝ) (A0 : Matrix (Fin d) (Fin d) ℝ)
    (k l : Fin d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, a i j * L (EuclideanSpace.single i (1 : ℝ)) k * L (EuclideanSpace.single j (1 : ℝ)) l
    - A0 k l)

/-- first-order coefficient of the pulled-back operator. -/
noncomputable def betTA (D2 : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) (L : Eu d →L[ℝ] Eu d) (a : Matrix (Fin d) (Fin d) ℝ)
    (bb : Eu d) (k : Fin d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, a i j * D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k)
    + L bb k

lemma sum3_comm (f : Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm

theorem traceA (a A0 : Matrix (Fin d) (Fin d) ℝ) (Dv : Eu d →L[ℝ] ℝ) (D2v : Eu d →L[ℝ] Eu d →L[ℝ] ℝ)
    (L : Eu d →L[ℝ] Eu d) (D2 : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) :
    ∑ i, ∑ j, a i j * D2comp Dv D2v L D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      ∑ i, ∑ j, A0 i j * D2v (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) +
      2 * ∑ k, ∑ l, alTA L a A0 k l * D2v (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) +
      ∑ k, (∑ i, ∑ j, a i j * D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) *
        Dv (EuclideanSpace.single k (1 : ℝ)) := by
  simp only [D2comp_apply, mul_add, Finset.sum_add_distrib]
  have p1 : ∑ i, ∑ j, a i j * Dv (D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) =
      ∑ k, (∑ i, ∑ j, a i j * D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) *
        Dv (EuclideanSpace.single k (1 : ℝ)) := by
    simp_rw [lin_expand Dv (D2 _ _), Finset.mul_sum, Finset.sum_mul]
    rw [sum3_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have p2 : ∑ i, ∑ j, a i j * D2v (L (EuclideanSpace.single i (1 : ℝ))) (L (EuclideanSpace.single j (1 : ℝ))) =
      ∑ k, ∑ l, (∑ i, ∑ j, a i j * L (EuclideanSpace.single i (1 : ℝ)) k * L (EuclideanSpace.single j (1 : ℝ)) l) *
        D2v (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
    simp_rw [bil_expand D2v (L _) (L _), Finset.mul_sum, Finset.sum_mul]
    rw [sum4_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have p3 : ∑ i, ∑ j, A0 i j * D2v (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) +
      2 * ∑ k, ∑ l, alTA L a A0 k l * D2v (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) =
      ∑ k, ∑ l, (∑ i, ∑ j, a i j * L (EuclideanSpace.single i (1 : ℝ)) k * L (EuclideanSpace.single j (1 : ℝ)) l) *
        D2v (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by unfold alTA; ring
  rw [p1, p2, ← p3]
  ring

theorem pull_localA {Ω : Set (Eu d)} {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {c : Eu d → Eu d} {x0 : Eu d}
    {r0 K : ℝ} {e b : Eu d} {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d}
    {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d} (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {ρ : ℝ} (hρr : ρ ≤ r0)
    (hΘl : ∀ x ∈ Metric.ball x0 ρ, ∀ x' ∈ Metric.ball x0 ρ, ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖)
    {lam : ℝ} {g gt v : Eu d → ℝ} {v1 : Eu d → Eu d →L[ℝ] ℝ} {v2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    {α : Eu d → Fin d → Fin d → ℝ} {β : Eu d → Fin d → ℝ}
    {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d} {A0 : Matrix (Fin d) (Fin d) ℝ}
    (hcoef : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, (∀ k l, α (Θ x) k l = alTA (DΘ x) (a x) A0 k l) ∧
      (∀ k, β (Θ x) k = betTA (D2Θ x) (DΘ x) (a x) (bb x) k) ∧ gt (Θ x) = g x)
    (hvd : ∀ z : Eu d, 0 < inner ℝ z e → HasFDerivAt v (v1 z) z ∧ HasFDerivAt v1 (v2 z) z)
    (hve : ∀ z : Eu d, 0 ≤ inner ℝ z e →
      lam * v z - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * v2 z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        - ∑ i, ∑ j, α z i j * v2 z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        - ∑ i, β z i * v1 z (EuclideanSpace.single i 1) = gt z)
    (hvb : ∀ z : Eu d, inner ℝ z e = 0 → v1 z (b - e) = 0)
    {s0 s1 s2 t0 t1 t2 : ℝ}
    (hs : ∀ z : Eu d, 0 ≤ inner ℝ z e → |v z| ≤ s0 ∧ ‖v1 z‖ ≤ s1 ∧ ‖v2 z‖ ≤ s2)
    (ht : ∀ z z' : Eu d, 0 ≤ inner ℝ z e → 0 ≤ inner ℝ z' e →
      |v z - v z'| ≤ t0 * ‖z - z'‖ ^ μ ∧ ‖v1 z - v1 z'‖ ≤ t1 * ‖z - z'‖ ^ μ ∧
        ‖v2 z - v2 z'‖ ≤ t2 * ‖z - z'‖ ^ μ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    (∀ x ∈ Metric.ball x0 ρ ∩ Ω,
      HasFDerivAt (fun y => v (Θ y)) ((v1 (Θ x)).comp (DΘ x)) x ∧
      HasFDerivAt (fun y => (v1 (Θ y)).comp (DΘ y)) (D2comp (v1 (Θ x)) (v2 (Θ x)) (DΘ x) (D2Θ x)) x) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
      lam * v (Θ x) - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * D2comp (v1 (Θ x)) (v2 (Θ x)) (DΘ x) (D2Θ x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) - (v1 (Θ x)).comp (DΘ x) (bb x) = g x) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, (v1 (Θ x)).comp (DΘ x) (c x) = 0) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, |v (Θ x)| ≤ s0 ∧ ‖(v1 (Θ x)).comp (DΘ x)‖ ≤ s1 * K ∧
      ‖D2comp (v1 (Θ x)) (v2 (Θ x)) (DΘ x) (D2Θ x)‖ ≤ s1 * K + s2 * K ^ 2) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
      |v (Θ x) - v (Θ x')| ≤ 2 * t0 * ‖x - x'‖ ^ μ ∧
      ‖(v1 (Θ x)).comp (DΘ x) - (v1 (Θ x')).comp (DΘ x')‖ ≤
        (2 * t1 * K + s1 * K * (2 * ρ) ^ (1 - μ)) * ‖x - x'‖ ^ μ ∧
      ‖D2comp (v1 (Θ x)) (v2 (Θ x)) (DΘ x) (D2Θ x) - D2comp (v1 (Θ x')) (v2 (Θ x')) (DΘ x') (D2Θ x')‖ ≤
        (2 * t1 * K + s1 * K + 2 * t2 * K ^ 2 + 2 * s2 * K ^ 2 * (2 * ρ) ^ (1 - μ)) * ‖x - x'‖ ^ μ) := by
  have hsub : ∀ x ∈ Metric.ball x0 ρ, x ∈ Metric.ball x0 r0 := fun x hx => Metric.ball_subset_ball hρr hx
  have hhalf : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, 0 ≤ inner ℝ (Θ x) e :=
    fun x hx => (hch.mem_closure_iff (hsub x hx.1)).mp hx.2
  have hS : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, x ∈ Metric.ball x0 r0 ∩ closure Ω :=
    fun x hx => ⟨hsub x hx.1, hx.2⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · -- derivatives
    have hpos : 0 < inner ℝ (Θ x) e := ((hch.side x (hsub x hx.1)).1).mp hx.2
    have hΘ : HasFDerivAt Θ (DΘ x) x := (hch.strict x (hsub x hx.1)).hasFDerivAt
    obtain ⟨h1, h2⟩ := hvd (Θ x) hpos
    exact ⟨h1.comp x hΘ, hasFDerivAt_Dcomp hΘ (hch.hd2 x ⟨hsub x hx.1, hx.2⟩) h2⟩
  · -- equation
    obtain ⟨hα, hβ, hg⟩ := hcoef x hx
    have he := hve (Θ x) (hhalf x hx)
    simp only [hα, hβ, hg] at he
    rw [traceA (a x) A0]
    have hb1 : (v1 (Θ x)).comp (DΘ x) (bb x) =
        ∑ k, DΘ x (bb x) k * v1 (Θ x) (EuclideanSpace.single k (1 : ℝ)) := by
      rw [ContinuousLinearMap.comp_apply]; exact lin_expand _ _
    have hb2 : ∑ k, betTA (D2Θ x) (DΘ x) (a x) (bb x) k * v1 (Θ x) (EuclideanSpace.single k 1) =
        (1 / 2 : ℝ) * ∑ k, (∑ i, ∑ j, a x i j * D2Θ x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k) *
          v1 (Θ x) (EuclideanSpace.single k (1 : ℝ)) +
        ∑ k, DΘ x (bb x) k * v1 (Θ x) (EuclideanSpace.single k (1 : ℝ)) := by
      unfold betTA
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hb1]
    linarith
  · -- boundary condition
    have hx0 : inner ℝ (Θ x) e = 0 := ((hch.side x (hsub x hx.1)).2).mp hx.2
    obtain ⟨κ, -, hκ⟩ := hch.obl x ⟨hsub x hx.1, hx.2⟩
    rw [ContinuousLinearMap.comp_apply, hκ, map_smul, hvb (Θ x) hx0, smul_zero]
  · -- sup bounds
    obtain ⟨h0, h1, h2⟩ := hs (Θ x) (hhalf x hx)
    have hb1 := hch.c2b.b1 x (hS x hx)
    have hb2 := hch.c2b.b2 x (hS x hx)
    have hK := hch.c2b.hK
    have hs1 : 0 ≤ s1 := (norm_nonneg _).trans h1
    refine ⟨h0, (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul h1 hb1 (norm_nonneg _) hs1), ?_⟩
    refine (D2comp_norm_le h1 h2 hb1 hb2).trans ?_
    have hs2 : 0 ≤ s2 := (ContinuousLinearMap.opNorm_nonneg _).trans h2
    nlinarith
  · -- Hölder bounds
    have hK := hch.c2b.hK
    have hz := hΘl x hx.1 x' hx'.1
    have hD : ‖x - x'‖ ≤ 2 * ρ := by
      have h1 := hx.1; have h2 := hx'.1
      rw [Metric.mem_ball, dist_eq_norm] at h1 h2
      calc ‖x - x'‖ = ‖(x - x0) - (x' - x0)‖ := by congr 1; abel
        _ ≤ ‖x - x0‖ + ‖x' - x0‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    obtain ⟨g0, g1, g2⟩ := ht (Θ x) (Θ x') (hhalf x hx) (hhalf x' hx')
    obtain ⟨-, a1, a2⟩ := hs (Θ x') (hhalf x' hx')
    have hp := pull_hol hμ0 hμ1 hK hz hD (hch.c2b.b1 x (hS x hx)) (hch.c2b.b1 x' (hS x' hx'))
      (hch.c2b.b2 x (hS x hx)) (hch.c2b.lip1 x (hS x hx) x' (hS x' hx'))
      (hch.c2b.hol2 x (hS x hx) x' (hS x' hx')) a1 a2 g1 g2 ht1 ht2
    refine ⟨?_, hp.1, hp.2⟩
    have hzt : ‖Θ x - Θ x'‖ ^ μ ≤ 2 * ‖x - x'‖ ^ μ :=
      (Real.rpow_le_rpow (norm_nonneg _) hz hμ0).trans (two_rpow_le hμ0 hμ1 (norm_nonneg _))
    calc |v (Θ x) - v (Θ x')| ≤ t0 * ‖Θ x - Θ x'‖ ^ μ := g0
      _ ≤ t0 * (2 * ‖x - x'‖ ^ μ) := by gcongr
      _ = 2 * t0 * ‖x - x'‖ ^ μ := by ring

end PullA

section CoefA

variable {d : ℕ}

end CoefA

section LocalSolveA

variable {d : ℕ}

lemma key_leA {a Ñ Nb k P : ℝ} (ha : 0 ≤ a) (hÑ0 : 0 ≤ Ñ) (hÑ : Ñ ≤ Nb) (hk0 : 0 ≤ k) (hk : k ≤ P) :
    a * (Ñ * k) ≤ a * (Nb * P) :=
  mul_le_mul_of_nonneg_left (mul_le_mul hÑ hk hk0 (hÑ0.trans hÑ)) ha

set_option maxHeartbeats 2000000 in
theorem local_solverA {Ω : Set (Eu d)} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) {c : Eu d → Eu d} {x0 : Eu d}
    {r0 K : ℝ} {e b : Eu d} {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d}
    {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d} (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    (hinv : ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : Eu d → Eu d,
        (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
          ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
        (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
        (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : Eu d) (r1 / 4),
          ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
        (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : Eu d) (r1 / 4) → Λ (Θ x) = x))
    (hV : VarModelA d μ) {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d} {Ka : ℝ}
    (hab : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)
    (hcoef : ∀ (Z : Set (Eu d)) (Λ : Eu d → Eu d) (ρ : ℝ), (∀ z ∈ Z, Λ z ∈ Metric.ball x0 r0 ∩ closure Ω) →
      (0 : Eu d) ∈ Z → Λ 0 = x0 → (∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) → (∀ z ∈ Z, ‖z‖ ≤ ρ) →
      (∀ z ∈ Z, ∀ k l, |alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l| ≤
        Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l - alTA (DΘ (Λ z')) (a (Λ z')) (a x0) k l| ≤
        Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
      (∀ z ∈ Z, ∀ k, |betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k| ≤ 2 * Ka * K) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k -
        betTA (D2Θ (Λ z')) (DΘ (Λ z')) (a (Λ z')) (bb (Λ z')) k| ≤
        4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖))
    (hpd : (a x0).PosDef) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r0 ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - W1 x (bb x) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ) := by
  obtain ⟨r1, hr1, hr1r0, Λ, hbl, hΛ1, hΛl, hΛ3⟩ := hinv
  obtain ⟨δ, hδ, hVδ⟩ := hV (a x0) hpd e b hch.he hch.hb
  have hK := hch.c2b.hK
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx0S : x0 ∈ Metric.ball x0 r0 ∩ closure Ω :=
    ⟨Metric.mem_ball_self hch.hr0,
      (hch.mem_closure_iff (Metric.mem_ball_self hch.hr0)).mpr (by rw [hch.h0, inner_zero_left])⟩
  have hKa : 0 ≤ Ka := (norm_nonneg _).trans (hab x0 hx0S).2
  set f : ℝ → ℝ := fun ρ => (d : ℝ) ^ 2 * (Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) with hf
  have hfc : ContinuousAt f 0 := by
    rw [hf]
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.add
    · exact continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr hμ0.le))
    · exact continuousAt_const.mul continuousAt_id
  have hf0 : f 0 = 0 := by
    rw [hf]; simp [Real.zero_rpow hμ0.ne']
  have e1 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ρ := self_mem_nhdsWithin
  have e2 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ρ < r1 / 4 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < r1 / 4))
  have e3 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f ρ < δ :=
    nhdsWithin_le_nhds (hfc.eventually (Iio_mem_nhds (by rw [hf0]; exact hδ)))
  have hev : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ρ ∧ ρ < r1 / 4 ∧ f ρ < δ := e1.and (e2.and e3)
  obtain ⟨ρ, hρ, hρ1', hρA'⟩ := hev.exists
  have hρ1 : ρ ≤ r1 / 4 := hρ1'.le
  set Mα : ℝ := Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ with hMα
  have hρA : (d : ℝ) ^ 2 * Mα ≤ δ := hρA'.le
  -- the z-region Z and its facts
  set Z : Set (Eu d) := {z | 0 ≤ inner ℝ z e ∧ ‖z‖ ≤ ρ} with hZ
  have hZb : ∀ z ∈ Z, z ∈ Metric.closedBall (0 : Eu d) (r1 / 4) := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz.2.trans hρ1
  have hΛS : ∀ z ∈ Z, Λ z ∈ Metric.ball x0 r0 ∩ closure Ω := by
    intro z hz
    obtain ⟨hm, hΘΛ⟩ := hΛ1 z (hZb z hz)
    have hb : Λ z ∈ Metric.ball x0 r0 :=
      Metric.ball_subset_ball hr1r0 (Metric.closedBall_subset_ball (by linarith) hm)
    exact ⟨hb, (hch.mem_closure_iff hb).mpr (by rw [hΘΛ]; exact hz.1)⟩
  have h0Z : (0 : Eu d) ∈ Z := ⟨by rw [inner_zero_left], by rw [norm_zero]; exact hρ.le⟩
  have hΛ0 : Λ 0 = x0 := by
    have := hΛ3 x0 (Metric.mem_ball_self hr1) (by rw [hch.h0]; exact Metric.mem_closedBall_self (by linarith))
    rwa [hch.h0] at this
  have hΛlZ : ∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖ :=
    fun z hz z' hz' => hΛl z (hZb z hz) z' (hZb z' hz')
  have hρZ : ∀ z ∈ Z, ‖z‖ ≤ ρ := fun z hz => hz.2
  obtain ⟨cα, cα', cβ, cβ'⟩ :=
    hcoef Z Λ ρ hΛS h0Z hΛ0 hΛlZ hρZ
  have hzz : ∀ z ∈ Z, ∀ z' ∈ Z, ‖z - z'‖ ≤ 2 * ρ := fun z hz z' hz' => by
    have := norm_sub_le z z'; linarith [hz.2, hz'.2]
  have hmem : ∀ z : Eu d, 0 ≤ inner ℝ z e → ‖z - 0‖ ≤ ρ → z ∈ Z := fun z hz hzρ =>
    ⟨hz, by simpa using hzρ⟩
  set T : Set (Eu d) := {z | 0 ≤ inner ℝ z e} with hT
  set q : ℝ := (2 / ρ) ^ μ with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  set Hα : ℝ := Ka * K ^ 2 + 2 * Ka * K ^ 2 * (2 * ρ) ^ (1 - μ) with hHα
  have hMα0 : 0 ≤ Mα := by positivity
  have hHα0 : 0 ≤ Hα := by positivity
  have hcα : ∀ k l, (∀ z ∈ T, |cutR 0 ρ z * alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l| ≤ Mα) ∧
      ∀ z ∈ T, ∀ z' ∈ T, |cutR 0 ρ z * alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l -
        cutR 0 ρ z' * alTA (DΘ (Λ z')) (a (Λ z')) (a x0) k l| ≤ (Hα + Mα * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by
    intro k l
    refine cut_hb hρ hμ0.le hμ1.le hMα0 hHα0 (fun z hz hzρ => cα z (hmem z hz hzρ) k l)
      (fun z hz hzρ z' hz' hzρ' => ?_)
    have h1 := cα' z (hmem z hz hzρ) z' (hmem z' hz' hzρ') k l
    have h2 := lip_le_hol (norm_nonneg (z - z')) (hzz z (hmem z hz hzρ) z' (hmem z' hz' hzρ')) hμ0.le hμ1.le
    calc _ ≤ Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖ := h1
      _ ≤ Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ((2 * ρ) ^ (1 - μ) * ‖z - z'‖ ^ μ) := by gcongr
      _ = Hα * ‖z - z'‖ ^ μ := by rw [hHα]; ring
  set Mβ : ℝ := 2 * Ka * K with hMβ
  set Hβ : ℝ := 4 * Ka * K + 2 * Ka * K * (2 * ρ) ^ (1 - μ) with hHβ
  have hMβ0 : 0 ≤ Mβ := by positivity
  have hHβ0 : 0 ≤ Hβ := by positivity
  have hcβ : ∀ k, (∀ z ∈ T, |cutR 0 ρ z * betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k| ≤ Mβ) ∧
      ∀ z ∈ T, ∀ z' ∈ T, |cutR 0 ρ z * betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k -
        cutR 0 ρ z' * betTA (D2Θ (Λ z')) (DΘ (Λ z')) (a (Λ z')) (bb (Λ z')) k| ≤
        (Hβ + Mβ * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by
    intro k
    refine cut_hb hρ hμ0.le hμ1.le hMβ0 hHβ0 (fun z hz hzρ => cβ z (hmem z hz hzρ) k)
      (fun z hz hzρ z' hz' hzρ' => ?_)
    have h1 := cβ' z (hmem z hz hzρ) z' (hmem z' hz' hzρ') k
    have h2 := lip_le_hol (norm_nonneg (z - z')) (hzz z (hmem z hz hzρ) z' (hmem z' hz' hzρ')) hμ0.le hμ1.le
    calc _ ≤ 4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖ := h1
      _ ≤ 4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ((2 * ρ) ^ (1 - μ) * ‖z - z'‖ ^ μ) := by gcongr
      _ = Hβ * ‖z - z'‖ ^ μ := by rw [hHβ]; ring
  set Kt : ℝ := (d : ℝ) ^ 2 * (Hα + Mα * q) + d * Mβ + d * (Hβ + Mβ * q) with hKt
  have hKt1 : 0 ≤ (d : ℝ) ^ 2 * (Hα + Mα * q) := by positivity
  have hKt2 : 0 ≤ (d : ℝ) * Mβ := by positivity
  have hKt3 : 0 ≤ (d : ℝ) * (Hβ + Mβ * q) := by positivity
  have hKt0 : 0 ≤ Kt := by positivity
  obtain ⟨lam0, Cv, hlam0, hCv, hsol⟩ := hVδ Kt hKt0
  have hP0 : 0 ≤ (2 * (ρ / 4)) ^ (1 - μ) := Real.rpow_nonneg (by positivity) _
  set Dp : ℝ := (2 * (ρ / 4)) ^ (1 - μ) with hDp
  set P : ℝ := 2 + 3 * K + K * Dp + 3 * K ^ 2 + 2 * K ^ 2 * Dp with hP
  have hPK : 0 ≤ K * Dp := mul_nonneg hK hP0
  have hPK2 : 0 ≤ K ^ 2 * Dp := mul_nonneg (by positivity) hP0
  refine ⟨ρ / 4, by positivity, by linarith, lam0, Cv * (2 + q) * P, hlam0, by positivity,
    fun lam hlam g M H hM0 hH0 hgM hgH => ?_⟩
  have hlam1 : 1 ≤ lam := hlam0.trans hlam
  have hlpos : 0 < lam := by linarith
  have hsum2 : ∀ (f : Fin d → Fin d → ℝ) (m : ℝ), (∀ i j, f i j ≤ m) → ∑ i, ∑ j, f i j ≤ (d : ℝ) ^ 2 * m := by
    intro f m hf
    calc ∑ i, ∑ j, f i j ≤ ∑ _i : Fin d, ∑ _j : Fin d, m :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf i j
      _ = (d : ℝ) ^ 2 * m := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hsum1 : ∀ (f : Fin d → ℝ) (m : ℝ), (∀ i, f i ≤ m) → ∑ i, f i ≤ (d : ℝ) * m := by
    intro f m hf
    calc ∑ i, f i ≤ ∑ _i : Fin d, m := Finset.sum_le_sum fun i _ => hf i
      _ = (d : ℝ) * m := by simp [Finset.sum_const, Finset.card_univ]
  have tm0 : ∀ z z' : Eu d, 0 ≤ ‖z - z'‖ ^ μ := fun z z' => Real.rpow_nonneg (norm_nonneg _) _
  have hA1 : ∀ x : Eu d, 0 ≤ inner ℝ x e →
      ∑ i, ∑ j, |cutR 0 ρ x * alTA (DΘ (Λ x)) (a (Λ x)) (a x0) i j| ≤ δ := fun x hx =>
    (hsum2 _ Mα fun i j => (hcα i j).1 x hx).trans hρA
  have hA2 : ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |cutR 0 ρ x * alTA (DΘ (Λ x)) (a (Λ x)) (a x0) i j -
        cutR 0 ρ x' * alTA (DΘ (Λ x')) (a (Λ x')) (a x0) i j| ≤ Kt * ‖x - x'‖ ^ μ := by
    intro x x' hx hx'
    refine (hsum2 _ _ fun i j => (hcα i j).2 x hx x' hx').trans ?_
    have h1 : (d : ℝ) ^ 2 * (Hα + Mα * q) ≤ Kt := by rw [hKt]; linarith
    calc (d : ℝ) ^ 2 * ((Hα + Mα * (2 / ρ) ^ μ) * ‖x - x'‖ ^ μ) =
        ((d : ℝ) ^ 2 * (Hα + Mα * q)) * ‖x - x'‖ ^ μ := by rw [hq]; ring
      _ ≤ Kt * ‖x - x'‖ ^ μ := by gcongr
  have hB1 : ∀ x : Eu d, 0 ≤ inner ℝ x e →
      ∑ i, |cutR 0 ρ x * betTA (D2Θ (Λ x)) (DΘ (Λ x)) (a (Λ x)) (bb (Λ x)) i| ≤ Kt := by
    intro x hx
    refine (hsum1 _ _ fun i => (hcβ i).1 x hx).trans ?_
    rw [hKt]; linarith
  have hB2 : ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |cutR 0 ρ x * betTA (D2Θ (Λ x)) (DΘ (Λ x)) (a (Λ x)) (bb (Λ x)) i -
        cutR 0 ρ x' * betTA (D2Θ (Λ x')) (DΘ (Λ x')) (a (Λ x')) (bb (Λ x')) i| ≤ Kt * ‖x - x'‖ ^ μ := by
    intro x x' hx hx'
    refine (hsum1 _ _ fun i => (hcβ i).2 x hx x' hx').trans ?_
    have h1 : (d : ℝ) * (Hβ + Mβ * q) ≤ Kt := by rw [hKt]; linarith
    calc (d : ℝ) * ((Hβ + Mβ * (2 / ρ) ^ μ) * ‖x - x'‖ ^ μ) =
        ((d : ℝ) * (Hβ + Mβ * q)) * ‖x - x'‖ ^ μ := by rw [hq]; ring
      _ ≤ Kt * ‖x - x'‖ ^ μ := by gcongr
  -- data
  have hgc := cut_hb (T := T) (c := 0) hρ hμ0.le hμ1.le hM0 (by positivity : (0 : ℝ) ≤ 2 * H)
    (f := fun z => g (Λ z)) (fun z hz hzρ => hgM _ (hΛS z (hmem z hz hzρ)).2)
    (fun z hz hzρ z' hz' hzρ' => by
      have hz1 := hmem z hz hzρ
      have hz2 := hmem z' hz' hzρ'
      have h1 := hgH _ (hΛS z hz1).2 _ (hΛS z' hz2).2
      have h2 : ‖Λ z - Λ z'‖ ^ μ ≤ 2 * ‖z - z'‖ ^ μ :=
        (Real.rpow_le_rpow (norm_nonneg _) (hΛlZ z hz1 z' hz2) hμ0.le).trans
          (two_rpow_le hμ0.le hμ1.le (norm_nonneg _))
      calc |g (Λ z) - g (Λ z')| ≤ H * ‖Λ z - Λ z'‖ ^ μ := h1
        _ ≤ H * (2 * ‖z - z'‖ ^ μ) := by gcongr
        _ = 2 * H * ‖z - z'‖ ^ μ := by ring)
  obtain ⟨v, v1, v2, hvd, hve, hvb, hvs, hvt⟩ :=
    hsol lam hlam (fun z k l => cutR 0 ρ z * alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l)
      (fun z k => cutR 0 ρ z * betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k)
      hA1 hA2 hB1 hB2 (fun z => cutR 0 ρ z * g (Λ z)) M (2 * H + M * (2 / ρ) ^ μ) hM0 (by positivity)
      hgc.1 (fun y z hy hz => hgc.2 y hy z hz)
  -- scale facts
  have hl0 : 0 ≤ 1 / lam := by positivity
  have hl1 : 1 / lam ≤ 1 := (div_le_one hlpos).mpr hlam1
  have hlh0 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hl0 _
  have hlh1 : (1 / lam) ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hl0 hl1 (by norm_num)
  have hE0 : 0 ≤ (1 / lam) ^ (μ / 2) := Real.rpow_nonneg hl0 _
  have hE1 : (1 / lam) ^ (μ / 2) ≤ 1 := Real.rpow_le_one hl0 hl1 (by linarith)
  have hlm1 : 1 ≤ lam ^ (μ / 2) := Real.one_le_rpow hlam1 (by linarith)
  set Nt : ℝ := lam ^ (μ / 2) * M + (2 * H + M * (2 / ρ) ^ μ) with hNt
  set N : ℝ := lam ^ (μ / 2) * M + H with hN
  have hNt0 : 0 ≤ Nt := by rw [hNt]; have := mul_nonneg (zero_le_one.trans hlm1) hM0; positivity
  have hN0 : 0 ≤ N := by rw [hN]; have := mul_nonneg (zero_le_one.trans hlm1) hM0; positivity
  have hNtN : Nt ≤ (2 + q) * N := by
    rw [hNt, hN, ← hq]
    have h1 : M ≤ lam ^ (μ / 2) * M := le_mul_of_one_le_left hM0 hlm1
    linarith [mul_le_mul_of_nonneg_left h1 hq0, mul_nonneg hq0 hH0, mul_nonneg (zero_le_one.trans hlm1) hM0]
  -- v bounds in pull_local form
  have hs : ∀ z : Eu d, 0 ≤ inner ℝ z e →
      |v z| ≤ Cv * (1 / lam) * (1 / lam) ^ (μ / 2) * Nt ∧
      ‖v1 z‖ ≤ Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * Nt ∧
      ‖v2 z‖ ≤ Cv * (1 / lam) ^ (μ / 2) * Nt := by
    intro z hz
    refine ⟨(hvs z hz 0 0).1, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_,
      ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun w w' => ?_⟩
    · rw [Real.norm_eq_abs]; exact (hvs z hz w 0).2.1
    · rw [Real.norm_eq_abs]; exact (hvs z hz w w').2.2
  have ht : ∀ z z' : Eu d, 0 ≤ inner ℝ z e → 0 ≤ inner ℝ z' e →
      |v z - v z'| ≤ Cv * (1 / lam) * Nt * ‖z - z'‖ ^ μ ∧
      ‖v1 z - v1 z'‖ ≤ Cv * (1 / lam) ^ (1 / 2 : ℝ) * Nt * ‖z - z'‖ ^ μ ∧
      ‖v2 z - v2 z'‖ ≤ Cv * Nt * ‖z - z'‖ ^ μ := by
    intro z z' hz hz'
    refine ⟨(hvt z z' hz hz' 0 0).1,
      ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (tm0 z z')) fun w => ?_,
      ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg (by positivity) (tm0 z z')) fun w w' => ?_⟩
    · rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs]; exact (hvt z z' hz hz' w 0).2.1
    · simp only [ContinuousLinearMap.sub_apply]
      rw [Real.norm_eq_abs]; exact (hvt z z' hz hz' w w').2.2
  -- coefficients agree with the transformed ones near x0
  have hρ4 : ρ / 4 ≤ r1 := by linarith
  have hball : ∀ x ∈ Metric.ball x0 (ρ / 4), x ∈ Metric.ball x0 r1 := fun x hx =>
    Metric.ball_subset_ball hρ4 hx
  have hΘsmall : ∀ x ∈ Metric.ball x0 (ρ / 4), ‖Θ x‖ ≤ ρ / 2 := by
    intro x hx
    have h1 := (hbl x (hball x hx) x0 (Metric.mem_ball_self hr1)).2
    rw [hch.h0, sub_zero] at h1
    have h2 := hx; rw [Metric.mem_ball, dist_eq_norm] at h2
    linarith
  have hcoef : ∀ x ∈ Metric.ball x0 (ρ / 4) ∩ closure Ω,
      (∀ k l, (fun z k l => cutR 0 ρ z * alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l) (Θ x) k l =
        alTA (DΘ x) (a x) (a x0) k l) ∧
      (∀ k, (fun z k => cutR 0 ρ z * betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k) (Θ x) k =
        betTA (D2Θ x) (DΘ x) (a x) (bb x) k) ∧
      (fun z => cutR 0 ρ z * g (Λ z)) (Θ x) = g x := by
    intro x hx
    have hc1 : cutR 0 ρ (Θ x) = 1 := cutR_eq_one hρ (by rw [sub_zero]; exact hΘsmall x hx.1)
    have hΛx : Λ (Θ x) = x := hΛ3 x (hball x hx.1) (by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hΘsmall x hx.1])
    refine ⟨fun k l => ?_, fun k => ?_, ?_⟩ <;> simp only [hc1, one_mul, hΛx]
  have hΘl : ∀ x ∈ Metric.ball x0 (ρ / 4), ∀ x' ∈ Metric.ball x0 (ρ / 4), ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖ :=
    fun x hx x' hx' => (hbl x (hball x hx) x' (hball x' hx')).2
  have hpl := pull_localA hμ0.le hμ1.le hch (by linarith : ρ / 4 ≤ r0) hΘl hcoef hvd hve hvb hs ht
    (by positivity) (by positivity) (by positivity)
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpl
  have hlhE : (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) ≤ 1 := mul_le_one₀ hlh1 hE0 hE1
  refine ⟨fun y => v (Θ y), fun y => (v1 (Θ y)).comp (DΘ y),
    fun y => D2comp (v1 (Θ y)) (v2 (Θ y)) (DΘ y) (D2Θ y), p1, p2, p3, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨q0, q1, q2⟩ := p4 x hx
    refine ⟨q0.trans ?_, q1.trans ?_, q2.trans ?_⟩
    · calc Cv * (1 / lam) * (1 / lam) ^ (μ / 2) * Nt = (Cv * (1 / lam) * (1 / lam) ^ (μ / 2)) * (Nt * 1) := by ring
        _ ≤ (Cv * (1 / lam) * (1 / lam) ^ (μ / 2)) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN zero_le_one (by rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2])
        _ = _ := by ring
    · calc Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * Nt * K =
            (Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2)) * (Nt * K) := by ring
        _ ≤ (Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2)) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN hK (by rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2])
        _ = _ := by ring
    · have hk : (1 / lam) ^ (1 / 2 : ℝ) * K + K ^ 2 ≤ P := by
        have := mul_le_of_le_one_left hK hlh1
        rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2]
      calc Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * Nt * K + Cv * (1 / lam) ^ (μ / 2) * Nt * K ^ 2 =
            (Cv * (1 / lam) ^ (μ / 2)) * (Nt * ((1 / lam) ^ (1 / 2 : ℝ) * K + K ^ 2)) := by ring
        _ ≤ (Cv * (1 / lam) ^ (μ / 2)) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN (by positivity) hk
        _ = _ := by ring
  · obtain ⟨q0, q1, q2⟩ := p5 x hx x' hx'
    have tt := tm0 x x'
    refine ⟨q0.trans ?_, q1.trans ?_, q2.trans ?_⟩
    · calc 2 * (Cv * (1 / lam) * Nt) * ‖x - x'‖ ^ μ = (Cv * (1 / lam) * ‖x - x'‖ ^ μ) * (Nt * 2) := by ring
        _ ≤ (Cv * (1 / lam) * ‖x - x'‖ ^ μ) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN (by norm_num) (by rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2])
        _ = _ := by ring
    · have hk : 2 * K + (1 / lam) ^ (μ / 2) * K * Dp ≤ P := by
        have := mul_le_of_le_one_left hPK hE1
        rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2]
      calc (2 * (Cv * (1 / lam) ^ (1 / 2 : ℝ) * Nt) * K +
            Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * Nt * K * (2 * (ρ / 4)) ^ (1 - μ)) * ‖x - x'‖ ^ μ =
            (Cv * (1 / lam) ^ (1 / 2 : ℝ) * ‖x - x'‖ ^ μ) * (Nt * (2 * K + (1 / lam) ^ (μ / 2) * K * Dp)) := by
              rw [hDp]; ring
        _ ≤ (Cv * (1 / lam) ^ (1 / 2 : ℝ) * ‖x - x'‖ ^ μ) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN (by positivity) hk
        _ = _ := by ring
    · have hk : 2 * (1 / lam) ^ (1 / 2 : ℝ) * K + (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * K +
          2 * K ^ 2 + 2 * (1 / lam) ^ (μ / 2) * K ^ 2 * Dp ≤ P := by
        have h1 := mul_le_of_le_one_left hK hlh1
        have h2 := mul_le_of_le_one_left hK hlhE
        have h3 := mul_le_of_le_one_left hPK2 hE1
        rw [hP]; linarith [sq_nonneg K, hK, hPK, hPK2]
      calc (2 * (Cv * (1 / lam) ^ (1 / 2 : ℝ) * Nt) * K + Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * Nt * K +
            2 * (Cv * Nt) * K ^ 2 + 2 * (Cv * (1 / lam) ^ (μ / 2) * Nt) * K ^ 2 * (2 * (ρ / 4)) ^ (1 - μ)) * ‖x - x'‖ ^ μ =
            (Cv * ‖x - x'‖ ^ μ) * (Nt * (2 * (1 / lam) ^ (1 / 2 : ℝ) * K + (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * K +
              2 * K ^ 2 + 2 * (1 / lam) ^ (μ / 2) * K ^ 2 * Dp)) := by rw [hDp]; ring
        _ ≤ (Cv * ‖x - x'‖ ^ μ) * (((2 + q) * N) * P) :=
            key_leA (by positivity) hNt0 hNtN (by positivity) hk
        _ = _ := by ring

end LocalSolveA

end ObliqueLib

theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hV : ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
  ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖))
    (x0 : EuclideanSpace ℝ (Fin d)) (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d)) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : 0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
        (∀ x ∈ Metric.ball x0 r0,
          (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
        0 ≤ K ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (hinv : ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
          ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4),
          ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
        (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4) → Λ (Θ x) = x))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Ka : ℝ)
    (hab : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)
    (hcoef : ∀ (Z : Set (EuclideanSpace ℝ (Fin d))) (Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ρ : ℝ), (∀ z ∈ Z, Λ z ∈ Metric.ball x0 r0 ∩ closure Ω) →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ Z → Λ 0 = x0 → (∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) → (∀ z ∈ Z, ‖z‖ ≤ ρ) →
      (∀ z ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
        Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l) - (1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (DΘ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z')) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
        Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
      (∀ z ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k)| ≤ 2 * Ka * K) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k) -
        ((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (D2Θ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z')) (bb (Λ z')) k)| ≤
        4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖))
    (hpd : (a x0).PosDef) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r0 ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - W1 x (bb x) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ := hchart
  exact ObliqueLib.local_solverA hμ0 hμ1 ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩ hinv hV hab hah
    hcoef hpd
