-- Prove2me | solution 1 for EthierKurtz.oblique_local_pieces_from_boundary_solvers
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T23:19:59.952123+00:00
-- url     : https://prove2.me/submissions/112c94ef-b66c-49b5-b6e6-61fee6f814c3

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph

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

lemma C2B.mono {T : Set E} {μ K K' : ℝ} {f : E → F} {Df : E → E →L[ℝ] F}
    {D2f : E → E →L[ℝ] E →L[ℝ] F} (h : C2B T μ K f Df D2f) (hKK : K ≤ K') : C2B T μ K' f Df D2f where
  hK := h.hK.trans hKK
  lip x hx y hy := (h.lip x hx y hy).trans (by gcongr)
  b1 x hx := (h.b1 x hx).trans hKK
  lip1 x hx y hy := (h.lip1 x hx y hy).trans (by gcongr)
  b2 x hx := (h.b2 x hx).trans hKK
  hol2 x hx y hy := (h.hol2 x hx y hy).trans (by gcongr)

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

end Glue

section IFT

variable {d : ℕ}

/-- the identity as a nonlinear right inverse of `id`, with `nnnorm = 1`. -/
def idNRI : (ContinuousLinearMap.id ℝ (Eu d)).NonlinearRightInverse where
  toFun := id
  nnnorm := 1
  bound' := fun y => by simp
  right_inv' := fun y => by simp

lemma chart_local_inverse {Θ : Eu d → Eu d} {x0 : Eu d}
    (hΘ : HasStrictFDerivAt Θ (ContinuousLinearMap.id ℝ (Eu d)) x0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖) ∧
      (∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∃ x ∈ Metric.closedBall x0 (r / 2), Θ x = z := by
  obtain ⟨s, hs, hap⟩ := hΘ.approximates_deriv_on_nhds (c := (1 / 2 : NNReal)) (Or.inr (by norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  have key : ∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r,
      ‖Θ x - Θ x' - (x - x')‖ ≤ (1 / 2) * ‖x - x'‖ := by
    intro x hx x' hx'
    have := hap x (hball hx) x' (hball hx')
    simpa using this
  refine ⟨r, hr, fun x hx x' hx' => ?_, fun x hx x' hx' => ?_, ?_⟩
  · have h1 := key x hx x' hx'
    have h2 := norm_sub_norm_le (x - x') (Θ x - Θ x')
    rw [norm_sub_rev (x - x') (Θ x - Θ x')] at h2
    linarith
  · have h1 := key x hx x' hx'
    have h2 := norm_sub_norm_le (Θ x - Θ x') (x - x')
    have h3 : 0 ≤ ‖x - x'‖ := norm_nonneg _
    linarith
  · intro z hz
    have hsub : Metric.closedBall x0 (r / 2) ⊆ s :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hsurj := hap.surjOn_closedBall_of_nonlinearRightInverse idNRI (by positivity) hsub
    have hrad : (((idNRI : (ContinuousLinearMap.id ℝ (Eu d)).NonlinearRightInverse).nnnorm : ℝ)⁻¹ -
        ((1 / 2 : NNReal) : ℝ)) * (r / 2) = r / 4 := by
      simp [idNRI]; ring
    rw [hrad] at hsurj
    obtain ⟨x, hx, hxz⟩ := hsurj hz
    exact ⟨x, hx, hxz⟩

end IFT

section OpTrans

variable {d : ℕ}

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

/-- an inverse function from the `chart_local_inverse` output. -/
theorem chart_inverse_fn {Θ : Eu d → Eu d} {x0 : Eu d} {r : ℝ} (hr : 0 < r)
    (hlo : ∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖)
    (hsurj : ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∃ x ∈ Metric.closedBall x0 (r / 2), Θ x = z) :
    ∃ Λ : Eu d → Eu d,
      (∀ z ∈ Metric.closedBall (Θ x0) (r / 4), Λ z ∈ Metric.closedBall x0 (r / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∀ z' ∈ Metric.closedBall (Θ x0) (r / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r, Θ x ∈ Metric.closedBall (Θ x0) (r / 4) → Λ (Θ x) = x) := by
  classical
  let Λ : Eu d → Eu d := fun z =>
    if h : z ∈ Metric.closedBall (Θ x0) (r / 4) then (hsurj z h).choose else x0
  have hΛ : ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), Λ z ∈ Metric.closedBall x0 (r / 2) ∧ Θ (Λ z) = z := by
    intro z hz
    simp only [Λ, dif_pos hz]
    exact (hsurj z hz).choose_spec
  have hin : ∀ y ∈ Metric.closedBall x0 (r / 2), y ∈ Metric.ball x0 r :=
    fun y hy => Metric.closedBall_subset_ball (by linarith) hy
  refine ⟨Λ, hΛ, fun z hz z' hz' => ?_, fun x hx hΘx => ?_⟩
  · have := hlo _ (hin _ (hΛ z hz).1) _ (hin _ (hΛ z' hz').1)
    rwa [(hΛ z hz).2, (hΛ z' hz').2] at this
  · have := hlo _ (hin _ (hΛ _ hΘx).1) _ hx
    rw [(hΛ _ hΘx).2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

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

/-- Variable-coefficient half-space solvability with Schauder bounds. -/
def VarModel (d : ℕ) (μ : ℝ) : Prop :=
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
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
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

end VarDef

section Pull

variable {d : ℕ}

theorem chart_inv_small {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) :
    ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : Eu d → Eu d,
      (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
        ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : Eu d) (r1 / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : Eu d) (r1 / 4) → Λ (Θ x) = x) := by
  have hs : HasStrictFDerivAt Θ (ContinuousLinearMap.id ℝ (Eu d)) x0 := by
    have := hch.strict x0 (Metric.mem_ball_self hch.hr0); rwa [hch.hD0] at this
  obtain ⟨r, hr, hlo, hup, hsurj⟩ := chart_local_inverse hs
  have hr1 : 0 < min r r0 := lt_min hr hch.hr0
  have hmr : min r r0 ≤ r := min_le_left _ _
  have hsub : Metric.ball x0 (min r r0) ⊆ Metric.ball x0 r := Metric.ball_subset_ball hmr
  have hsurj1 : ∀ z ∈ Metric.closedBall (Θ x0) (min r r0 / 4),
      ∃ x ∈ Metric.closedBall x0 (min r r0 / 2), Θ x = z := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (Θ x0) (r / 4) :=
      Metric.closedBall_subset_closedBall (by linarith) hz
    obtain ⟨x, hx, rfl⟩ := hsurj z hz'
    refine ⟨x, ?_, rfl⟩
    have hxb : x ∈ Metric.ball x0 r := Metric.closedBall_subset_ball (by linarith) hx
    have := hlo x hxb x0 (Metric.mem_ball_self hr)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    linarith
  obtain ⟨Λ, h1, h2, h3⟩ :=
    chart_inverse_fn hr1 (fun x hx x' hx' => hlo x (hsub hx) x' (hsub hx')) hsurj1
  rw [hch.h0] at h1 h2 h3
  exact ⟨min r r0, hr1, min_le_right _ _, Λ,
    fun x hx x' hx' => ⟨hlo x (hsub hx) x' (hsub hx'), hup x (hsub hx) x' (hsub hx')⟩, h1, h2, h3⟩

end Pull

section PullLocal

variable {d : ℕ}

end PullLocal

section Interior

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem interior_solver {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : Eu d → Eu d) {x0 : Eu d} {R : ℝ} (hR : 0 < R) (hball : Metric.ball x0 R ⊆ Ω) (hd : 0 < d)
    (hV : VarModel d μ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ) := by
  set e : Eu d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by rw [he_def]; simp
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  obtain ⟨δ, hδ, hVδ⟩ := hV e 0 he (inner_zero_left _)
  obtain ⟨lam0, Cv, hlam0, hCv, hsol⟩ := hVδ 0 le_rfl
  set a : Eu d := x0 - R • e with ha
  set q : ℝ := (2 / R) ^ μ with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hcl : ∀ x ∈ Metric.closedBall x0 R, x ∈ closure Ω := by
    intro x hx
    rw [← closure_ball x0 hR.ne'] at hx
    exact closure_mono hball hx
  -- z-space facts
  have hza : ∀ z : Eu d, z + a - x0 = z - R • e := fun z => by rw [ha]; abel
  refine ⟨R / 2, by positivity, by linarith, lam0, Cv * (2 + q), hlam0, by positivity,
    fun lam hlam g M H hM0 hH0 hgM hgH => ?_⟩
  have hgc := cut_hb (T := {z : Eu d | 0 ≤ inner ℝ z e}) (c := R • e) hR hμ0.le hμ1.le hM0 hH0
    (f := fun z => g (z + a))
    (fun z _ hzρ => hgM _ (hcl _ (by rw [Metric.mem_closedBall, dist_eq_norm, hza]; exact hzρ)))
    (fun z _ hzρ z' _ hzρ' => by
      have h1 := hgH _ (hcl _ (by rw [Metric.mem_closedBall, dist_eq_norm, hza]; exact hzρ))
        _ (hcl _ (by rw [Metric.mem_closedBall, dist_eq_norm, hza]; exact hzρ'))
      rwa [add_sub_add_right_eq_sub] at h1)
  obtain ⟨v, v1, v2, hvd, hve, hvb, hvs, hvt⟩ :=
    hsol lam hlam (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => by simp [hδ.le])
      (fun _ _ _ _ => by simp)
      (fun _ _ => by simp) (fun _ _ _ _ => by simp)
      (fun z => cutR (R • e) R z * g (z + a)) M (H + M * (2 / R) ^ μ) hM0 (by positivity)
      hgc.1 (fun y z hy hz => hgc.2 y hy z hz)
  have hlam1 : 1 ≤ lam := hlam0.trans hlam
  have hlpos : 0 < lam := by linarith
  have hl0 : 0 ≤ 1 / lam := by positivity
  have hlm1 : 1 ≤ lam ^ (μ / 2) := Real.one_le_rpow hlam1 (by linarith)
  set Nt : ℝ := lam ^ (μ / 2) * M + (H + M * (2 / R) ^ μ) with hNt
  set N : ℝ := lam ^ (μ / 2) * M + H with hN
  have hlM : 0 ≤ lam ^ (μ / 2) * M := mul_nonneg (zero_le_one.trans hlm1) hM0
  have hNt0 : 0 ≤ Nt := by rw [hNt]; positivity
  have hNtN : Nt ≤ (2 + q) * N := by
    rw [hNt, hN, ← hq]
    have h1 : M ≤ lam ^ (μ / 2) * M := le_mul_of_one_le_left hM0 hlm1
    linarith [mul_le_mul_of_nonneg_left h1 hq0, mul_nonneg hq0 hH0]
  -- membership facts
  have hpos : ∀ x ∈ Metric.ball x0 (R / 2), 0 < inner ℝ (x - a) e := by
    intro x hx
    have h1 : x - a = (x - x0) + R • e := by rw [ha]; abel
    rw [h1, inner_add_left, inner_smul_left, hee]
    have h2 := abs_real_inner_le_norm (x - x0) e
    rw [he, mul_one] at h2
    have h3 := hx; rw [Metric.mem_ball, dist_eq_norm] at h3
    simp only [conj_trivial]
    linarith [neg_abs_le (inner ℝ (x - x0) e)]
  have hcut : ∀ x ∈ Metric.ball x0 (R / 2), cutR (R • e) R (x - a) = 1 := by
    intro x hx
    refine cutR_eq_one hR ?_
    have h1 : x - a - R • e = x - x0 := by rw [ha]; abel
    rw [h1]; have h3 := hx; rw [Metric.mem_ball, dist_eq_norm] at h3; linarith
  have hsubΩ : ∀ x ∈ Metric.ball x0 (R / 2), x ∈ Ω := fun x hx =>
    hball (Metric.ball_subset_ball (by linarith) hx)
  have tm0 : ∀ x x' : Eu d, 0 ≤ ‖x - x'‖ ^ μ := fun x x' => Real.rpow_nonneg (norm_nonneg _) _
  have hdiff : ∀ x x' : Eu d, x - a - (x' - a) = x - x' := fun x x' => sub_sub_sub_cancel_right x x' a
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
  have hfin : ∀ pre : ℝ, 0 ≤ pre → pre * Nt ≤ pre * ((2 + q) * N) :=
    fun pre hpre => mul_le_mul_of_nonneg_left hNtN hpre
  refine ⟨fun y => v (y - a), fun y => v1 (y - a), fun y => v2 (y - a), fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨h1, h2⟩ := hvd (x - a) (hpos x hx.1)
    have hs : HasFDerivAt (fun y : Eu d => y - a) (ContinuousLinearMap.id ℝ (Eu d)) x :=
      (hasFDerivAt_id x).sub_const a
    have k1 := h1.comp x hs
    have k2 := h2.comp x hs
    rw [ContinuousLinearMap.comp_id] at k1 k2
    exact ⟨k1, k2⟩
  · have h := hve (x - a) (hpos x hx.1).le
    simp only [zero_mul, Finset.sum_const_zero, sub_zero, hcut x hx.1, one_mul, sub_add_cancel] at h
    exact h
  · exfalso
    have h1 : x ∈ Ω := hsubΩ x hx.1
    exact hx.2.2 (by rw [hΩ.interior_eq]; exact h1)
  · obtain ⟨s0, s1, s2⟩ := hs (x - a) (hpos x hx.1).le
    refine ⟨s0.trans ?_, s1.trans ?_, s2.trans ?_⟩
    · calc _ = (Cv * (1 / lam) * (1 / lam) ^ (μ / 2)) * Nt := by ring
        _ ≤ (Cv * (1 / lam) * (1 / lam) ^ (μ / 2)) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring
    · calc _ = (Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2)) * Nt := by ring
        _ ≤ (Cv * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2)) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring
    · calc _ = (Cv * (1 / lam) ^ (μ / 2)) * Nt := by ring
        _ ≤ (Cv * (1 / lam) ^ (μ / 2)) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring
  · obtain ⟨t0, t1, t2⟩ := ht (x - a) (x' - a) (hpos x hx.1).le (hpos x' hx'.1).le
    rw [hdiff] at t0 t1 t2
    have t := tm0 x x'
    refine ⟨t0.trans ?_, t1.trans ?_, t2.trans ?_⟩
    · calc _ = (Cv * (1 / lam) * ‖x - x'‖ ^ μ) * Nt := by ring
        _ ≤ (Cv * (1 / lam) * ‖x - x'‖ ^ μ) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring
    · calc _ = (Cv * (1 / lam) ^ (1 / 2 : ℝ) * ‖x - x'‖ ^ μ) * Nt := by ring
        _ ≤ (Cv * (1 / lam) ^ (1 / 2 : ℝ) * ‖x - x'‖ ^ μ) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring
    · calc _ = (Cv * ‖x - x'‖ ^ μ) * Nt := by ring
        _ ≤ (Cv * ‖x - x'‖ ^ μ) * ((2 + q) * N) := hfin _ (by positivity)
        _ = _ := by ring

end Interior

section BumpS

variable {d : ℕ}

lemma cs_bdd_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Eu d → F}
    (hf : HasCompactSupport f) (h : ContDiff ℝ 1 f) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ K) ∧ (∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖) ∧
      ∀ x y, ‖f x - f y‖ ≤ 2 * K := by
  obtain ⟨B, hB⟩ := h.continuous.bounded_above_of_compact_support hf
  obtain ⟨L, hL⟩ := (h.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hf.fderiv (𝕜 := ℝ))
  have hlip : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => ((h.differentiable (by norm_num)) z).hasFDerivAt.hasFDerivWithinAt)
      (fun z _ => hL z) (Set.mem_univ y) (Set.mem_univ x)
  set K := max (max B 0) L
  have eB : B ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨K, le_max_of_le_left (le_max_right _ _), fun x => (hB x).trans eB, fun x y => ?_, fun x y => ?_⟩
  · exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith [(hB x).trans eB, (hB y).trans eB]

lemma bl_hol {B L μ t a : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ht : 0 ≤ t) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (ha1 : a ≤ 2 * B) (ha2 : a ≤ L * t) : a ≤ max (2 * B) L * t ^ μ := by
  rcases le_or_gt t 1 with h1 | h1
  · have : t ≤ t ^ μ := by
      rcases ht.eq_or_lt with h0 | h0
      · rw [← h0]; exact Real.rpow_nonneg le_rfl _
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ μ := Real.rpow_le_rpow_of_exponent_ge h0 h1 hμ1
    calc a ≤ L * t := ha2
      _ ≤ max (2 * B) L * t ^ μ := by
          gcongr
          · exact le_max_right _ _
  · have : 1 ≤ t ^ μ := Real.one_le_rpow h1.le hμ0
    calc a ≤ 2 * B := ha1
      _ = 2 * B * 1 := (mul_one _).symm
      _ ≤ max (2 * B) L * t ^ μ := by
          gcongr
          · exact le_max_left _ _

/-- `C^3` with compact support gives global `C^{2,μ}` bounds. -/
theorem cs_C2B {ψ : Eu d → ℝ} {ψ1 : Eu d → Eu d →L[ℝ] ℝ} {ψ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0) (hK2 : 0 ≤ K2)
    (hl0 : ∀ x y, ‖ψ x - ψ y‖ ≤ K0 * ‖x - y‖) (hb1 : ∀ x, ‖ψ1 x‖ ≤ K1)
    (hl1 : ∀ x y, ‖ψ1 x - ψ1 y‖ ≤ K1 * ‖x - y‖) (hb2 : ∀ x, ‖ψ2 x‖ ≤ K2)
    (hl2 : ∀ x y, ‖ψ2 x - ψ2 y‖ ≤ K2 * ‖x - y‖) (hd2 : ∀ x y, ‖ψ2 x - ψ2 y‖ ≤ 2 * K2) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    C2B (Set.univ : Set (Eu d)) μ (max (max K0 K1) (max (2 * K2) K2)) ψ ψ1 ψ2 := by
  set K := max (max K0 K1) (max (2 * K2) K2) with hK
  have e0 : K0 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have e1 : K1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have e2 : K2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have e3 : max (2 * K2) K2 ≤ K := le_max_right _ _
  exact
  { hK := hK0.trans e0
    lip := fun x _ y _ => (hl0 x y).trans (mul_le_mul_of_nonneg_right e0 (norm_nonneg _))
    b1 := fun x _ => (hb1 x).trans e1
    lip1 := fun x _ y _ => (hl1 x y).trans (mul_le_mul_of_nonneg_right e1 (norm_nonneg _))
    b2 := fun x _ => (hb2 x).trans e2
    hol2 := fun x _ y _ => by
      exact (bl_hol hμ0 hμ1 (norm_nonneg (x - y)) hK2 hK2 (hd2 x y) (hl2 x y)).trans
        (mul_le_mul_of_nonneg_right e3 (Real.rpow_nonneg (norm_nonneg _) _)) }

theorem cs_C2B' {ψ : Eu d → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) : ∃ K : ℝ, C2B (Set.univ : Set (Eu d)) μ K ψ (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ)) := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ ψ) := hψ.fderiv_right (m := 2) le_rfl
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ψ)) := h1.fderiv_right (m := 1) le_rfl
  have h0' : ContDiff ℝ 1 ψ := hψ.of_le (by norm_cast)
  have h1' : ContDiff ℝ 1 (fderiv ℝ ψ) := h1.of_le (by norm_cast)
  have hc1 : HasCompactSupport (fderiv ℝ ψ) := hc.fderiv (𝕜 := ℝ)
  have hc2 : HasCompactSupport (fderiv ℝ (fderiv ℝ ψ)) := hc1.fderiv (𝕜 := ℝ)
  have A0 := cs_bdd_lip (F := ℝ) hc h0'
  have A1 := cs_bdd_lip (F := Eu d →L[ℝ] ℝ) hc1 h1'
  have A2 := cs_bdd_lip (F := Eu d →L[ℝ] Eu d →L[ℝ] ℝ) hc2 h2
  obtain ⟨K0, hK0, _hb0, hl0, _hd0⟩ := A0
  obtain ⟨K1, _hK1, hb1, hl1, _hd1⟩ := A1
  obtain ⟨K2, hK2, hb2, hl2, hd2⟩ := A2
  have hC := cs_C2B (ψ := ψ) (ψ1 := fderiv ℝ ψ) (ψ2 := fderiv ℝ (fderiv ℝ ψ)) (μ := μ)
    hK0 hK2 hl0 hb1 hl1 hb2 hl2 hd2 hμ0 hμ1
  exact ⟨_, hC⟩

/-- the oblique projection `P z = z + ⟪e,z⟫ (b - e)` -/
noncomputable def obP (e b : Eu d) : Eu d →L[ℝ] Eu d :=
  ContinuousLinearMap.id ℝ (Eu d) + (innerSL ℝ e).smulRight (b - e)

lemma obP_apply (e b z : Eu d) : obP e b z = z + inner ℝ e z • (b - e) := by
  simp [obP]

/-- the quadratic form `q z = ‖P z‖² + ⟪e,z⟫²` -/
noncomputable def obQ (e b : Eu d) (z : Eu d) : ℝ := ‖obP e b z‖ ^ 2 + (inner ℝ e z) ^ 2

lemma obQ_bounds {e b : Eu d} (he : ‖e‖ = 1) (z : Eu d) :
    ‖z‖ ^ 2 ≤ (1 + ‖b - e‖ ^ 2) * obQ e b z ∧ obQ e b z ≤ 3 * (1 + ‖b - e‖ ^ 2) * ‖z‖ ^ 2 := by
  set c := ‖b - e‖ with hc
  set p := ‖obP e b z‖
  set l := inner ℝ e z with hl
  have hc0 : 0 ≤ c := norm_nonneg _
  have hp0 : 0 ≤ p := norm_nonneg _
  have hlz : |l| ≤ ‖z‖ := by
    have := abs_real_inner_le_norm e z
    rw [he, one_mul] at this; exact this
  have hz1 : ‖z‖ ≤ p + |l| * c := by
    have : z = obP e b z - l • (b - e) := by rw [obP_apply]; abel
    calc ‖z‖ = ‖obP e b z - l • (b - e)‖ := by rw [← this]
      _ ≤ p + ‖l • (b - e)‖ := norm_sub_le _ _
      _ = p + |l| * c := by rw [norm_smul, Real.norm_eq_abs]
  have hp1 : p ≤ ‖z‖ + |l| * c := by
    calc p = ‖z + l • (b - e)‖ := by show ‖obP e b z‖ = _; rw [obP_apply]
      _ ≤ ‖z‖ + ‖l • (b - e)‖ := norm_add_le _ _
      _ = ‖z‖ + |l| * c := by rw [norm_smul, Real.norm_eq_abs]
  have hl2 : l ^ 2 = |l| ^ 2 := (sq_abs l).symm
  have hz0 := norm_nonneg z
  have ha0 := abs_nonneg l
  unfold obQ
  constructor
  · have h1 : ‖z‖ ^ 2 ≤ (p + |l| * c) ^ 2 := by gcongr
    nlinarith [sq_nonneg (p * c - |l|)]
  · have h1 : p ^ 2 ≤ (‖z‖ + |l| * c) ^ 2 := by gcongr
    have h2 : |l| * c ≤ ‖z‖ * c := by gcongr
    have h3 : |l| ^ 2 ≤ ‖z‖ ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖z‖ - ‖z‖ * c), mul_nonneg hz0 hc0]

lemma obP_be {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) : obP e b (b - e) = 0 := by
  rw [obP_apply]
  have h1 : inner ℝ e (b - e) = -1 := by
    rw [inner_sub_right, real_inner_comm, hb, real_inner_self_eq_norm_sq, he]; norm_num
  rw [h1]; simp

lemma hasFDerivAt_obQ (e b z : Eu d) :
    HasFDerivAt (obQ e b) (2 • (innerSL ℝ (obP e b z)).comp (obP e b) +
      ((2 : ℕ) • (innerSL ℝ e z) ^ (2 - 1)) • innerSL ℝ e) z := by
  have h1 := (obP e b).hasFDerivAt (x := z) |>.norm_sq
  have h2 := ((innerSL ℝ e).hasFDerivAt (x := z)).pow 2
  exact h1.add h2

lemma obQ_contDiff (e b : Eu d) : ContDiff ℝ 3 (obQ e b) := by
  have h1 : ContDiff ℝ 3 (fun z => ‖obP e b z‖ ^ 2) := (obP e b).contDiff.norm_sq ℝ
  have h2 : ContDiff ℝ 3 (fun z => (innerSL ℝ e z) ^ 2) := ((innerSL ℝ e).contDiff).pow 2
  exact h1.add h2

/-- the bump -/
noncomputable def obBump (e b : Eu d) (a : ℝ) (z : Eu d) : ℝ := Real.smoothTransition (2 - obQ e b z / a)

theorem obBump_props {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {s : ℝ} (hs : 0 < s) :
    ∃ ψ : Eu d → ℝ, ContDiff ℝ 3 ψ ∧ HasCompactSupport ψ ∧ (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧
      (∃ τ : ℝ, 0 < τ ∧ ∀ z, ‖z‖ ≤ τ → ψ z = 1) ∧ (∀ z, s / 2 ≤ ‖z‖ → ψ z = 0) ∧
      (∀ z, s / 2 < ‖z‖ → fderiv ℝ ψ z = 0 ∧ fderiv ℝ (fderiv ℝ ψ) z = 0) ∧
      (∀ z, inner ℝ z e = 0 → fderiv ℝ ψ z (b - e) = 0) := by
  set Bq := 1 + ‖b - e‖ ^ 2 with hBq
  have hBq1 : 1 ≤ Bq := by have := sq_nonneg ‖b - e‖; linarith
  have hBq0 : 0 < Bq := by linarith
  set a := s ^ 2 / (8 * Bq) with ha
  have ha0 : 0 < a := by positivity
  set ψ := obBump e b a with hψ
  have hcd : ContDiff ℝ 3 ψ := by
    have hq := obQ_contDiff e b
    have hin : ContDiff ℝ 3 (fun z => 2 - obQ e b z / a) := contDiff_const.sub (hq.div_const a)
    exact (Real.smoothTransition.contDiff (n := 3)).comp hin
  have hzero : ∀ z, s / 2 ≤ ‖z‖ → ψ z = 0 := by
    intro z hz
    have hb1 := (obQ_bounds (b := b) he z).1
    have hs2 : (s / 2) ^ 2 ≤ ‖z‖ ^ 2 := by gcongr
    have : 2 * a ≤ obQ e b z := by
      have h3 : (s / 2) ^ 2 ≤ Bq * obQ e b z := hs2.trans hb1
      rw [ha]
      rw [show 2 * (s ^ 2 / (8 * Bq)) = (s / 2) ^ 2 / Bq by field_simp; ring]
      rw [div_le_iff₀ hBq0]; linarith
    show Real.smoothTransition _ = 0
    apply Real.smoothTransition.zero_of_nonpos
    rw [sub_nonpos, le_div_iff₀ ha0]; linarith
  have hopen : IsOpen {z : Eu d | s / 2 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hev : ∀ z, s / 2 < ‖z‖ → ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    intro z hz
    filter_upwards [hopen.mem_nhds hz] with w hw using hzero w (le_of_lt hw)
  refine ⟨ψ, hcd, ?_, fun z => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    ⟨s / (5 * Bq), by positivity, fun z hz => ?_⟩, hzero, fun z hz => ?_, fun z hz => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Eu d) (s / 2)) fun z hz => hzero z ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz; exact hz.le
  · show Real.smoothTransition _ = 1
    apply Real.smoothTransition.one_of_one_le
    have hb2 := (obQ_bounds (b := b) he z).2
    have hz2 : ‖z‖ ^ 2 ≤ (s / (5 * Bq)) ^ 2 := by gcongr
    have : obQ e b z ≤ a := by
      calc obQ e b z ≤ 3 * Bq * ‖z‖ ^ 2 := hb2
        _ ≤ 3 * Bq * (s / (5 * Bq)) ^ 2 := by gcongr
        _ ≤ a := by
            rw [ha, div_pow, mul_pow]
            rw [show 3 * Bq * (s ^ 2 / (5 ^ 2 * Bq ^ 2)) = 3 * s ^ 2 / (25 * Bq) by field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [sq_nonneg s]
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ ha0]; linarith
  · constructor
    · rw [(hev z hz).fderiv_eq]; simp
    · have : fderiv ℝ ψ =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        rw [(hev w hw).fderiv_eq]; simp
      rw [this.fderiv_eq]; simp
  · -- chain rule: ψ = h ∘ q with q' (b - e) = 0 on the plane
    have hh : DifferentiableAt ℝ (fun t : ℝ => Real.smoothTransition (2 - t / a)) (obQ e b z) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.comp _
        ((differentiableAt_const _).sub (differentiableAt_id.div_const a))
    have hcomp : HasFDerivAt ψ ((fderiv ℝ (fun t : ℝ => Real.smoothTransition (2 - t / a)) (obQ e b z)).comp
        (2 • (innerSL ℝ (obP e b z)).comp (obP e b) +
          ((2 : ℕ) • (innerSL ℝ e z) ^ (2 - 1)) • innerSL ℝ e)) z :=
      hh.hasFDerivAt.comp z (hasFDerivAt_obQ e b z)
    rw [hcomp.fderiv]
    have hP := obP_be he hb
    have hl : innerSL ℝ e z = 0 := by rw [innerSL_apply_apply, real_inner_comm]; exact hz
    simp [hP, hl]

end BumpS

section CutDefS

variable {d : ℕ}

structure CutData (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (ρ Z τ : ℝ) (χ : Eu d → ℝ)
    (χ1 : Eu d → Eu d →L[ℝ] ℝ) (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : Prop where
  hρ : 0 < ρ
  hτ : 0 < τ
  hd : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt χ (χ1 x) x ∧ HasFDerivAt χ1 (χ2 x) x
  bc : ∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, χ1 x (c x) = 0
  van : ∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → χ y = 0 ∧ χ1 y = 0 ∧ χ2 y = 0
  one : ∀ y ∈ Metric.ball x0 τ, χ y = 1
  rng : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1
  c2b : C2B (Metric.ball x0 ρ ∩ closure Ω) μ Z χ χ1 χ2

lemma C2B.sub' {T S : Set (Eu d)} {μ K : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Eu d → F} {Df : Eu d → Eu d →L[ℝ] F}
    {D2f : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] F} (h : C2B T μ K f Df D2f) (hST : S ⊆ T) : C2B S μ K f Df D2f where
  hK := h.hK
  lip x hx y hy := h.lip x (hST hx) y (hST hy)
  b1 x hx := h.b1 x (hST hx)
  lip1 x hx y hy := h.lip1 x (hST hx) y (hST hy)
  b2 x hx := h.b2 x (hST hx)
  hol2 x hx y hy := h.hol2 x (hST hx) y (hST hy)

end CutDefS

section CutS

variable {d : ℕ}

theorem cut_of_map {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hρ : 0 < ρ) (he : ‖e‖ = 1) (hb : inner ℝ b e = 0)
    (hder : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt Θ (DΘ x) x ∧ HasFDerivAt DΘ (D2Θ x) x)
    (h0 : Θ x0 = 0)
    (hbil : ∀ x ∈ Metric.ball x0 ρ, ‖x - x0‖ ≤ 2 * ‖Θ x‖ ∧ ‖Θ x‖ ≤ 2 * ‖x - x0‖)
    (hobl : ∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, inner ℝ (Θ x) e = 0 ∧ ∃ κ : ℝ, DΘ x (c x) = κ • (b - e))
    (hc2 : C2B (Metric.ball x0 ρ ∩ closure Ω) μ K Θ DΘ D2Θ) :
    ∃ (Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ) (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      CutData Ω μ c x0 ρ Z τ χ χ1 χ2 := by
  obtain ⟨ψ, hψcd, hψcs, hψr, ⟨τψ, hτψ, hψ1⟩, hψ0, hψd0, hψbc⟩ := obBump_props he hb (s := ρ / 4) (by positivity)
  obtain ⟨Kψ, hψC⟩ := cs_C2B' hψcd hψcs hμ0.le hμ1
  have hdiff : Differentiable ℝ ψ := hψcd.differentiable (by norm_cast)
  have h1cd : ContDiff ℝ 2 (fderiv ℝ ψ) := hψcd.fderiv_right (m := 2) le_rfl
  have hdiff1 : Differentiable ℝ (fderiv ℝ ψ) := h1cd.differentiable (by norm_cast)
  have hψd : ∀ z, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z => (hdiff z).hasFDerivAt
  have hψd2 : ∀ z, HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z := fun z => (hdiff1 z).hasFDerivAt
  have hR : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖x - y‖ ≤ 2 * ρ := by
    intro x hx y hy
    have h1 : dist x x0 < ρ := hx.1
    have h2 : dist y x0 < ρ := hy.1
    rw [← dist_eq_norm]
    linarith [dist_triangle_right x y x0]
  obtain ⟨Z, hZ⟩ := C2B.comp hψC hc2 (fun _ _ => Set.mem_univ _) hR hμ0 hμ1
  refine ⟨Z, min (τψ / 2) ρ, ψ ∘ Θ, fun x => (fderiv ℝ ψ (Θ x)).comp (DΘ x),
    fun x => D2comp (fderiv ℝ ψ (Θ x)) (fderiv ℝ (fderiv ℝ ψ) (Θ x)) (DΘ x) (D2Θ x),
    { hρ := hρ, hτ := lt_min (by positivity) hρ, hd := ?_, bc := ?_, van := ?_, one := ?_, rng := ?_, c2b := hZ }⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hder x hx
    exact ⟨(hψd (Θ x)).comp x h1, hasFDerivAt_Dcomp h1 h2 (hψd2 (Θ x))⟩
  · intro x hx
    obtain ⟨hpl, κ, hκ⟩ := hobl x hx
    show (fderiv ℝ ψ (Θ x)) (DΘ x (c x)) = 0
    rw [hκ, map_smul, hψbc (Θ x) hpl, smul_zero]
  · intro y hy hfar
    have hz : ρ / 4 ≤ ‖Θ y‖ := by linarith [(hbil y hy).1]
    have hz' : ρ / 4 / 2 < ‖Θ y‖ := by linarith
    obtain ⟨hf1, hf2⟩ := hψd0 (Θ y) hz'
    refine ⟨hψ0 (Θ y) hz'.le, ?_, ?_⟩
    · show (fderiv ℝ ψ (Θ y)).comp (DΘ y) = 0
      rw [hf1]; exact ContinuousLinearMap.zero_comp _
    · show D2comp (fderiv ℝ ψ (Θ y)) (fderiv ℝ (fderiv ℝ ψ) (Θ y)) (DΘ y) (D2Θ y) = 0
      rw [hf1, hf2]; simp [D2comp]
  · intro y hy
    have hy1 : dist y x0 < min (τψ / 2) ρ := hy
    have hyρ : y ∈ Metric.ball x0 ρ := lt_of_lt_of_le hy1 (min_le_right _ _)
    have hyt : ‖y - x0‖ < τψ / 2 := by rw [← dist_eq_norm]; exact lt_of_lt_of_le hy1 (min_le_left _ _)
    exact hψ1 (Θ y) (by linarith [(hbil y hyρ).2])
  · intro y; exact hψr (Θ y)

theorem cut_boundary {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r1 →
      ∃ (Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ) (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
        CutData Ω μ c x0 ρ Z τ χ χ1 χ2 := by
  obtain ⟨r1, hr1, hr1r0, Λ, hbl, -, -, -⟩ := chart_inv_small hch
  refine ⟨r1, hr1, hr1r0, fun ρ hρ hρr => ?_⟩
  have hsub : Metric.ball x0 ρ ⊆ Metric.ball x0 r0 := Metric.ball_subset_ball (hρr.trans hr1r0)
  have hsub1 : Metric.ball x0 ρ ⊆ Metric.ball x0 r1 := Metric.ball_subset_ball hρr
  have hx0 : x0 ∈ Metric.ball x0 r1 := Metric.mem_ball_self hr1
  refine cut_of_map hμ0 hμ1 hρ hch.he hch.hb (fun x hx => ?_) hch.h0 (fun x hx => ?_) (fun x hx => ?_)
    (hch.c2b.sub' (Set.inter_subset_inter_left _ hsub))
  · exact ⟨(hch.strict x (hsub hx.1)).hasFDerivAt, hch.hd2 x ⟨hsub hx.1, hx.2⟩⟩
  · have := hbl x (hsub1 hx) x0 hx0
    rw [hch.h0, sub_zero] at this
    exact this
  · refine ⟨((hch.side x (hsub hx.1)).2.mp hx.2), ?_⟩
    obtain ⟨κ, -, hκ⟩ := hch.obl x ⟨hsub hx.1, hx.2⟩
    exact ⟨κ, hκ⟩

theorem cut_interior {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {R : ℝ} (hΩ : IsOpen Ω)
    (hd : 0 < d) (hball : Metric.ball x0 R ⊆ Ω) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      ∃ (Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ) (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
        CutData Ω μ c x0 ρ Z τ χ χ1 χ2 := by
  intro ρ hρ hρR
  set e : Eu d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by rw [he_def, EuclideanSpace.norm_single, norm_one]
  have hb : inner ℝ (0 : Eu d) e = 0 := inner_zero_left _
  have hC : C2B (Metric.ball x0 ρ ∩ closure Ω) μ 1 (fun x => x - x0)
      (fun _ => ContinuousLinearMap.id ℝ (Eu d)) (fun _ => 0) :=
    { hK := zero_le_one
      lip := fun x _ y _ => by rw [sub_sub_sub_cancel_right, one_mul]
      b1 := fun _ _ => ContinuousLinearMap.norm_id_le
      lip1 := fun x _ y _ => by rw [sub_self, norm_zero]; positivity
      b2 := fun _ _ => ContinuousLinearMap.opNorm_zero.le.trans zero_le_one
      hol2 := fun x _ y _ => by
        rw [sub_self]; exact ContinuousLinearMap.opNorm_zero.le.trans (by positivity) }
  refine cut_of_map (Θ := fun x => x - x0) (DΘ := fun _ => ContinuousLinearMap.id ℝ (Eu d))
    (D2Θ := fun _ => 0) (b := 0) hμ0 hμ1 hρ he hb (fun x _ => ?_) (sub_self x0) (fun x _ => ?_)
    (fun x hx => ?_) hC
  · exact ⟨(hasFDerivAt_id x).sub_const x0, hasFDerivAt_const _ _⟩
  · constructor <;> linarith [norm_nonneg (x - x0)]
  · exfalso
    have hxΩ : x ∈ Ω := hball (Metric.ball_subset_ball hρR hx.1)
    have : x ∈ Ω ∩ frontier Ω := ⟨hxΩ, hx.2⟩
    rw [hΩ.inter_frontier_eq] at this
    exact this

end CutS

section LocDefS

variable {d : ℕ}

def LocSol (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (ρ lam0 C : ℝ) : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)

theorem LocSol.mono {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ lam0 C ρ' lam0' C' : ℝ}
    (h : LocSol Ω μ c x0 ρ lam0 C) (hρ : ρ' ≤ ρ) (hl0 : 0 < lam0) (hl : lam0 ≤ lam0') (hC : C ≤ C') :
    LocSol Ω μ c x0 ρ' lam0' C' := by
  intro lam hlam g M H hM hH hgb hgh
  have hlp : 0 < lam := hl0.trans_le (hl.trans hlam)
  obtain ⟨W, W1, W2, h1, h2, h3, h4, h5⟩ := h lam (hl.trans hlam) g M H hM hH hgb hgh
  have hs : Metric.ball x0 ρ' ⊆ Metric.ball x0 ρ := Metric.ball_subset_ball hρ
  have hN : 0 ≤ lam ^ (μ / 2) * M + H := add_nonneg (mul_nonneg (Real.rpow_nonneg hlp.le _) hM) hH
  have hi : 0 ≤ 1 / lam := by positivity
  have e1 : 0 ≤ (1 / lam) ^ (μ / 2) := Real.rpow_nonneg hi _
  have e2 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hi _
  refine ⟨W, W1, W2, fun x hx => h1 x ⟨hs hx.1, hx.2⟩, fun x hx => h2 x ⟨hs hx.1, hx.2⟩,
    fun x hx => h3 x ⟨hs hx.1, hx.2⟩, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨b0, b1, b2⟩ := h4 x ⟨hs hx.1, hx.2⟩
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hi) e1) hN
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC e2) e1) hN
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC e1) hN
    -- s15: nlinarith replaced
    -- s15: nlinarith replaced
    -- s15: nlinarith replaced
  · obtain ⟨b0, b1, b2⟩ := h5 x ⟨hs hx.1, hx.2⟩ x' ⟨hs hx'.1, hx'.2⟩
    have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hi) hN) hp
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC e2) hN) hp
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN) hp
    -- s15: nlinarith replaced
    -- s15: nlinarith replaced
    -- s15: nlinarith replaced

end LocDefS

end ObliqueLib

theorem solution (d : ℕ) (hd : 0 < d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hopen : IsOpen Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hV : ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
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
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
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
    (hploc : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        (0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ))) :
    ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (χ2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (lam0 C : ℝ),
      (0 < ρ ∧
        0 < τ ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt χ (χ1 x) x ∧ HasFDerivAt χ1 (χ2 x) x) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, χ1 x (c x) = 0) ∧
        (∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → χ y = 0 ∧ χ1 y = 0 ∧ χ2 y = 0) ∧
        (∀ y ∈ Metric.ball x0 τ, χ y = 1) ∧
        (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        0 ≤ Z ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ x - χ y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x - χ1 y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x - χ2 y‖ ≤ Z * ‖x - y‖ ^ μ)) ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) := by
  intro x0 hx0
  by_cases hxi : x0 ∈ Ω
  · obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen x0 hxi
    obtain ⟨ρ, hρ, hρR, lam0, C, hl, hC, hsol⟩ := ObliqueLib.interior_solver hopen hμ0 hμ1 c hR hball hd hV
    obtain ⟨Z, τ, χ, χ1, χ2, hcut⟩ := ObliqueLib.cut_interior (c := c) hopen hd hball hμ0 hμ1.le ρ hρ hρR
    exact ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, ⟨hcut.hρ, hcut.hτ, hcut.hd, hcut.bc, hcut.van, hcut.one, hcut.rng,
      hcut.c2b.hK, hcut.c2b.lip, hcut.c2b.b1, hcut.c2b.lip1, hcut.c2b.b2, hcut.c2b.hol2⟩, hl, hC, hsol⟩
  · have hfr : x0 ∈ frontier Ω := ⟨hx0, by rwa [hopen.interior_eq]⟩
    obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩,
      ρ, hρ, lam0, C, hl, hC, hsol⟩ := hploc x0 hfr
    have hc : ObliqueLib.ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ :=
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩
    have hs : ObliqueLib.LocSol Ω μ c x0 ρ lam0 C := hsol
    obtain ⟨r1, hr1, -, hcutf⟩ := ObliqueLib.cut_boundary hc hμ0 hμ1.le
    obtain ⟨Z, τ, χ, χ1, χ2, hcut⟩ := hcutf (min ρ r1) (lt_min hρ hr1) (min_le_right _ _)
    exact ⟨min ρ r1, Z, τ, χ, χ1, χ2, lam0, C, ⟨hcut.hρ, hcut.hτ, hcut.hd, hcut.bc, hcut.van, hcut.one,
      hcut.rng, hcut.c2b.hK, hcut.c2b.lip, hcut.c2b.b1, hcut.c2b.lip1, hcut.c2b.b2, hcut.c2b.hol2⟩, hl, hC,
      hs.mono (min_le_left _ _) (by linarith) le_rfl le_rfl⟩
