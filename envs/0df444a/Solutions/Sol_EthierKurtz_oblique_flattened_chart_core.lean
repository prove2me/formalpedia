-- Prove2me | solution 1 for EthierKurtz.oblique_flattened_chart_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:02:18.409186+00:00
-- url     : https://prove2.me/submissions/3128383e-a3a5-4b60-85b6-2d97216c6701

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder

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
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
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
    linarith

end Comp2

section HalfLip

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end HalfLip

section Flat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `φ ↦ φ.smulRight e` as a continuous linear map. -/
noncomputable def sRL (e : F) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.smulRightL ℝ E F).flip e

lemma sRL_apply (e : F) (φ : E →L[ℝ] ℝ) : sRL e φ = φ.smulRight e := rfl

lemma norm_sRL_apply {e : F} (he : ‖e‖ = 1) (φ : E →L[ℝ] ℝ) : ‖sRL e φ‖ = ‖φ‖ := by
  rw [sRL_apply, ContinuousLinearMap.norm_smulRight_apply, he, mul_one]

noncomputable def DFl (e : F) (Dg : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] F := sRL e (Dg x)

noncomputable def D2Fl (e : F) (D2g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  (sRL e).comp (D2g x)

lemma hasFDerivAt_Dfl {Dg : E → E →L[ℝ] ℝ} {D2g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (e : F)
    (hg : HasFDerivAt Dg (D2g x) x) : HasFDerivAt (DFl e Dg) (D2Fl e D2g x) x :=
  (sRL e).hasFDerivAt.comp x hg

theorem C2B.smul_vec {T : Set E} {μ K : ℝ} {g : E → ℝ} {Dg : E → E →L[ℝ] ℝ}
    {D2g : E → E →L[ℝ] E →L[ℝ] ℝ} {e : F} (he : ‖e‖ = 1) (h : C2B T μ K g Dg D2g) :
    C2B T μ K (fun y => g y • e) (DFl e Dg) (D2Fl e D2g) where
  hK := h.hK
  lip x hx y hy := by
    rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    have := h.lip x hx y hy; rwa [Real.norm_eq_abs] at this
  b1 x hx := by rw [DFl, norm_sRL_apply he]; exact h.b1 x hx
  lip1 x hx y hy := by rw [DFl, DFl, ← map_sub, norm_sRL_apply he]; exact h.lip1 x hx y hy
  b2 x hx := by
    refine ContinuousLinearMap.opNorm_le_bound _ h.hK fun v => ?_
    rw [D2Fl, ContinuousLinearMap.comp_apply, norm_sRL_apply he]
    exact ((D2g x).le_opNorm v).trans (by gcongr; exact h.b2 x hx)
  hol2 x hx y hy := by
    have hm : 0 ≤ K * ‖x - y‖ ^ μ := mul_nonneg h.hK (rpow_nonneg (norm_nonneg _) _)
    refine ContinuousLinearMap.opNorm_le_bound _ hm fun v => ?_
    rw [D2Fl, D2Fl, ← ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_apply, norm_sRL_apply he]
    exact ((D2g x - D2g y).le_opNorm v).trans (by gcongr; exact h.hol2 x hx y hy)

/-- `C2B` of `x ↦ x - g x • e` with derivative `id - DFl` and second derivative `-D2Fl`. -/
theorem C2B.flat {T : Set E} {μ K : ℝ} {g : E → ℝ} {Dg : E → E →L[ℝ] ℝ}
    {D2g : E → E →L[ℝ] E →L[ℝ] ℝ} {e : E} (he : ‖e‖ = 1) (h : C2B T μ K g Dg D2g) :
    C2B T μ (1 + K) (fun y => y - g y • e) (fun x => ContinuousLinearMap.id ℝ E - DFl e Dg x)
      (fun x => -D2Fl e D2g x) := by
  have hs := h.smul_vec he
  have hK := h.hK
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have e1 : x - g x • e - (y - g y • e) = (x - y) - (g x • e - g y • e) := by abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have := hs.lip x hx y hy; linarith
  · intro x hx
    refine (norm_sub_le _ _).trans ?_
    have := hs.b1 x hx; have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E); linarith
  · intro x hx y hy
    have e1 : ContinuousLinearMap.id ℝ E - DFl e Dg x - (ContinuousLinearMap.id ℝ E - DFl e Dg y) =
        -(DFl e Dg x - DFl e Dg y) := by abel
    rw [e1, norm_neg]
    exact (hs.lip1 x hx y hy).trans (by gcongr; linarith)
  · intro x hx; rw [ContinuousLinearMap.opNorm_neg]; have := hs.b2 x hx; linarith
  · intro x hx y hy
    have e1 : -D2Fl e D2g x - -D2Fl e D2g y = -(D2Fl e D2g x - D2Fl e D2g y) := by abel
    rw [e1, ContinuousLinearMap.opNorm_neg]
    exact (hs.hol2 x hx y hy).trans (by gcongr; linarith)

end Flat

section PkgDef

end PkgDef

section Glue

variable {n : ℕ}

lemma eu_expand (v : Eu n) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
  exact h.symm

end Glue

section Cutoff

variable {d : ℕ}

lemma holder_continuousAt {μ H : ℝ} (hμ : 0 < μ) {F : Type*} [NormedAddCommGroup F] {f : Eu d → F}
    {s : Set (Eu d)} {y : Eu d} (hs : s ∈ 𝓝 y) (hf : ∀ z ∈ s, ‖f z - f y‖ ≤ H * ‖z - y‖ ^ μ) :
    ContinuousAt f y := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun z : Eu d => H * ‖z - y‖ ^ μ :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hμ.le)
  have ht := hc.tendsto y
  simp only [sub_self, norm_zero, Real.zero_rpow hμ.ne', mul_zero] at ht
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.eventually_of_mem hs hf) ht

theorem cutoff_C1H {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {c : Eu d} {R M0 M1 H : ℝ} (hR : 0 < R)
    {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}
    (hd : ∀ y ∈ Metric.ball c R, HasFDerivAt ψ (ψ1 y) y)
    (hb0 : ∀ y ∈ Metric.ball c R, |ψ y| ≤ M0) (hb1 : ∀ y ∈ Metric.ball c R, ‖ψ1 y‖ ≤ M1)
    (hhol : ∀ y ∈ Metric.ball c R, ∀ z ∈ Metric.ball c R, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) (hH : 0 ≤ H) :
    ∃ (g : Eu d → ℝ) (g1 : Eu d → (Eu d →L[ℝ] ℝ)) (N0 N1 H' : ℝ),
      (∀ y ∈ Metric.ball c (R / 4), g y = ψ y ∧ g1 y = ψ1 y) ∧
      (∀ y, HasFDerivAt g (g1 y) y) ∧ Continuous g1 ∧ (∀ y, |g y| ≤ N0) ∧ (∀ y, ‖g1 y‖ ≤ N1) ∧
      (∀ y z, ‖g1 y - g1 z‖ ≤ H' * ‖y - z‖ ^ μ) ∧ 0 ≤ H' := by
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hb0 c hc)
  have hM1 : 0 ≤ M1 := (norm_nonneg (ψ1 c)).trans (hb1 c hc)
  let f : ContDiffBump c := ⟨R / 4, R / 2, by positivity, by linarith⟩
  set χ : Eu d → ℝ := ⇑f with hχdef
  have hχs : ContDiff ℝ 2 χ := f.contDiff
  set Dχ := fderiv ℝ χ
  have hχd : ∀ y, HasFDerivAt χ (Dχ y) y := fun y =>
    ((hχs.differentiable (by norm_num)) y).hasFDerivAt
  have hDχc : Continuous Dχ := hχs.continuous_fderiv (by norm_num)
  have hDχs : ContDiff ℝ 1 Dχ := hχs.fderiv_right (by norm_num)
  obtain ⟨Bχ, hBχ⟩ := hDχc.bounded_above_of_compact_support (f.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨B2, hB2⟩ := (hDχs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    ((f.hasCompactSupport.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg (Dχ c)).trans (hBχ c)
  have hB20 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ Dχ c)).trans (hB2 c)
  have h01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => ⟨f.nonneg, f.le_one⟩
  have hlipχ : ∀ y z, |χ y - χ z| ≤ Bχ * ‖y - z‖ := fun y z => by
    have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x _ => (hχd x).hasFDerivWithinAt)
      (fun x _ => hBχ x) (Set.mem_univ z) (Set.mem_univ y)
    rwa [Real.norm_eq_abs] at this
  have hlipD : ∀ y z, ‖Dχ y - Dχ z‖ ≤ B2 * ‖y - z‖ := fun y z =>
    convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => ((hDχs.differentiable (by norm_num)) x).hasFDerivAt.hasFDerivWithinAt)
      (fun x _ => hB2 x) (Set.mem_univ z) (Set.mem_univ y)
  -- χ = 1 near the small ball, χ = 0 far away
  have hin : ∀ y ∈ Metric.ball c (R / 4), χ y = 1 ∧ Dχ y = 0 := by
    intro y hy
    have hev : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) fun z hz =>
        f.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    refine ⟨hev.self_of_nhds, ?_⟩
    show fderiv ℝ χ y = 0
    rw [hev.fderiv_eq]; exact fderiv_const_apply 1
  have hout : ∀ y, R / 2 < dist y c → χ y = 0 ∧ Dχ y = 0 := by
    intro y hy
    have hopen : IsOpen {z : Eu d | R / 2 < dist z c} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have hev : χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz => f.zero_of_le_dist (le_of_lt hz)
    refine ⟨hev.self_of_nhds, ?_⟩
    show fderiv ℝ χ y = 0
    rw [hev.fderiv_eq]; exact fderiv_const_apply 0
  set g : Eu d → ℝ := fun y => χ y * ψ y
  set g1 : Eu d → (Eu d →L[ℝ] ℝ) := fun y => χ y • ψ1 y + ψ y • Dχ y
  have hg1z : ∀ y, R / 2 < dist y c → g1 y = 0 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hout y hy
    simp [g1, h1, h2]
  have hgz : ∀ y, R / 2 < dist y c → g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    intro y hy
    have hopen : IsOpen {z : Eu d | R / 2 < dist z c} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    exact Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz => by simp [g, (hout z hz).1]
  have hg1zev : ∀ y, R / 2 < dist y c → g1 =ᶠ[𝓝 y] fun _ => 0 := by
    intro y hy
    have hopen : IsOpen {z : Eu d | R / 2 < dist z c} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    exact Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz => hg1z z hz
  have hfar : ∀ y, y ∉ Metric.ball c R → R / 2 < dist y c := by
    intro y hy
    rw [Metric.mem_ball, not_lt] at hy; linarith
  set N1 := M1 + M0 * Bχ
  have hN1 : 0 ≤ N1 := by positivity
  have hb1g : ∀ y, ‖g1 y‖ ≤ N1 := by
    intro y
    by_cases hy : y ∈ Metric.ball c R
    · refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h01 y).1]
      have e1 : χ y * ‖ψ1 y‖ ≤ M1 := by
        exact (mul_le_of_le_one_left (norm_nonneg _) (h01 y).2).trans (hb1 y hy)
      have e2 : |ψ y| * ‖Dχ y‖ ≤ M0 * Bχ :=
        mul_le_mul (hb0 y hy) (hBχ y) (norm_nonneg _) hM0
      linarith
    · rw [hg1z y (hfar y hy), norm_zero]; exact hN1
  set Lc := (Bχ * M1 + M0 * B2 + M1 * Bχ) * (R / 2) ^ (1 - μ)
  have hLc : 0 ≤ Lc := by positivity
  refine ⟨g, g1, M0, N1, H + Lc + 2 * N1 * (2 / R) ^ μ, ?_, ?_, ?_, ?_, hb1g, ?_, by positivity⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := hin y hy
    refine ⟨by simp [g, h1], by simp [g1, h1, h2]⟩
  · intro y
    by_cases hy : y ∈ Metric.ball c R
    · exact (hχd y).mul (hd y hy)
    · have h0 := hg1z y (hfar y hy)
      rw [h0]
      exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq (hgz y (hfar y hy))
  · refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hy : y ∈ Metric.ball c R
    · have hψ1 : ContinuousAt ψ1 y := holder_continuousAt hμ0 (Metric.isOpen_ball.mem_nhds hy)
        fun z hz => hhol z hz y hy
      exact ((hχd y).continuousAt.smul hψ1).add ((hd y hy).continuousAt.smul hDχc.continuousAt)
    · exact continuousAt_const.congr (hg1zev y (hfar y hy)).symm
  · intro y
    by_cases hy : y ∈ Metric.ball c R
    · show |χ y * ψ y| ≤ M0
      rw [abs_mul, abs_of_nonneg (h01 y).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (h01 y).2).trans (hb0 y hy)
    · show |χ y * ψ y| ≤ M0
      rw [(hout y (hfar y hy)).1]; simpa using hM0
  · intro y z
    set r := ‖y - z‖
    have hr0 : 0 ≤ r := norm_nonneg _
    by_cases hrf : R / 2 ≤ r
    · -- far apart: boundedness
      have h1 : 1 ≤ (2 / R) ^ μ * r ^ μ := by
        rw [← Real.mul_rpow (by positivity) hr0]
        refine Real.one_le_rpow ?_ hμ0.le
        rw [div_mul_eq_mul_div, le_div_iff₀ hR]; linarith
      have h2 : ‖g1 y - g1 z‖ ≤ 2 * N1 := by
        refine (norm_sub_le _ _).trans ?_; linarith [hb1g y, hb1g z]
      have h3 : 0 ≤ (H + Lc) * r ^ μ := by positivity
      calc ‖g1 y - g1 z‖ ≤ 2 * N1 * ((2 / R) ^ μ * r ^ μ) := h2.trans (le_mul_of_one_le_right (by linarith) h1)
        _ ≤ (H + Lc + 2 * N1 * (2 / R) ^ μ) * r ^ μ := by linarith
    push_neg at hrf
    by_cases hy : y ∈ Metric.ball c R
    · by_cases hz : z ∈ Metric.ball c R
      · -- main estimate
        have hid : g1 y - g1 z = χ y • (ψ1 y - ψ1 z) + (χ y - χ z) • ψ1 z +
            (ψ y • (Dχ y - Dχ z) + (ψ y - ψ z) • Dχ z) := by
          simp only [g1]
          first | module | (rw [sub_smul, smul_sub, smul_sub, sub_smul]; abel)
        have hψl : |ψ y - ψ z| ≤ M1 * r := by
          have := (convex_ball c R).norm_image_sub_le_of_norm_hasFDerivWithin_le
            (fun x hx => (hd x hx).hasFDerivWithinAt) hb1 hz hy
          rwa [Real.norm_eq_abs] at this
        have t1 : ‖χ y • (ψ1 y - ψ1 z)‖ ≤ H * r ^ μ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h01 y).1]
          exact (mul_le_of_le_one_left (norm_nonneg _) (h01 y).2).trans (hhol y hy z hz)
        have t2 : ‖(χ y - χ z) • ψ1 z‖ ≤ Bχ * r * M1 := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hlipχ y z) (hb1 z hz) (norm_nonneg _) (by positivity)
        have t3 : ‖ψ y • (Dχ y - Dχ z)‖ ≤ M0 * (B2 * r) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hb0 y hy) (hlipD y z) (norm_nonneg _) hM0
        have t4 : ‖(ψ y - ψ z) • Dχ z‖ ≤ M1 * r * Bχ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul hψl (hBχ z) (norm_nonneg _) (by positivity)
        have hlh : r ≤ (R / 2) ^ (1 - μ) * r ^ μ := lip_le_hol hr0 hrf.le hμ0.le hμ1
        have hsum : ‖g1 y - g1 z‖ ≤ H * r ^ μ + (Bχ * M1 + M0 * B2 + M1 * Bχ) * r := by
          rw [hid]
          refine (norm_add_le _ _).trans ?_
          refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
          linarith
        have hK0 : 0 ≤ Bχ * M1 + M0 * B2 + M1 * Bχ := by positivity
        have h5 : (Bχ * M1 + M0 * B2 + M1 * Bχ) * r ≤ Lc * r ^ μ := by
          calc (Bχ * M1 + M0 * B2 + M1 * Bχ) * r
              ≤ (Bχ * M1 + M0 * B2 + M1 * Bχ) * ((R / 2) ^ (1 - μ) * r ^ μ) := by gcongr
            _ = Lc * r ^ μ := by ring
        have h6 : 0 ≤ 2 * N1 * (2 / R) ^ μ * r ^ μ := by positivity
        linarith
      · have hzf := hfar z hz
        have hyc : R / 2 < dist y c := by
          have := dist_triangle z y c
          rw [dist_eq_norm z y, norm_sub_rev] at this
          have : R ≤ dist z c := by rw [Metric.mem_ball, not_lt] at hz; exact hz
          linarith
        rw [hg1z y hyc, hg1z z hzf, sub_zero, norm_zero]; positivity
    · have hyf := hfar y hy
      have hzc : R / 2 < dist z c := by
        have := dist_triangle y z c
        rw [dist_eq_norm y z] at this
        have : R ≤ dist y c := by rw [Metric.mem_ball, not_lt] at hy; exact hy
        linarith
      rw [hg1z y hyf, hg1z z hzc, sub_zero, norm_zero]; positivity

end Cutoff

section Graph

variable {n : ℕ}

noncomputable def eL (n : ℕ) : Eu (n + 1) := EuclideanSpace.single (Fin.last n) 1

noncomputable def piL (n : ℕ) : Eu (n + 1) →L[ℝ] Eu n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))
      map_add' := fun a b => by refine PiLp.ext fun i => ?_; simp
      map_smul' := fun c a => by refine PiLp.ext fun i => ?_; simp }

noncomputable def iL (n : ℕ) : Eu n →L[ℝ] Eu (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Fin.lastCases (0 : ℝ) (fun i => z i))
      map_add' := fun a b => by
        refine PiLp.ext fun j => ?_
        cases j using Fin.lastCases <;> simp
      map_smul' := fun c a => by
        refine PiLp.ext fun j => ?_
        cases j using Fin.lastCases <;> simp }

/-- The graph map of the Definitions' boundary charts. -/
noncomputable def gr (u : Eu n → ℝ) (z : Eu n) : Eu (n + 1) :=
  (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) : EuclideanSpace ℝ (Fin (n + 1)))

lemma piL_apply (ξ : Eu (n + 1)) (i : Fin n) : piL n ξ i = ξ (Fin.castSucc i) := rfl

lemma iL_castSucc (z : Eu n) (i : Fin n) : iL n z (Fin.castSucc i) = z i := by simp [iL]

lemma iL_last (z : Eu n) : iL n z (Fin.last n) = 0 := by simp [iL]

lemma eL_castSucc (i : Fin n) : eL n (Fin.castSucc i) = 0 := by
  simp [eL, EuclideanSpace.single_apply, Fin.castSucc_ne_last]

lemma eL_last : eL n (Fin.last n) = 1 := by simp [eL]

lemma norm_eL : ‖eL n‖ = 1 := by simp [eL]

lemma gr_castSucc (u : Eu n → ℝ) (z : Eu n) (i : Fin n) : gr u z (Fin.castSucc i) = z i := by simp [gr]

lemma gr_last (u : Eu n → ℝ) (z : Eu n) : gr u z (Fin.last n) = u z := by simp [gr]

lemma piL_iL (z : Eu n) : piL n (iL n z) = z := PiLp.ext fun i => by rw [piL_apply, iL_castSucc]

lemma piL_gr (u : Eu n → ℝ) (z : Eu n) : piL n (gr u z) = z :=
  PiLp.ext fun i => by rw [piL_apply, gr_castSucc]

lemma inner_eL (ξ : Eu (n + 1)) : inner ℝ ξ (eL n) = ξ (Fin.last n) := by
  simp [eL, EuclideanSpace.inner_single_right]

lemma decomp (ξ : Eu (n + 1)) : ξ = iL n (piL n ξ) + ξ (Fin.last n) • eL n := by
  refine PiLp.ext fun j => ?_
  cases j using Fin.lastCases with
  | last => simp [iL_last, eL_last]
  | cast i => simp [iL_castSucc, eL_castSucc, piL_apply]

lemma gr_eq (u : Eu n → ℝ) (z : Eu n) : gr u z = iL n z + u z • eL n := by
  refine PiLp.ext fun j => ?_
  cases j using Fin.lastCases with
  | last => simp [iL_last, eL_last, gr_last]
  | cast i => simp [iL_castSucc, eL_castSucc, gr_castSucc]

lemma inner_iL_eL (z : Eu n) : inner ℝ (iL n z) (eL n) = 0 := by rw [inner_eL, iL_last]

lemma norm_sq_split (ξ : Eu (n + 1)) : ‖ξ‖ ^ 2 = ‖piL n ξ‖ ^ 2 + ξ (Fin.last n) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [piL_apply, Real.norm_eq_abs, sq_abs]

lemma norm_piL_apply_le (ξ : Eu (n + 1)) : ‖piL n ξ‖ ≤ ‖ξ‖ := by
  have h := norm_sq_split ξ
  have h2 : ‖piL n ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith [sq_nonneg (ξ (Fin.last n))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma norm_piL_le : ‖piL n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by rw [one_mul]; exact norm_piL_apply_le ξ

lemma norm_iL_apply (z : Eu n) : ‖iL n z‖ = ‖z‖ := by
  have h := norm_sq_split (iL n z)
  rw [piL_iL, iL_last] at h
  have h2 : ‖iL n z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- Flattening map and its global inverse. -/
noncomputable def Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) : Eu (n + 1) := ξ - u (piL n ξ) • eL n

lemma inner_Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) :
    inner ℝ (Fl u ξ) (eL n) = ξ (Fin.last n) - u (piL n ξ) := by
  rw [Fl, inner_sub_left, real_inner_smul_left, inner_eL, inner_eL, eL_last, mul_one]

/-- `C2B` of a continuous linear map. -/
lemma C2B_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : Set E} {μ K : ℝ} (L : E →L[ℝ] F) (hL : ‖L‖ ≤ K) :
    C2B T μ K L (fun _ => L) (fun _ => 0) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hL
  refine ⟨hK, fun x _ y _ => ?_, fun _ _ => hL, fun x _ y _ => ?_, fun _ _ => ?_, fun x _ y _ => ?_⟩
  · rw [← map_sub]; exact (L.le_opNorm _).trans (by gcongr)
  · simp only [sub_self, norm_zero]; exact mul_nonneg hK (norm_nonneg _)
  · exact ContinuousLinearMap.opNorm_zero.le.trans hK
  · simp only [sub_self]
    exact ContinuousLinearMap.opNorm_zero.le.trans (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))

noncomputable def DFlat (Du : Eu n → Eu n →L[ℝ] ℝ) (ξ : Eu (n + 1)) : Eu (n + 1) →L[ℝ] Eu (n + 1) :=
  ContinuousLinearMap.id ℝ (Eu (n + 1)) - DFl (eL n) (fun ξ => (Du (piL n ξ)).comp (piL n)) ξ

noncomputable def D2Flat (Du : Eu n → Eu n →L[ℝ] ℝ) (D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ)
    (ξ : Eu (n + 1)) : Eu (n + 1) →L[ℝ] Eu (n + 1) →L[ℝ] Eu (n + 1) :=
  -D2Fl (eL n) (fun ξ => D2comp (Du (piL n ξ)) (D2u (piL n ξ)) (piL n) 0) ξ

lemma hasFDerivAt_DFlat {Du : Eu n → Eu n →L[ℝ] ℝ} {D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ}
    {ξ : Eu (n + 1)} (hu : HasFDerivAt Du (D2u (piL n ξ)) (piL n ξ)) :
    HasFDerivAt (DFlat Du) (D2Flat Du D2u ξ) ξ := by
  have h1 : HasFDerivAt (fun ξ => (Du (piL n ξ)).comp (piL n))
      (D2comp (Du (piL n ξ)) (D2u (piL n ξ)) (piL n) 0) ξ :=
    hasFDerivAt_Dcomp (f := piL n) (Df := fun _ => piL n) (piL n).hasFDerivAt (hasFDerivAt_const _ _) hu
  exact (hasFDerivAt_Dfl (eL n) h1).const_sub (ContinuousLinearMap.id ℝ (Eu (n + 1)))

/-- `C2B` of the flattening map on `closedBall 0 r` from `C2B` of `u` on `closedBall 0 r`. -/
theorem Fl_C2B {u : Eu n → ℝ} {Du : Eu n → Eu n →L[ℝ] ℝ} {D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ}
    {r μ K : ℝ} (hu : C2B (Metric.closedBall 0 r) μ K u Du D2u) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ K', C2B (Metric.closedBall (0 : Eu (n + 1)) r) μ K' (Fl u) (DFlat Du) (D2Flat Du D2u) := by
  have hπ : C2B (Metric.closedBall (0 : Eu (n + 1)) r) μ 1 (piL n) (fun _ => piL n) (fun _ => 0) :=
    C2B_clm (piL n) norm_piL_le
  have hmap : ∀ ξ ∈ Metric.closedBall (0 : Eu (n + 1)) r, piL n ξ ∈ Metric.closedBall (0 : Eu n) r := by
    intro ξ hξ
    rw [mem_closedBall_zero_iff] at hξ ⊢
    exact (norm_piL_apply_le ξ).trans hξ
  have hR : ∀ x ∈ Metric.closedBall (0 : Eu (n + 1)) r, ∀ y ∈ Metric.closedBall (0 : Eu (n + 1)) r,
      ‖x - y‖ ≤ 2 * r := by
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx hy
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  obtain ⟨K2, hc⟩ := C2B.comp hu hπ hmap hR hμ0 hμ1
  exact ⟨1 + K2, hc.flat norm_eL⟩

end Graph

section Side

variable {n : ℕ}

end Side

section SideDef

variable {n : ℕ}

end SideDef

section C1Hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f` is `C^{1,μ}` on `T` with bounds `M0` (value), `M1` (derivative), `H` (Hölder constant of the derivative). -/
structure C1Hb (T : Set E) (μ M0 M1 H : ℝ) (f : E → ℝ) (f1 : E → E →L[ℝ] ℝ) : Prop where
  hd : ∀ y ∈ T, HasFDerivAt f (f1 y) y
  b0 : ∀ y ∈ T, |f y| ≤ M0
  b1 : ∀ y ∈ T, ‖f1 y‖ ≤ M1
  hol : ∀ y ∈ T, ∀ z ∈ T, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ
  hH : 0 ≤ H

lemma C1Hb.mono {T S : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (hST : S ⊆ T) : C1Hb S μ M0 M1 H f f1 :=
  ⟨fun y hy => h.hd y (hST hy), fun y hy => h.b0 y (hST hy), fun y hy => h.b1 y (hST hy),
    fun y hy z hz => h.hol y (hST hy) z (hST hz), h.hH⟩

lemma C1Hb.lip {T : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (hT : Convex ℝ T) {y z : E} (hy : y ∈ T) (hz : z ∈ T) :
    |f y - f z| ≤ M1 * ‖y - z‖ := by
  have := hT.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (h.hd x hx).hasFDerivWithinAt) h.b1 hz hy
  simpa [Real.norm_eq_abs] using this

lemma C1Hb_const (T : Set E) (μ c : ℝ) : C1Hb T μ |c| 0 0 (fun _ => c) (fun _ => 0) :=
  ⟨fun y _ => hasFDerivAt_const c y, fun _ _ => le_rfl, fun _ _ => by simp, fun _ _ _ _ => by simp, le_rfl⟩

lemma C1Hb.add {T : Set E} {μ M0 M1 H N0 N1 H' : ℝ} {f g : E → ℝ} {f1 g1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (hg : C1Hb T μ N0 N1 H' g g1) :
    C1Hb T μ (M0 + N0) (M1 + N1) (H + H') (fun y => f y + g y) (fun y => f1 y + g1 y) := by
  refine ⟨fun y hy => (hf.hd y hy).add (hg.hd y hy), fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, add_nonneg hf.hH hg.hH⟩
  · exact (abs_add_le _ _).trans (add_le_add (hf.b0 y hy) (hg.b0 y hy))
  · exact (norm_add_le _ _).trans (add_le_add (hf.b1 y hy) (hg.b1 y hy))
  · have h1 : f1 y + g1 y - (f1 z + g1 z) = (f1 y - f1 z) + (g1 y - g1 z) := by abel
    rw [h1, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.hol y hy z hz) (hg.hol y hy z hz))

lemma C1Hb.const_mul {T : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (a : ℝ) :
    C1Hb T μ (|a| * M0) (|a| * M1) (|a| * H) (fun y => a * f y) (fun y => a • f1 y) := by
  refine ⟨fun y hy => (hf.hd y hy).const_mul a, fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, mul_nonneg (abs_nonneg a) hf.hH⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.b0 y hy) (abs_nonneg a)
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hf.b1 y hy) (abs_nonneg a)
  · have hs : a • f1 y - a • f1 z = a • (f1 y - f1 z) := by
      ext v; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    rw [hs, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.hol y hy z hz) (abs_nonneg a)

lemma C1Hb.sum {T : Set E} {μ : ℝ} {ι : Type*} (s : Finset ι) {M0 M1 H : ι → ℝ} {f : ι → E → ℝ}
    {f1 : ι → E → E →L[ℝ] ℝ} (hf : ∀ i ∈ s, C1Hb T μ (M0 i) (M1 i) (H i) (f i) (f1 i)) :
    C1Hb T μ (∑ i ∈ s, M0 i) (∑ i ∈ s, M1 i) (∑ i ∈ s, H i) (fun y => ∑ i ∈ s, f i y)
      (fun y => ∑ i ∈ s, f1 i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using C1Hb_const T μ 0
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

lemma C1Hb.mul {T : Set E} {μ M0 M1 H N0 N1 H' R : ℝ} {f g : E → ℝ} {f1 g1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (hg : C1Hb T μ N0 N1 H' g g1) (hT : Convex ℝ T)
    (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hM0' : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hN0 : 0 ≤ N0) (hN1' : 0 ≤ N1) :
    C1Hb T μ (M0 * N0) (M0 * N1 + N0 * M1) (M0 * H' + N0 * H + 2 * (M1 * N1) * R ^ (1 - μ))
      (fun y => f y * g y) (fun y => f y • g1 y + g y • f1 y) := by
  have hM0 : ∀ y ∈ T, 0 ≤ M0 := fun y hy => (abs_nonneg _).trans (hf.b0 y hy)
  have hN1 : ∀ y ∈ T, 0 ≤ N1 := fun y hy => (norm_nonneg _).trans (hg.b1 y hy)
  refine ⟨fun y hy => (hf.hd y hy).mul (hg.hd y hy), fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hf.b0 y hy) (hg.b0 y hy) (abs_nonneg _) (hM0 y hy)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hf.b0 y hy) (hg.b1 y hy) (norm_nonneg _) (hM0 y hy)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hg.b0 y hy) (hf.b1 y hy) (norm_nonneg _) hN0
  · have hd : f y • g1 y + g y • f1 y - (f z • g1 z + g z • f1 z) =
        f y • (g1 y - g1 z) + (f y - f z) • g1 z + g y • (f1 y - f1 z) + (g y - g z) • f1 z := by
      ext v; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have hyz : ‖y - z‖ ≤ R ^ (1 - μ) * ‖y - z‖ ^ μ := lip_le_hol (norm_nonneg _) (hR y hy z hz) hμ0 hμ1
    have hp : 0 ≤ ‖y - z‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have e1 : ‖f y • (g1 y - g1 z)‖ ≤ M0 * (H' * ‖y - z‖ ^ μ) := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hf.b0 y hy) (hg.hol y hy z hz) (norm_nonneg _) (hM0 y hy)
    have e2 : ‖(f y - f z) • g1 z‖ ≤ (M1 * ‖y - z‖) * N1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hf.lip hT hy hz) (hg.b1 z hz) (norm_nonneg _) (mul_nonneg hM1 (norm_nonneg _))
    have e3 : ‖g y • (f1 y - f1 z)‖ ≤ N0 * (H * ‖y - z‖ ^ μ) := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hg.b0 y hy) (hf.hol y hy z hz) (norm_nonneg _) hN0
    have e4 : ‖(g y - g z) • f1 z‖ ≤ (N1 * ‖y - z‖) * M1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hg.lip hT hy hz) (hf.b1 z hz) (norm_nonneg _) (mul_nonneg (hN1 y hy) (norm_nonneg _))
    rw [hd]
    have e5 : (M1 * ‖y - z‖) * N1 + (N1 * ‖y - z‖) * M1 ≤ 2 * (M1 * N1) * (R ^ (1 - μ) * ‖y - z‖ ^ μ) := by
      have := mul_le_mul_of_nonneg_left hyz (mul_nonneg hM1 (hN1 y hy)); linarith
    calc _ ≤ ‖f y • (g1 y - g1 z)‖ + ‖(f y - f z) • g1 z‖ + ‖g y • (f1 y - f1 z)‖ + ‖(g y - g z) • f1 z‖ :=
          norm_add₄_le
      _ ≤ M0 * (H' * ‖y - z‖ ^ μ) + (M1 * ‖y - z‖) * N1 + N0 * (H * ‖y - z‖ ^ μ) + (N1 * ‖y - z‖) * M1 := by
          linarith
      _ ≤ (M0 * H' + N0 * H + 2 * (M1 * N1) * R ^ (1 - μ)) * ‖y - z‖ ^ μ := by linarith
      _ ≤ _ := le_rfl
  · have := Real.rpow_nonneg hR0 (1 - μ)
    have := hf.hH; have := hg.hH
    positivity

lemma C1Hb.inv {T : Set E} {μ M0 M1 H R m : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (hT : Convex ℝ T) (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hm : 0 < m) (hfm : ∀ y ∈ T, m ≤ |f y|) :
    C1Hb T μ m⁻¹ (M1 / m ^ 2) (H / m ^ 2 + 2 * M0 * M1 / m ^ 4 * M1 * R ^ (1 - μ))
      (fun y => (f y)⁻¹) (fun y => -((f y) ^ 2)⁻¹ • f1 y) := by
  have hne : ∀ y ∈ T, f y ≠ 0 := fun y hy h => by have := hfm y hy; rw [h, abs_zero] at this; linarith
  have hsq : ∀ y ∈ T, m ^ 2 ≤ f y ^ 2 := fun y hy => by
    have := pow_le_pow_left₀ hm.le (hfm y hy) 2; rwa [sq_abs] at this
  have hinv : ∀ y ∈ T, (f y ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ := fun y hy => inv_anti₀ (by positivity) (hsq y hy)
  have hsp : ∀ y ∈ T, 0 < f y ^ 2 := fun y hy => lt_of_lt_of_le (by positivity) (hsq y hy)
  have hm0 : m ≠ 0 := hm.ne'
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy z hz => ?_, ?_⟩
  · have h1 := (hasDerivAt_inv (hne y hy)).hasFDerivAt.comp y (hf.hd y hy)
    refine h1.congr_fderiv ?_
    ext v; simp [mul_comm]
  · rw [abs_inv]; exact inv_anti₀ hm (hfm y hy)
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hsp y hy)), div_eq_inv_mul]
    exact mul_le_mul (hinv y hy) (hf.b1 y hy) (norm_nonneg _) (by positivity)
  · have hpa := hsp y hy; have hpb := hsp z hz
    set a := f y; set b := f z
    have ha := hne y hy; have hb := hne z hz
    have hd : -(a ^ 2)⁻¹ • f1 y - -(b ^ 2)⁻¹ • f1 z =
        -(a ^ 2)⁻¹ • (f1 y - f1 z) - ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) • f1 z := by
      ext v; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have hab : |(a ^ 2)⁻¹ - (b ^ 2)⁻¹| ≤ 2 * M0 * M1 / m ^ 4 * ‖y - z‖ := by
      rw [inv_sub_inv (pow_ne_zero 2 ha) (pow_ne_zero 2 hb), abs_div,
        show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, abs_mul,
        abs_of_pos (mul_pos hpa hpb), div_le_iff₀ (mul_pos hpa hpb)]
      have h1 : |b - a| ≤ M1 * ‖y - z‖ := by rw [abs_sub_comm]; exact hf.lip hT hy hz
      have h2 : |b + a| ≤ 2 * M0 := (abs_add_le _ _).trans (by linarith [hf.b0 y hy, hf.b0 z hz])
      have h4 : m ^ 4 ≤ a ^ 2 * b ^ 2 := by
        have := mul_le_mul (hsq y hy) (hsq z hz) (by positivity) (by positivity); linarith
      have h5 : |b - a| * |b + a| ≤ M1 * ‖y - z‖ * (2 * M0) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM1 (norm_nonneg _))
      have h6 : M1 * ‖y - z‖ * (2 * M0) = 2 * M0 * M1 / m ^ 4 * ‖y - z‖ * m ^ 4 := by
        field_simp
      rw [h6] at h5
      exact h5.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    have hyz : ‖y - z‖ ≤ R ^ (1 - μ) * ‖y - z‖ ^ μ := lip_le_hol (norm_nonneg _) (hR y hy z hz) hμ0 hμ1
    rw [hd]
    have e1 : ‖-(a ^ 2)⁻¹ • (f1 y - f1 z)‖ ≤ (m ^ 2)⁻¹ * (H * ‖y - z‖ ^ μ) := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpa)]
      exact mul_le_mul (hinv y hy) (hf.hol y hy z hz) (norm_nonneg _) (by positivity)
    have e2 : ‖((a ^ 2)⁻¹ - (b ^ 2)⁻¹) • f1 z‖ ≤ 2 * M0 * M1 / m ^ 4 * ‖y - z‖ * M1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hab (hf.b1 z hz) (norm_nonneg _) (by positivity)
    set c := 2 * M0 * M1 / m ^ 4
    have hc0 : 0 ≤ c := by positivity
    have e3 : c * ‖y - z‖ * M1 ≤ c * M1 * (R ^ (1 - μ) * ‖y - z‖ ^ μ) := by
      have h7 : c * ‖y - z‖ * M1 = c * M1 * ‖y - z‖ := by ring
      rw [h7]; exact mul_le_mul_of_nonneg_left hyz (mul_nonneg hc0 hM1)
    have h8 : (H / m ^ 2 + c * M1 * R ^ (1 - μ)) * ‖y - z‖ ^ μ =
        (m ^ 2)⁻¹ * (H * ‖y - z‖ ^ μ) + c * M1 * (R ^ (1 - μ) * ‖y - z‖ ^ μ) := by ring
    rw [h8]
    exact (norm_sub_le _ _).trans (by linarith)
  · have := Real.rpow_nonneg hR0 (1 - μ); have := hf.hH; positivity

lemma C1Hb.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F} {T : Set E}
    {μ M0 M1 H K R : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ} (hf : C1Hb T μ M0 M1 H f f1)
    {τ : F → E} {Dτ : F → F →L[ℝ] E} {D2τ : F → F →L[ℝ] F →L[ℝ] E}
    (hτ : C2B S μ K τ Dτ D2τ) (hτd : ∀ y ∈ S, HasFDerivAt τ (Dτ y) y) (hmap : ∀ y ∈ S, τ y ∈ T)
    (hR : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hM1 : 0 ≤ M1) :
    C1Hb S μ M0 (M1 * K) (H * K ^ μ * K + M1 * K * R ^ (1 - μ)) (fun y => f (τ y))
      (fun y => (f1 (τ y)).comp (Dτ y)) := by
  have hK := hτ.hK
  refine ⟨fun y hy => (hf.hd (τ y) (hmap y hy)).comp y (hτd y hy), fun y hy => hf.b0 _ (hmap y hy),
    fun y hy => ?_, fun y hy z hz => ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hf.b1 _ (hmap y hy)) (hτ.b1 y hy) (norm_nonneg _) hM1)
  · have hd : (f1 (τ y)).comp (Dτ y) - (f1 (τ z)).comp (Dτ z) =
        (f1 (τ y) - f1 (τ z)).comp (Dτ y) + (f1 (τ z)).comp (Dτ y - Dτ z) := by
      ext v; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, map_sub]; ring
    have hyz : ‖y - z‖ ≤ R ^ (1 - μ) * ‖y - z‖ ^ μ := lip_le_hol (norm_nonneg _) (hR y hy z hz) hμ0 hμ1
    have hτl : ‖τ y - τ z‖ ^ μ ≤ K ^ μ * ‖y - z‖ ^ μ := by
      rw [← Real.mul_rpow hK (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hτ.lip y hy z hz) hμ0
    have e1 : ‖(f1 (τ y) - f1 (τ z)).comp (Dτ y)‖ ≤ H * (K ^ μ * ‖y - z‖ ^ μ) * K :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
        ((hf.hol _ (hmap y hy) _ (hmap z hz)).trans (mul_le_mul_of_nonneg_left hτl hf.hH))
        (hτ.b1 y hy) (norm_nonneg _) (mul_nonneg hf.hH (mul_nonneg (Real.rpow_nonneg hK _)
          (Real.rpow_nonneg (norm_nonneg _) _))))
    have e2 : ‖(f1 (τ z)).comp (Dτ y - Dτ z)‖ ≤ M1 * (K * (R ^ (1 - μ) * ‖y - z‖ ^ μ)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hf.b1 _ (hmap z hz))
        ((hτ.lip1 y hy z hz).trans (mul_le_mul_of_nonneg_left hyz hK)) (norm_nonneg _) hM1)
    rw [hd]
    have h8 : (H * K ^ μ * K + M1 * K * R ^ (1 - μ)) * ‖y - z‖ ^ μ =
        H * (K ^ μ * ‖y - z‖ ^ μ) * K + M1 * (K * (R ^ (1 - μ) * ‖y - z‖ ^ μ)) := by ring
    rw [h8]
    exact (norm_add_le _ _).trans (add_le_add e1 e2)
  · have := Real.rpow_nonneg hR0 (1 - μ); have := Real.rpow_nonneg hK μ; have := hf.hH; positivity

end C1Hb

section Transfer

variable {n : ℕ}

end Transfer

section Coef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma C1Hb.weaken {T : Set E} {μ M0 M1 H M0' M1' H' : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (h0 : M0 ≤ M0') (h1 : M1 ≤ M1') (h2 : H ≤ H') :
    C1Hb T μ M0' M1' H' f f1 :=
  ⟨h.hd, fun y hy => (h.b0 y hy).trans h0, fun y hy => (h.b1 y hy).trans h1,
    fun y hy z hz => (h.hol y hy z hz).trans
      (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) _)), h.hH.trans h2⟩

/-- `f` is `C^{1,μ}` on `T` with some bounds. -/
def C1ex (T : Set E) (μ : ℝ) (f : E → ℝ) : Prop :=
  ∃ M0 M1 H : ℝ, ∃ f1 : E → E →L[ℝ] ℝ, C1Hb T μ M0 M1 H f f1

lemma C1ex.mono {T S : Set E} {μ : ℝ} {f : E → ℝ} (h : C1ex T μ f) (hST : S ⊆ T) : C1ex S μ f := by
  obtain ⟨M0, M1, H, f1, h⟩ := h
  exact ⟨M0, M1, H, f1, h.mono hST⟩

lemma C1ex_const (T : Set E) (μ c : ℝ) : C1ex T μ (fun _ => c) := ⟨_, _, _, _, C1Hb_const T μ c⟩

lemma C1ex.add {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) :
    C1ex T μ (fun y => f y + g y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  obtain ⟨N0, N1, H', g1, hg⟩ := hg
  exact ⟨_, _, _, _, hf.add hg⟩

lemma C1ex.const_mul {T : Set E} {μ : ℝ} {f : E → ℝ} (hf : C1ex T μ f) (a : ℝ) :
    C1ex T μ (fun y => a * f y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  exact ⟨_, _, _, _, hf.const_mul a⟩

lemma C1ex.sub {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) :
    C1ex T μ (fun y => f y - g y) := by
  have h := hf.add (hg.const_mul (-1))
  simpa [sub_eq_add_neg] using h

lemma C1ex.sum {T : Set E} {μ : ℝ} {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, C1ex T μ (f i)) : C1ex T μ (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C1ex_const T μ 0
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

lemma C1ex.mul {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) (hT : Convex ℝ T)
    {R : ℝ} (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    C1ex T μ (fun y => f y * g y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  obtain ⟨N0, N1, H', g1, hg⟩ := hg
  exact ⟨_, _, _, _, (hf.weaken (le_max_left M0 0) (le_max_left M1 0) le_rfl).mul
    (hg.weaken (le_max_left N0 0) (le_max_left N1 0) le_rfl) hT hR hR0 hμ0 hμ1 (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)⟩

lemma C1ex.inv {T : Set E} {μ : ℝ} {f : E → ℝ} (hf : C1ex T μ f) (hT : Convex ℝ T)
    {R : ℝ} (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {m : ℝ} (hm : 0 < m) (hfm : ∀ y ∈ T, m ≤ |f y|) : C1ex T μ (fun y => (f y)⁻¹) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  exact ⟨_, _, _, _, (hf.weaken (le_max_left M0 0) (le_max_left M1 0) le_rfl).inv hT hR hR0 hμ0 hμ1
    (le_max_right _ _) (le_max_right _ _) hm hfm⟩

lemma C1ex.div {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) (hT : Convex ℝ T)
    {R : ℝ} (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {m : ℝ} (hm : 0 < m) (hgm : ∀ y ∈ T, m ≤ |g y|) : C1ex T μ (fun y => f y / g y) := by
  have h := hf.mul (hg.inv hT hR hR0 hμ0 hμ1 hm hgm) hT hR hR0 hμ0 hμ1
  simpa [div_eq_mul_inv] using h

lemma C1ex.lip {T : Set E} {μ : ℝ} {f : E → ℝ} (hf : C1ex T μ f) (hT : Convex ℝ T) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ T, ∀ z ∈ T, |f y - f z| ≤ L * ‖y - z‖ := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  exact ⟨max M1 0, le_max_right _ _, fun y hy z hz =>
    (hf.lip hT hy hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-- `z ↦ Du z w` is `C^{1,μ}` from `C2B` data of `u`. -/
lemma C2B.apply_C1Hb {u : E → ℝ} {Du : E → E →L[ℝ] ℝ} {D2u : E → E →L[ℝ] E →L[ℝ] ℝ} {T : Set E}
    {μ K : ℝ} (hu : C2B T μ K u Du D2u) (hd : ∀ z ∈ T, HasFDerivAt Du (D2u z) z) (w : E) :
    C1Hb T μ (K * ‖w‖) (K * ‖w‖) (K * ‖w‖) (fun z => Du z w) (fun z => (D2u z).flip w) := by
  have key : ∀ A : E →L[ℝ] E →L[ℝ] ℝ, ‖A.flip w‖ ≤ ‖A‖ * ‖w‖ := fun A =>
    (A.flip.le_opNorm w).trans (by rw [ContinuousLinearMap.opNorm_flip])
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun y hy z hz => ?_,
    mul_nonneg hu.hK (norm_nonneg w)⟩
  · have h := (hd z hz).clm_apply (hasFDerivAt_const w z)
    exact h.congr_fderiv (by rw [ContinuousLinearMap.comp_zero, zero_add])
  · rw [← Real.norm_eq_abs]
    exact ((Du z).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hu.b1 z hz) (norm_nonneg w))
  · exact (key _).trans (mul_le_mul_of_nonneg_right (hu.b2 z hz) (norm_nonneg w))
  · have he : (D2u y).flip w - (D2u z).flip w = (D2u y - D2u z).flip w := by
      ext h'; simp
    rw [he]
    have h1 := mul_le_mul_of_nonneg_right (hu.hol2 y hy z hz) (norm_nonneg w)
    have h2 : K * ‖y - z‖ ^ μ * ‖w‖ = K * ‖w‖ * ‖y - z‖ ^ μ := by ring
    exact (key _).trans (h1.trans h2.le)

end Coef

section CoefEu

variable {n : ℕ}

end CoefEu

section ObCoef

lemma cball_diam {E : Type*} [NormedAddCommGroup E] {R : ℝ} :
    ∀ y ∈ Metric.closedBall (0 : E) R, ∀ z ∈ Metric.closedBall (0 : E) R, ‖y - z‖ ≤ 2 * R := by
  intro y hy z hz
  rw [mem_closedBall_zero_iff] at hy hz
  exact (norm_sub_le y z).trans (by linarith)

variable {n : ℕ}

/-- last entry of `DFlat Du (gr u z) (V z)`. -/
noncomputable def gN (Du : Eu n → Eu n →L[ℝ] ℝ) (V : Eu n → Eu (n + 1)) (z : Eu n) : ℝ :=
  V z (Fin.last n) - Du z (piL n (V z))

lemma Du_piL_expand (Du : Eu n → Eu n →L[ℝ] ℝ) (V : Eu n → Eu (n + 1)) (z : Eu n) :
    Du z (piL n (V z)) = ∑ i, Du z (EuclideanSpace.single i 1) * V z (Fin.castSucc i) := by
  conv_lhs => rw [eu_expand (piL n (V z))]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, piL_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma gN_C1ex {R μ K : ℝ} (hR : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {u : Eu n → ℝ}
    {Du : Eu n → Eu n →L[ℝ] ℝ} {D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ}
    (hu : C2B (Metric.closedBall 0 R) μ K u Du D2u)
    (hd : ∀ z ∈ Metric.closedBall (0 : Eu n) R, HasFDerivAt Du (D2u z) z)
    {V : Eu n → Eu (n + 1)} (hV : ∀ k, C1ex (Metric.closedBall 0 R) μ (fun z => V z k)) :
    C1ex (Metric.closedBall 0 R) μ (gN Du V) := by
  have he : gN Du V = fun z => V z (Fin.last n) -
      ∑ i, Du z (EuclideanSpace.single i 1) * V z (Fin.castSucc i) := by
    funext z; rw [gN, Du_piL_expand]
  rw [he]
  refine (hV _).sub (C1ex.sum _ fun i _ => ?_)
  have h1 : C1ex (Metric.closedBall (0 : Eu n) R) μ (fun z => Du z (EuclideanSpace.single i 1)) :=
    ⟨_, _, _, _, hu.apply_C1Hb hd _⟩
  exact h1.mul (hV _) (convex_closedBall 0 R) cball_diam (by linarith) hμ0 hμ1

theorem obl_coef {R μ K : ℝ} (hR : 0 < R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {u : Eu n → ℝ}
    {Du : Eu n → Eu n →L[ℝ] ℝ} {D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ}
    (hu : C2B (Metric.closedBall 0 R) μ K u Du D2u)
    (hd : ∀ z ∈ Metric.closedBall (0 : Eu n) R, HasFDerivAt Du (D2u z) z)
    {V : Eu n → Eu (n + 1)} (hV : ∀ k, C1ex (Metric.closedBall 0 R) μ (fun z => V z k))
    (h0 : gN Du V 0 ≠ 0) :
    ∃ R' > 0, R' ≤ R ∧
      (∀ z ∈ Metric.closedBall (0 : Eu n) R', |gN Du V 0| / 2 ≤ |gN Du V z| ∧ 0 < gN Du V z * gN Du V 0) ∧
      ∀ i : Fin n, C1ex (Metric.closedBall 0 R') μ
        (fun z => V z (Fin.castSucc i) / gN Du V z - V 0 (Fin.castSucc i) / gN Du V 0) := by
  have hg := gN_C1ex hR.le hμ0 hμ1 hu hd hV
  obtain ⟨L, hL0, hL⟩ := hg.lip (convex_closedBall 0 R)
  set a := |gN Du V 0| with ha
  have ha0 : 0 < a := abs_pos.mpr h0
  set R' := min R (a / (2 * (L + 1))) with hR'
  have hR'0 : 0 < R' := lt_min hR (by positivity)
  have hR'R : R' ≤ R := min_le_left _ _
  have hsub : Metric.closedBall (0 : Eu n) R' ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall hR'R
  have hlow : ∀ z ∈ Metric.closedBall (0 : Eu n) R', |gN Du V z - gN Du V 0| ≤ a / 2 := by
    intro z hz
    have h1 := hL z (hsub hz) 0 (Metric.mem_closedBall_self hR.le)
    rw [sub_zero] at h1
    have hz' : ‖z‖ ≤ a / (2 * (L + 1)) := (mem_closedBall_zero_iff.mp hz).trans (min_le_right _ _)
    have h2 : L * ‖z‖ ≤ (L + 1) * (a / (2 * (L + 1))) :=
      mul_le_mul (by linarith) hz' (norm_nonneg _) (by linarith)
    have h3 : (L + 1) * (a / (2 * (L + 1))) = a / 2 := by field_simp
    linarith
  have hbd : ∀ z ∈ Metric.closedBall (0 : Eu n) R', a / 2 ≤ |gN Du V z| ∧ 0 < gN Du V z * gN Du V 0 := by
    intro z hz
    have h1 := hlow z hz
    have h2 := abs_sub_abs_le_abs_sub (gN Du V 0) (gN Du V z)
    rw [abs_sub_comm] at h2
    refine ⟨by linarith, ?_⟩
    have h3 : |(gN Du V z - gN Du V 0) * gN Du V 0| ≤ a / 2 * a := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 ha0.le
    have h4 := neg_abs_le ((gN Du V z - gN Du V 0) * gN Du V 0)
    have h5 : gN Du V 0 * gN Du V 0 = a * a := by rw [ha, abs_mul_abs_self]
    have h6 : 0 < a * a := mul_pos ha0 ha0
    linarith
  refine ⟨R', hR'0, hR'R, hbd, fun i => ?_⟩
  have hT := convex_closedBall (0 : Eu n) R'
  exact (((hV _).mono hsub).div (hg.mono hsub) hT cball_diam (by linarith) hμ0 hμ1
    (by positivity : (0 : ℝ) < a / 2) (fun z hz => (hbd z hz).1)).sub (C1ex_const _ μ _)

/-- global `C^{1,μ}` lift of a `C^{1,μ}` function on a ball of `ℝ^n` along `piL`, exact on a smaller ball. -/
theorem glob_lift {μ R : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hR : 0 < R) {f : Eu n → ℝ}
    (hf : C1ex (Metric.closedBall 0 R) μ f) :
    ∃ (g : Eu (n + 1) → ℝ) (g1 : Eu (n + 1) → (Eu (n + 1) →L[ℝ] ℝ)) (N0 N1 H' : ℝ),
      (∀ ξ ∈ Metric.ball (0 : Eu (n + 1)) (R / 4), g ξ = f (piL n ξ)) ∧
      (∀ y, HasFDerivAt g (g1 y) y) ∧ Continuous g1 ∧ (∀ y, |g y| ≤ N0) ∧ (∀ y, ‖g1 y‖ ≤ N1) ∧
      (∀ y z, ‖g1 y - g1 z‖ ≤ H' * ‖y - z‖ ^ μ) ∧ 0 ≤ H' := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  have hf' := hf.weaken (le_refl M0) (le_max_left M1 0) le_rfl
  have hc := hf'.comp (S := Metric.closedBall (0 : Eu (n + 1)) R) (C2B_clm (piL n) norm_piL_le)
    (fun y _ => (piL n).hasFDerivAt)
    (fun y hy => by rw [mem_closedBall_zero_iff] at hy ⊢; exact (norm_piL_apply_le y).trans hy)
    cball_diam (by linarith) hμ0.le hμ1 (le_max_right _ _)
  obtain ⟨g, g1, N0, N1, H', hagree, hrest⟩ := cutoff_C1H hμ0 hμ1 (c := 0) hR
    (fun y hy => hc.hd y (Metric.ball_subset_closedBall hy))
    (fun y hy => hc.b0 y (Metric.ball_subset_closedBall hy))
    (fun y hy => hc.b1 y (Metric.ball_subset_closedBall hy))
    (fun y hy z hz => hc.hol y (Metric.ball_subset_closedBall hy) z (Metric.ball_subset_closedBall hz)) hc.hH
  exact ⟨g, g1, N0, N1, H', fun ξ hξ => (hagree ξ hξ).1, hrest⟩

end ObCoef

section ObDir

variable {n : ℕ}

lemma DFlat_gr_apply (u : Eu n → ℝ) (Du : Eu n → Eu n →L[ℝ] ℝ) (z : Eu n) (V : Eu (n + 1)) :
    DFlat Du (gr u z) V = iL n (piL n V) + (V (Fin.last n) - Du z (piL n V)) • eL n := by
  rw [DFlat, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, DFl, sRL_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, piL_gr]
  rw [sub_smul, ← add_sub_assoc, ← decomp V]

lemma iL_piL_expand (V : Eu (n + 1)) :
    iL n (piL n V) = ∑ i, V (Fin.castSucc i) • iL n (EuclideanSpace.single i 1) := by
  conv_lhs => rw [eu_expand (piL n V)]
  rw [map_sum]
  simp only [map_smul, piL_apply]

/-- After the shear with `ψ_i = V_i/g - b_i` the field direction is `g • (eL + Σ b_i w_i)`. -/
theorem oblique_dir (u : Eu n → ℝ) (Du : Eu n → Eu n →L[ℝ] ℝ) (z : Eu n) (V : Eu (n + 1)) (b : Fin n → ℝ)
    (hg : V (Fin.last n) - Du z (piL n V) ≠ 0) :
    (ContinuousLinearMap.id ℝ (Eu (n + 1)) - (innerSL ℝ (eL n)).smulRight
      (∑ i, (V (Fin.castSucc i) / (V (Fin.last n) - Du z (piL n V)) - b i) •
        iL n (EuclideanSpace.single i 1)))
      (DFlat Du (gr u z) V) =
    (V (Fin.last n) - Du z (piL n V)) • (eL n + ∑ i, b i • iL n (EuclideanSpace.single i 1)) := by
  set g := V (Fin.last n) - Du z (piL n V) with hgdef
  have hD := DFlat_gr_apply u Du z V
  rw [← hgdef] at hD
  have hin : inner ℝ (eL n) (DFlat Du (gr u z) V) = g := by
    rw [hD, real_inner_comm, inner_eL]
    simp [iL_last, eL_last]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, hin, hD, iL_piL_expand, Finset.smul_sum, smul_add, Finset.smul_sum]
  have hi : ∀ i, g • ((V (Fin.castSucc i) / g - b i) • iL n (EuclideanSpace.single i 1)) =
      V (Fin.castSucc i) • iL n (EuclideanSpace.single i 1) - g • (b i • iL n (EuclideanSpace.single i 1)) := by
    intro i
    rw [smul_smul, smul_smul, ← sub_smul]
    congr 1
    field_simp
  simp only [hi, Finset.sum_sub_distrib]
  abel

end ObDir

section ChartV

variable {n : ℕ}

end ChartV

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

section ObDef

/-- plain core of O8: chart data (C2B graph function, C^{1,μ} transported field, side description) ⇒ `ObChart`. -/
def ObCore (n : ℕ) (μ : ℝ) : Prop :=
  ∀ (Ω : Set (Eu (n + 1))), IsOpen Ω → ∀ (x0 : Eu (n + 1)) (U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1))
    (u : Eu n → ℝ) (Du : Eu n → Eu n →L[ℝ] ℝ) (D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    C2B (Metric.closedBall 0 R) μ K u Du D2u →
    (∀ z ∈ Metric.closedBall (0 : Eu n) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : Eu (n + 1) → Eu (n + 1)),
    (∀ k, C1ex (Metric.closedBall 0 R) μ (fun z => U (c (x0 + U.symm (gr u z))) k)) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) (eL n)) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) (eL n) = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K' : ℝ) (e b : Eu (n + 1)) (Θ : Eu (n + 1) → Eu (n + 1)) (DΘ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1))
      (D2Θ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1) →L[ℝ] Eu (n + 1)), ObChart Ω μ c x0 r0 K' e b Θ DΘ D2Θ

end ObDef

section ObCore

lemma C2B_aff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : Set E} {μ K : ℝ} (L : E →L[ℝ] F) (x0 : E) (hL : ‖L‖ ≤ K) :
    C2B T μ K (fun x => L (x - x0)) (fun _ => L) (fun _ => 0) := by
  have h := C2B_clm (T := T) (μ := μ) L hL
  refine ⟨h.hK, fun x _ y _ => ?_, h.b1, h.lip1, h.b2, h.hol2⟩
  rw [← map_sub, sub_sub_sub_cancel_right]
  exact (L.le_opNorm _).trans (by gcongr)

lemma smulRight_sigma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (σ : ℝ)
    (hσ : σ * σ = 1) (e : E) (a : Fin m → ℝ) (w : Fin m → E) (γ : E) :
    ((innerSL ℝ (σ • e)).smulRight (∑ i, (σ * a i) • w i)) γ =
      ((innerSL ℝ e).smulRight (∑ i, a i • w i)) γ := by
  have hs : (∑ i, (σ * a i) • w i) = σ • ∑ i, a i • w i := by
    rw [Finset.smul_sum]; simp_rw [mul_smul]
  rw [hs]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℝ e γ) * hσ

variable {n : ℕ}

lemma C2B.strict_ball {u : Eu n → ℝ} {Du : Eu n → Eu n →L[ℝ] ℝ} {D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ}
    {R μ K : ℝ} (hu : C2B (Metric.closedBall 0 R) μ K u Du D2u)
    (hd : ∀ z ∈ Metric.closedBall (0 : Eu n) R, HasFDerivAt u (Du z) z)
    {z : Eu n} (hz : z ∈ Metric.ball 0 R) : HasStrictFDerivAt u (Du z) z := by
  have hnhds : Metric.closedBall (0 : Eu n) R ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Filter.mem_of_superset hnhds fun y hy => hd y hy) ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hK := hu.hK
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
  refine ⟨min δ (ε / (K + 1)), lt_min hδ (by positivity), fun y hy => ?_⟩
  have hy1 : y ∈ Metric.closedBall (0 : Eu n) R :=
    Metric.ball_subset_closedBall (hδb (Metric.mem_ball.mpr (hy.trans_le (min_le_left _ _))))
  have hy2 : ‖y - z‖ < ε / (K + 1) := by rw [← dist_eq_norm]; exact hy.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  have h1 := hu.lip1 y hy1 z (Metric.ball_subset_closedBall hz)
  have h3 : (K + 1) * (ε / (K + 1)) = ε := by field_simp
  have h4 : K * ‖y - z‖ ≤ (K + 1) * ‖y - z‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h5 : (K + 1) * ‖y - z‖ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hy2 (by linarith)
  linarith

lemma hasStrictFDerivAt_Fl {u : Eu n → ℝ} {Du : Eu n → Eu n →L[ℝ] ℝ} {ξ : Eu (n + 1)}
    (hu : HasStrictFDerivAt u (Du (piL n ξ)) (piL n ξ)) : HasStrictFDerivAt (Fl u) (DFlat Du ξ) ξ := by
  have h1 : HasStrictFDerivAt (fun ξ => u (piL n ξ)) ((Du (piL n ξ)).comp (piL n)) ξ :=
    hu.comp ξ (piL n).hasStrictFDerivAt
  have h2 := (hasStrictFDerivAt_id ξ).sub (h1.smul_const (eL n))
  rw [DFlat, DFl, sRL_apply]
  exact h2

lemma norm_Fl_le {u : Eu n → ℝ} {K : ℝ} {ξ : Eu (n + 1)} (hK : |u (piL n ξ)| ≤ K * ‖piL n ξ‖) (hK0 : 0 ≤ K) :
    ‖Fl u ξ‖ ≤ (1 + K) * ‖ξ‖ := by
  have h1 : ‖Fl u ξ‖ ≤ ‖ξ‖ + |u (piL n ξ)| := by
    rw [Fl]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_eL, mul_one, Real.norm_eq_abs]
  have h2 := hK.trans (mul_le_mul_of_nonneg_left (norm_piL_apply_le ξ) hK0)
  linarith

lemma Fl_of_inner_zero {u : Eu n → ℝ} {ξ : Eu (n + 1)} (h : inner ℝ (Fl u ξ) (eL n) = 0) :
    Fl u ξ = iL n (piL n ξ) ∧ ξ = gr u (piL n ξ) := by
  rw [inner_Fl] at h
  have h' : ξ (Fin.last n) = u (piL n ξ) := by linarith
  constructor
  · rw [Fl, ← h']
    exact sub_eq_iff_eq_add.mpr (decomp ξ)
  · rw [gr_eq, ← h']
    exact decomp ξ

/-- the shear package (statement of `shear` with `hP` discharged). -/
def ShearPkg (d : ℕ) (μ : ℝ) : Prop :=
  ∀ {m : ℕ} (w : Fin m → Eu d) (e : Eu d) (he : ‖e‖ = 1)
      (M0 M1 H : Fin m → ℝ) (ψ : Fin m → Eu d → ℝ) (ψ1 : Fin m → Eu d → (Eu d →L[ℝ] ℝ))
      (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
      (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
      (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : Eu d → Eu d) (DG : Eu d → (Eu d →L[ℝ] Eu d)) (D2G : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d)),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (Eu d) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : Eu d) (r : ℝ), 0 ≤ r → ∃ K, C2B {x : Eu d | 0 ≤ inner ℝ x e ∧ dist x c ≤ r} μ K Gm DG D2G)

variable {n : ℕ} in

theorem shearpkg_of_plain {n : ℕ} {μ : ℝ} (h : ∀ {m : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin (n + 1))) (e : EuclideanSpace ℝ (Fin (n + 1))) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (DG : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) (D2G : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 ≤ r → ∃ K, let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ inner ℝ x e ∧ dist x c ≤ r}
        0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Gm x - Gm y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DG x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖DG x - DG y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2G x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖D2G x - D2G y‖ ≤ K * ‖x - y‖ ^ μ))) : ShearPkg (n + 1) μ := by
  intro m w e he M0 M1 H ψ ψ1 hd hc hb0 hb1 hhol hH
  obtain ⟨Gm, DG, D2G, h1, h2, h3, h4, h5, h6⟩ := h w e he M0 M1 H ψ ψ1 hd hc hb0 hb1 hhol hH
  refine ⟨Gm, DG, D2G, h1, h2, h3, h4, h5, fun c r hr => ?_⟩
  obtain ⟨K, a1, a2, a3, a4, a5, a6⟩ := h6 c r hr
  exact ⟨K, a1, a2, a3, a4, a5, a6⟩

theorem ob_chart_core {μ : ℝ} (hS : ShearPkg (n + 1) μ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) : ObCore n μ := by
  intro Ω hΩ x0 U u Du D2u R K hR hu hd hu0 hDu0 c hV s r1 hs hr1 hside hobl
  have hK0 := hu.hK
  set V : Eu n → Eu (n + 1) := fun z => U (c (x0 + U.symm (gr u z))) with hVdef
  have hgr0 : gr u 0 = 0 := by rw [gr_eq, hu0, map_zero, zero_smul, add_zero]
  have hV0 : V 0 = U (c x0) := by simp only [hVdef, hgr0, map_zero, add_zero]
  have hg0 : gN Du V 0 = U (c x0) (Fin.last n) := by
    rw [gN, hDu0, ContinuousLinearMap.zero_apply, sub_zero, hV0]
  have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hg0ne : gN Du V 0 ≠ 0 := by
    rw [hg0]; intro h; rw [h, mul_zero] at hobl; exact lt_irrefl 0 hobl
  obtain ⟨R', hR'0, hR'R, hbd, hâ⟩ :=
    obl_coef (V := V) hR hμ0.le hμ1 hu (fun z hz => (hd z hz).2) hV hg0ne
  set σ : ℝ := -s with hσdef
  have hσ2 : σ * σ = 1 := by rw [hσdef, neg_mul_neg, hs2]
  set β : Fin n → ℝ := fun i => V 0 (Fin.castSucc i) / gN Du V 0 with hβ
  have hψex : ∀ i : Fin n, ∃ (g : Eu (n + 1) → ℝ) (g1 : Eu (n + 1) → (Eu (n + 1) →L[ℝ] ℝ)) (N0 N1 H' : ℝ),
      (∀ ξ ∈ Metric.ball (0 : Eu (n + 1)) (R' / 4),
        g ξ = σ * (V (piL n ξ) (Fin.castSucc i) / gN Du V (piL n ξ) - β i)) ∧
      (∀ y, HasFDerivAt g (g1 y) y) ∧ Continuous g1 ∧ (∀ y, |g y| ≤ N0) ∧ (∀ y, ‖g1 y‖ ≤ N1) ∧
      (∀ y z, ‖g1 y - g1 z‖ ≤ H' * ‖y - z‖ ^ μ) ∧ 0 ≤ H' := fun i =>
    glob_lift hμ0 hμ1 hR'0 ((hâ i).const_mul σ)
  choose ψ ψ1 N0 N1 Hs hψag hψd hψc hψb0 hψb1 hψhol hψH using hψex
  have hesh : ‖σ • eL n‖ = 1 := by
    rw [norm_smul, norm_eL, mul_one, Real.norm_eq_abs, hσdef, abs_neg]
    rcases hs with h | h <;> rw [h] <;> norm_num
  obtain ⟨Gm, DG, D2G, hGin, hGs, -, hGpl, hGd2, hGC⟩ :=
    hS (fun i => iL n (EuclideanSpace.single i 1)) (σ • eL n) hesh N0 N1 Hs ψ ψ1
      hψd hψc hψb0 hψb1 hψhol hψH
  have hwe : ∀ i, inner ℝ (iL n (EuclideanSpace.single i (1 : ℝ))) (σ • eL n) = 0 := fun i => by
    rw [real_inner_smul_right, inner_iL_eL, mul_zero]
  set r0 := min r1 (R' / 4) with hr0def
  have hr0 : 0 < r0 := lt_min hr1 (by positivity)
  have hr0r1 : r0 ≤ r1 := min_le_left _ _
  have hr0R' : r0 ≤ R' / 4 := min_le_right _ _
  have hr0R : r0 < R := by linarith
  set LU : Eu (n + 1) →L[ℝ] Eu (n + 1) := U.toLinearIsometry.toContinuousLinearMap with hLU
  set LUs : Eu (n + 1) →L[ℝ] Eu (n + 1) := U.symm.toLinearIsometry.toContinuousLinearMap with hLUs
  have hLUn : ‖LU‖ ≤ 1 := U.toLinearIsometry.norm_toContinuousLinearMap_le
  have hLUsn : ‖LUs‖ ≤ 1 := U.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  set A : Eu (n + 1) → Eu (n + 1) := fun x => LU (x - x0) with hA
  have hAn : ∀ x, ‖A x‖ = ‖x - x0‖ := fun x => U.norm_map _
  have hAball : ∀ x ∈ Metric.ball x0 r0, ‖A x‖ < r0 := fun x hx => by
    rw [hAn, ← dist_eq_norm]; exact hx
  have hpiball : ∀ x ∈ Metric.ball x0 r0, piL n (A x) ∈ Metric.ball (0 : Eu n) R := fun x hx => by
    rw [mem_ball_zero_iff]; exact ((norm_piL_apply_le _).trans_lt (hAball x hx)).trans hr0R
  have hAs : ∀ x, HasStrictFDerivAt A LU x := fun x =>
    (LU.hasStrictFDerivAt.comp x ((hasStrictFDerivAt_id x).sub_const x0)).congr_fderiv LU.comp_id
  have hF1s : ∀ x ∈ Metric.ball x0 r0,
      HasStrictFDerivAt (fun y => Fl u (A y)) ((DFlat Du (A x)).comp LU) x := fun x hx =>
    (hasStrictFDerivAt_Fl (hu.strict_ball (fun z hz => (hd z hz).1) (hpiball x hx))).comp x (hAs x)
  -- C2B chain
  set T0 := Metric.ball x0 r0 ∩ closure Ω with hT0
  have hT0b : ∀ x ∈ T0, ‖x - x0‖ < r0 := fun x hx => by rw [← dist_eq_norm]; exact hx.1
  have hdiam : ∀ x ∈ T0, ∀ y ∈ T0, ‖x - y‖ ≤ 2 * r0 := fun x hx y hy => by
    have h := norm_sub_le (x - x0) (y - x0)
    rw [sub_sub_sub_cancel_right] at h
    linarith [hT0b x hx, hT0b y hy]
  have hAC : C2B T0 μ 1 A (fun _ => LU) (fun _ => 0) := C2B_aff LU x0 hLUn
  obtain ⟨K1, hFlC⟩ := Fl_C2B hu hμ0 hμ1
  obtain ⟨K2, hF1C⟩ := hFlC.comp hAC (fun x hx => by
    rw [mem_closedBall_zero_iff]; exact (hAball x hx.1).le.trans hr0R.le) hdiam hμ0 hμ1
  have hFsign : ∀ x ∈ T0, 0 ≤ σ * inner ℝ (Fl u (A x)) (eL n) := by
    intro x hx
    have hs' := hside x (Metric.ball_subset_ball hr0r1 hx.1)
    by_cases hxΩ : x ∈ Ω
    · exact (hs'.1.mp hxΩ).le
    · have hxf : x ∈ frontier Ω := ⟨hx.2, by rw [hΩ.interior_eq]; exact hxΩ⟩
      have h0 : inner ℝ (Fl u (A x)) (eL n) = 0 := hs'.2.mp hxf
      rw [h0, mul_zero]
  have hFbd : ∀ x ∈ T0, ‖Fl u (A x)‖ ≤ (1 + K) * r0 := by
    intro x hx
    have hpi : piL n (A x) ∈ Metric.closedBall (0 : Eu n) R :=
      Metric.ball_subset_closedBall (hpiball x hx.1)
    have hl := hu.lip _ hpi 0 (Metric.mem_closedBall_self hR.le)
    rw [hu0, sub_zero, sub_zero, Real.norm_eq_abs] at hl
    exact (norm_Fl_le hl hK0).trans (mul_le_mul_of_nonneg_left (hAball x hx.1).le (by linarith))
  obtain ⟨K3, hGC'⟩ := hGC 0 ((1 + K) * r0) (by positivity)
  obtain ⟨K4, hF2C⟩ := hGC'.comp hF1C (fun x hx => ⟨by
      show 0 ≤ inner ℝ (Fl u (A x)) (σ • eL n)
      rw [real_inner_smul_right]; exact hFsign x hx, by
      show dist (Fl u (A x)) 0 ≤ (1 + K) * r0
      rw [dist_zero_right]; exact hFbd x hx⟩) hdiam hμ0 hμ1
  have hUsC : C2B (Set.univ : Set (Eu (n + 1))) μ 1 LUs (fun _ => LUs) (fun _ => 0) := C2B_clm LUs hLUsn
  obtain ⟨K5, hΘC⟩ := hUsC.comp hF2C (fun _ _ => Set.mem_univ _) hdiam hμ0 hμ1
  -- basic values at x0
  have hA0 : A x0 = 0 := by simp only [hA, sub_self, map_zero]
  have hFl0 : Fl u 0 = 0 := by rw [Fl, map_zero, hu0, zero_smul, sub_zero]
  have hG0 : Gm 0 = 0 := (hGpl 0 (inner_zero_left _)).1
  have hψ0 : ∀ i, ψ i 0 = 0 := fun i => by
    rw [hψag i 0 (Metric.mem_ball_self (by positivity)), map_zero]
    simp [hβ]
  refine ⟨r0, K5, U.symm (σ • eL n), U.symm (-σ • ∑ i, β i • iL n (EuclideanSpace.single i 1)), _, _, _,
    ObChart.mk hr0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hΘC⟩
  · rw [LinearIsometryEquiv.norm_map]; exact hesh
  · rw [LinearIsometryEquiv.inner_map_map, real_inner_smul_left, real_inner_smul_right, sum_inner]
    simp [real_inner_smul_left, inner_iL_eL]
  · intro x hx
    exact LUs.hasStrictFDerivAt.comp x ((hGs _).comp x (hF1s x hx))
  · intro x hx
    have hpos : 0 < inner ℝ (Fl u (A x)) (σ • eL n) := by
      rw [real_inner_smul_right]; exact (hside x (Metric.ball_subset_ball hr0r1 hx.1)).1.mp hx.2
    have hDF1 : HasFDerivAt (fun y => (DFlat Du (A y)).comp LU)
        (D2comp (DFlat Du (A x)) (D2Flat Du D2u (A x)) LU 0) x :=
      hasFDerivAt_Dcomp (f := A) (Df := fun _ => LU) (hAs x).hasFDerivAt (hasFDerivAt_const LU x)
        (hasFDerivAt_DFlat (hd _ (Metric.ball_subset_closedBall (hpiball x hx.1))).2)
    have hDF2 := hasFDerivAt_Dcomp (f := fun y => Fl u (A y)) (hF1s x hx.1).hasFDerivAt hDF1 (hGd2 _ hpos)
    exact hasFDerivAt_Dcomp (f := fun y => Gm (Fl u (A y))) (Dg := fun _ => LUs)
      ((hGs _).comp x (hF1s x hx.1)).hasFDerivAt hDF2 (hasFDerivAt_const LUs _)
  · show LUs (Gm (Fl u (A x0))) = 0
    rw [hA0, hFl0, hG0, map_zero]
  · have hDF0 : DFlat Du 0 = ContinuousLinearMap.id ℝ (Eu (n + 1)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [DFlat, DFl, sRL_apply, hDu0]
    have hDG0 : DG 0 = ContinuousLinearMap.id ℝ (Eu (n + 1)) := by
      rw [(hGpl 0 (inner_zero_left _)).2]
      refine ContinuousLinearMap.ext fun v => ?_
      simp [hψ0]
    refine ContinuousLinearMap.ext fun v => ?_
    show LUs ((DG (Fl u (A x0))) ((DFlat Du (A x0)) (LU v))) = v
    rw [hA0, hFl0, hDG0, hDF0]
    exact U.symm_apply_apply v
  · intro x hx
    have hin : inner ℝ (LUs (Gm (Fl u (A x)))) (U.symm (σ • eL n)) = σ * inner ℝ (Fl u (A x)) (eL n) := by
      show inner ℝ (U.symm (Gm (Fl u (A x)))) (U.symm (σ • eL n)) = _
      rw [LinearIsometryEquiv.inner_map_map, hGin _ _ hwe, real_inner_smul_right]
    have hs' := hside x (Metric.ball_subset_ball hr0r1 hx)
    show (x ∈ Ω ↔ 0 < inner ℝ (LUs (Gm (Fl u (A x)))) (U.symm (σ • eL n))) ∧
      (x ∈ frontier Ω ↔ inner ℝ (LUs (Gm (Fl u (A x)))) (U.symm (σ • eL n)) = 0)
    rw [hin]
    refine ⟨hs'.1, ?_⟩
    have h2 : x ∈ frontier Ω ↔ inner ℝ (Fl u (A x)) (eL n) = 0 := hs'.2
    rw [h2]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rw [h, zero_mul] at hσ2; exact absurd hσ2 zero_ne_one
      · exact h
  · rintro x ⟨hxb, hxf⟩
    have h0in : inner ℝ (Fl u (A x)) (eL n) = 0 := (hside x (Metric.ball_subset_ball hr0r1 hxb)).2.mp hxf
    obtain ⟨hFl, hgr⟩ := Fl_of_inner_zero h0in
    set z := piL n (A x) with hz
    have hzn : ‖z‖ < R' / 4 := (norm_piL_apply_le _).trans_lt ((hAball x hxb).trans_le hr0R')
    have hzR' : iL n z ∈ Metric.ball (0 : Eu (n + 1)) (R' / 4) := by
      rw [mem_ball_zero_iff, norm_iL_apply]; exact hzn
    have hz' : z ∈ Metric.closedBall (0 : Eu n) R' := by
      rw [mem_closedBall_zero_iff]; linarith
    have hVz : LU (c x) = V z := by
      show U (c x) = U (c (x0 + U.symm (gr u z)))
      rw [← hgr]
      show U (c x) = U (c (x0 + U.symm (U (x - x0))))
      rw [U.symm_apply_apply, add_sub_cancel]
    have hψz : ∀ i, ψ i (iL n z) = σ * (V z (Fin.castSucc i) / gN Du V z - β i) := fun i => by
      rw [hψag i _ hzR', piL_iL]
    have hgz : gN Du V z ≠ 0 := by
      intro h; have := (hbd z hz').2; rw [h, zero_mul] at this; exact lt_irrefl 0 this
    have key : (ContinuousLinearMap.id ℝ (Eu (n + 1)) - (innerSL ℝ (eL n)).smulRight
        (∑ i, (V z (Fin.castSucc i) / gN Du V z - β i) • iL n (EuclideanSpace.single i 1)))
        (DFlat Du (gr u z) (V z)) =
        gN Du V z • (eL n + ∑ i, β i • iL n (EuclideanSpace.single i 1)) :=
      oblique_dir u Du z (V z) β hgz
    have hCL : (innerSL ℝ (σ • eL n)).smulRight
        (∑ i, (σ * (V z (Fin.castSucc i) / gN Du V z - β i)) • iL n (EuclideanSpace.single i 1)) =
        (innerSL ℝ (eL n)).smulRight
        (∑ i, (V z (Fin.castSucc i) / gN Du V z - β i) • iL n (EuclideanSpace.single i 1)) :=
      ContinuousLinearMap.ext fun γ => smulRight_sigma σ hσ2 (eL n) _ _ γ
    have hDGz := (hGpl (iL n z) (by rw [real_inner_smul_right, inner_iL_eL, mul_zero])).2
    simp_rw [hψz] at hDGz
    rw [hCL] at hDGz
    show ∃ κ : ℝ, 0 < κ ∧ LUs ((DG (Fl u (A x))) ((DFlat Du (A x)) (LU (c x)))) =
      κ • (U.symm (-σ • ∑ i, β i • iL n (EuclideanSpace.single i 1)) - U.symm (σ • eL n))
    rw [hFl, hDGz, hVz, hgr, key]
    refine ⟨s * gN Du V z, ?_, ?_⟩
    · have e1 : (s * gN Du V z) * (s * gN Du V 0) = gN Du V z * gN Du V 0 := by
        linear_combination (gN Du V z * gN Du V 0) * hs2
      rw [← hg0] at hobl
      have h2 := (hbd z hz').2
      by_contra hneg
      push_neg at hneg
      linarith [mul_nonpos_of_nonpos_of_nonneg hneg hobl.le]
    · rw [← map_sub, ← map_smul]
      show U.symm _ = U.symm _
      congr 1
      rw [hσdef, neg_neg, neg_smul, sub_neg_eq_add]
      simp only [smul_add, smul_smul]
      rw [show s * gN Du V z * s = gN Du V z by linear_combination gN Du V z * hs2]
      abel

end ObCore

section Plain

theorem plain_of_obcore {n : ℕ} {μ : ℝ} (h : ObCore n μ) :
    let eL : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
    let gr : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun u z => WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))
    let Fl : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun u ξ => ξ - u (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) • eL
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsOpen Ω → ∀ (x0 : EuclideanSpace ℝ (Fin (n + 1))) (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (D2u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    (0 ≤ K ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖u x - u y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x - Du y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x - D2u y‖ ≤ K * ‖x - y‖ ^ μ)) →
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ k, ∃ (M0 M1 H : ℝ) (f1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt (fun z => U (c (x0 + U.symm (gr u z))) k) (f1 y) y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, |U (c (x0 + U.symm (gr u y))) k| ≤ M0) ∧ (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y‖ ≤ M1) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) eL) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) eL = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
        (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ) := by
  intro eL gr Fl Ω hΩ x0 U u Du D2u R K hR hu hd hu0 hDu0 c hV s r1 hs hr1 hside hpos
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  obtain ⟨r0, K', e, b, Θ, DΘ, D2Θ, hO⟩ := h Ω hΩ x0 U u Du D2u R K hR ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ hd hu0 hDu0 c
    (fun k => by
      obtain ⟨M0, M1, H, f1, h1, h2, h3, h4, h5⟩ := hV k
      exact ⟨M0, M1, H, f1, h1, h2, h3, h4, h5⟩) s r1 hs hr1 hside hpos
  obtain ⟨hr0, he, hb, hst, hd2, h0, hD0, hsd, hobl', hc2⟩ := hO
  obtain ⟨hK, hlip, hb1, hlip1, hb2, hhol2⟩ := hc2
  exact ⟨r0, K', e, b, Θ, DΘ, D2Θ, hr0, he, hb, hst, hd2, h0, hD0, hsd, hobl', hK, hlip, hb1, hlip1, hb2, hhol2⟩

end Plain

end ObliqueLib

theorem solution (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hS : ∀ {m : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin (n + 1))) (e : EuclideanSpace ℝ (Fin (n + 1))) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (DG : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) (D2G : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 ≤ r → ∃ K, let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ inner ℝ x e ∧ dist x c ≤ r}
        0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Gm x - Gm y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DG x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖DG x - DG y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2G x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖D2G x - D2G y‖ ≤ K * ‖x - y‖ ^ μ))) :
    let eL : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
    let gr : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun u z => WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))
    let Fl : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun u ξ => ξ - u (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) • eL
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsOpen Ω → ∀ (x0 : EuclideanSpace ℝ (Fin (n + 1))) (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (D2u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    (0 ≤ K ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖u x - u y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x - Du y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x - D2u y‖ ≤ K * ‖x - y‖ ^ μ)) →
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ k, ∃ (M0 M1 H : ℝ) (f1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt (fun z => U (c (x0 + U.symm (gr u z))) k) (f1 y) y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, |U (c (x0 + U.symm (gr u y))) k| ≤ M0) ∧ (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y‖ ≤ M1) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) eL) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) eL = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
        (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ) := by
  exact ObliqueLib.plain_of_obcore (ObliqueLib.ob_chart_core (ObliqueLib.shearpkg_of_plain hS) hμ0 hμ1.le)
