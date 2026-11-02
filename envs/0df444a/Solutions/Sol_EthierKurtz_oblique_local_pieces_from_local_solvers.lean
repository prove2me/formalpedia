-- Prove2me | solution 1 for EthierKurtz.oblique_local_pieces_from_local_solvers
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:26:38.750784+00:00
-- url     : https://prove2.me/submissions/b7b6ff5e-5905-4b96-a490-975268b033f9

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

noncomputable local instance instL2NO (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SO (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section Series

variable {d : ℕ}

/-- `f` is bounded by `M` and `μ`-Hölder with constant `H` on `X`. -/
def HB (X : Set (Eu d)) (μ M H : ℝ) (f : Eu d → ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ X, |f x| ≤ M) ∧ ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ H * ‖x - y‖ ^ μ

end Series

section ZextS

variable {d : ℕ}

end ZextS

section ProdS

variable {d : ℕ}

end ProdS

section PatchS

variable {d : ℕ}

end PatchS

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
    · have := mul_nonneg (mul_nonneg hi e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg e1 hN
      linarith [mul_le_mul_of_nonneg_right hC this]
  · obtain ⟨b0, b1, b2⟩ := h5 x ⟨hs hx.1, hx.2⟩ x' ⟨hs hx'.1, hx'.2⟩
    have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg hN hp
      linarith [mul_le_mul_of_nonneg_right hC this]

end LocDefS

section CanonS

variable {d : ℕ}

end CanonS

section GlobalS

variable {d : ℕ}

end GlobalS

section NormA

variable {d : ℕ}

end NormA

section VarA

variable {d : ℕ}

end VarA

section PullA

variable {d : ℕ}

end PullA

section CoefA

variable {d : ℕ}

end CoefA

section LocalSolveA

variable {d : ℕ}

end LocalSolveA

section InteriorA

variable {d : ℕ}

end InteriorA

section PieceA

variable {d : ℕ}

def LocSolA (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (a : Eu d → Matrix (Fin d) (Fin d) ℝ) (bb : Eu d → Eu d)
    (x0 : Eu d) (ρ lam0 C : ℝ) : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam →
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)

theorem LocSolA.mono {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {a : Eu d → Matrix (Fin d) (Fin d) ℝ}
    {bb : Eu d → Eu d} {x0 : Eu d} {ρ lam0 C ρ' lam0' C' : ℝ}
    (h : LocSolA Ω μ c a bb x0 ρ lam0 C) (hρ : ρ' ≤ ρ) (hl0 : 0 < lam0) (hl : lam0 ≤ lam0') (hC : C ≤ C') :
    LocSolA Ω μ c a bb x0 ρ' lam0' C' := by
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
    · have := mul_nonneg (mul_nonneg hi e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg e1 hN
      linarith [mul_le_mul_of_nonneg_right hC this]
  · obtain ⟨b0, b1, b2⟩ := h5 x ⟨hs hx.1, hx.2⟩ x' ⟨hs hx'.1, hx'.2⟩
    have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg hN hp
      linarith [mul_le_mul_of_nonneg_right hC this]

theorem ObChart.shrink {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (h : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) {r : ℝ} (hr : 0 < r) (hrr : r ≤ r0) :
    ObChart Ω μ c x0 r K e b Θ DΘ D2Θ where
  hr0 := hr
  he := h.he
  hb := h.hb
  strict x hx := h.strict x (Metric.ball_subset_ball hrr hx)
  hd2 x hx := h.hd2 x ⟨Metric.ball_subset_ball hrr hx.1, hx.2⟩
  h0 := h.h0
  hD0 := h.hD0
  side x hx := h.side x (Metric.ball_subset_ball hrr hx)
  obl x hx := h.obl x ⟨Metric.ball_subset_ball hrr hx.1, hx.2⟩
  c2b := h.c2b.sub' (fun x hx => ⟨Metric.ball_subset_ball hrr hx.1, hx.2⟩)

end PieceA

section ProdA

variable {d : ℕ}

end ProdA

section PatchA

variable {d : ℕ}

end PatchA

section LinA

variable {d : ℕ}

end LinA

section GlobalA

variable {d : ℕ}

end GlobalA

section GSolA

variable {d : ℕ}

lemma ab_restrict {Ω : Set (Eu d)} {μ : ℝ} {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d}
    {x0 : Eu d} {R Ka ρ : ℝ} (hρ : ρ ≤ R)
    (hab : ∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) :
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) := by
  have hs : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, x ∈ Metric.ball x0 R ∩ closure Ω :=
    fun x hx => ⟨Metric.ball_subset_ball hρ hx.1, hx.2⟩
  exact ⟨fun x hx => hab x (hs x hx), fun x hx x' hx' => hah x (hs x hx) x' (hs x' hx')⟩

theorem piece_existsA'' {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (c : Eu d → Eu d)
    (hd : 0 < d) {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d}
    (hbd : ∀ (x0 : Eu d) (r0 K : ℝ) (e b : Eu d) (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d)
      (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d), ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ → ∀ Ka : ℝ,
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) →
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) → (a x0).PosDef →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r0 ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ LocSolA Ω μ c a bb x0 ρ lam0 C)
    (hint : ∀ (x0 : Eu d) (R : ℝ), 0 < R → Metric.ball x0 R ⊆ Ω → ∀ Ka : ℝ,
      (∀ x ∈ Metric.ball x0 R, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) →
      (∀ x ∈ Metric.ball x0 R, ∀ x' ∈ Metric.ball x0 R,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) → (a x0).PosDef →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ LocSolA Ω μ c a bb x0 ρ lam0 C)
    (hA : ∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
      (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ))
    (hpd : ∀ x ∈ closure Ω, (a x).PosDef)
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : Eu d) (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d)
      (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d), ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) :
    ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ)
      (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (lam0 C Ka : ℝ),
      CutData Ω μ c x0 ρ Z τ χ χ1 χ2 ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧ LocSolA Ω μ c a bb x0 ρ lam0 C ∧ 0 ≤ Ka ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) := by
  intro x0 hx0
  obtain ⟨RA, Ka, hRA, hab, hah⟩ := hA x0 hx0
  have hKa : 0 ≤ Ka := (norm_nonneg _).trans (hab x0 ⟨Metric.mem_ball_self hRA, hx0⟩).2
  by_cases hxi : x0 ∈ Ω
  · obtain ⟨R0, hR0, hball0⟩ := Metric.isOpen_iff.mp hΩ x0 hxi
    have hR : 0 < min R0 RA := lt_min hR0 hRA
    have hball : Metric.ball x0 (min R0 RA) ⊆ Ω :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hball0
    have hin : ∀ x ∈ Metric.ball x0 (min R0 RA), x ∈ Metric.ball x0 RA ∩ closure Ω := fun x hx =>
      ⟨Metric.ball_subset_ball (min_le_right _ _) hx, subset_closure (hball hx)⟩
    obtain ⟨ρ, hρ, hρR, lam0, C, hl, hC, hsol⟩ := hint x0 (min R0 RA) hR hball Ka
      (fun x hx => hab x (hin x hx)) (fun x hx x' hx' => hah x (hin x hx) x' (hin x' hx')) (hpd x0 hx0)
    obtain ⟨Z, τ, χ, χ1, χ2, hcut⟩ := cut_interior (c := c) hΩ hd hball hμ0 hμ1.le ρ hρ hρR
    have hs : LocSolA Ω μ c a bb x0 ρ lam0 C := hsol
    obtain ⟨hab', hah'⟩ := ab_restrict (hρR.trans (min_le_right _ _)) hab hah
    exact ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, Ka, hcut, hl, hC, hs, hKa, hab', hah'⟩
  · have hfr : x0 ∈ frontier Ω := ⟨hx0, by rwa [hΩ.interior_eq]⟩
    obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, hc0⟩ := hch x0 hfr
    have hc' := hc0.shrink (lt_min hc0.hr0 hRA) (min_le_left _ _)
    have hin : ∀ x ∈ Metric.ball x0 (min r0 RA) ∩ closure Ω, x ∈ Metric.ball x0 RA ∩ closure Ω := fun x hx =>
      ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    obtain ⟨ρ, hρ, hρR, lam0, C, hl, hC, hsol⟩ := hbd x0 _ K e b Θ DΘ D2Θ hc' Ka
      (fun x hx => hab x (hin x hx)) (fun x hx x' hx' => hah x (hin x hx) x' (hin x' hx')) (hpd x0 hx0)
    obtain ⟨r1, hr1, -, hcutf⟩ := cut_boundary hc' hμ0 hμ1.le
    obtain ⟨Z, τ, χ, χ1, χ2, hcut⟩ := hcutf (min ρ r1) (lt_min hρ hr1) (min_le_right _ _)
    have hs : LocSolA Ω μ c a bb x0 ρ lam0 C := hsol
    obtain ⟨hab', hah'⟩ := ab_restrict (((min_le_left _ _).trans hρR).trans (min_le_right _ _)) hab hah
    exact ⟨min ρ r1, Z, τ, χ, χ1, χ2, lam0, C, Ka, hcut, hl, hC,
      hs.mono (min_le_left _ _) (by linarith) le_rfl le_rfl, hKa, hab', hah'⟩

/-- Global solvability of the oblique problem for `lam u - ½ a:D²u - Du·bb = g` with Hölder estimates. -/
def GSolA (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (a : Eu d → Matrix (Fin d) (Fin d) ℝ)
    (bb : Eu d → Eu d) : Prop :=
  ∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : Eu d → ℝ) (M H : ℝ), HB (closure Ω) μ M H g →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
      (∀ x ∈ closure Ω, lam * u x -
        (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - u1 x (bb x) = g x) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
        ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)

end GSolA

end ObliqueLib

theorem solution (d : ℕ) (hd : 0 < d) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hbd : ∀ (x0 : EuclideanSpace ℝ (Fin d)) (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d)) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
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
            ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) → ∀ Ka : ℝ,
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) →
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) →
      (a x0).PosDef →
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
          ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)))
    (hint : ∀ (x0 : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → Metric.ball x0 R ⊆ Ω → ∀ Ka : ℝ,
      (∀ x ∈ Metric.ball x0 R, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) →
      (∀ x ∈ Metric.ball x0 R, ∀ x' ∈ Metric.ball x0 R,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) →
      (a x0).PosDef →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧
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
          ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)))
    (hA : (∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
          ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)))
    (hpd : ∀ x ∈ closure Ω, (a x).PosDef)
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) :
    ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (χ2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (lam0 C Ka : ℝ),
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) ∧ 0 ≤ Ka ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) := by
  have hbd' : ∀ (x0 : ObliqueLib.Eu d) (r0 K : ℝ) (e b : ObliqueLib.Eu d) (Θ : ObliqueLib.Eu d → ObliqueLib.Eu d)
      (DΘ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d)
      (D2Θ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d),
      ObliqueLib.ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ → ∀ Ka : ℝ,
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) →
      (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) → (a x0).PosDef →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r0 ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ObliqueLib.LocSolA Ω μ c a bb x0 ρ lam0 C := by
    intro x0 r0 K e b Θ DΘ D2Θ hc Ka hab hah hpd0
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩ := hc
    exact hbd x0 r0 K e b Θ DΘ D2Θ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ Ka hab hah hpd0
  have hch' : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : ObliqueLib.Eu d) (Θ : ObliqueLib.Eu d → ObliqueLib.Eu d)
      (DΘ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d)
      (D2Θ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d),
      ObliqueLib.ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ := by
    intro x0 hx0
    obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ :=
      hch x0 hx0
    exact ⟨r0, K, e, b, Θ, DΘ, D2Θ, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩⟩
  intro x0 hx0
  obtain ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, Ka, ⟨a1, a2, a3, a4, a5, a6, a7, ⟨k1, k2, k3, k4, k5, k6⟩⟩, hl, hC, hs, hKa, hab, hah⟩ :=
    ObliqueLib.piece_existsA'' hΩ hμ0 hμ1 c hd hbd' hint hA hpd hch' x0 hx0
  exact ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, Ka, ⟨a1, a2, a3, a4, a5, a6, a7, k1, k2, k3, k4, k5, k6⟩, hl, hC, hs, hKa, hab, hah⟩
