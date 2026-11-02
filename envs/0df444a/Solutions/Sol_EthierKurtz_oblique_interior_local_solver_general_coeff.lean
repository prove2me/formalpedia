-- Prove2me | solution 1 for EthierKurtz.oblique_interior_local_solver_general_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:08:44.050722+00:00
-- url     : https://prove2.me/submissions/b5cf7a99-891e-4ed3-b20a-f1eec6a42140

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

lemma coord_le (v : Eu n) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.inner_single_right, EuclideanSpace.norm_single, norm_one, mul_one] at h
  simpa using h

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

section ObChartS

end ObChartS

section VarDef

end VarDef

section Pull

variable {d : ℕ}

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

end VarA

section PullA

variable {d : ℕ}

end PullA

section CoefA

variable {d : ℕ}

end CoefA

section InteriorA

variable {d : ℕ}

lemma entry_le_sum2 (f : Fin d → Fin d → ℝ) (hf : ∀ i j, 0 ≤ f i j) (i j : Fin d) : f i j ≤ ∑ i, ∑ j, f i j :=
  (Finset.single_le_sum (fun j _ => hf i j) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, f i j) (fun i _ => Finset.sum_nonneg fun j _ => hf i j)
      (Finset.mem_univ i))

set_option maxHeartbeats 2000000 in
theorem interior_solverA {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : Eu d → Eu d) {x0 : Eu d} {R : ℝ} (hR : 0 < R) (hball : Metric.ball x0 R ⊆ Ω) (hd : 0 < d)
    (hV : VarModelA d μ) {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d} {Ka : ℝ}
    (hab : ∀ x ∈ Metric.ball x0 R, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 R, ∀ x' ∈ Metric.ball x0 R,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)
    (hpd : (a x0).PosDef) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
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
  set e : Eu d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by rw [he_def]; simp
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  obtain ⟨δ, hδ, hVδ⟩ := hV (a x0) hpd e 0 he (inner_zero_left _)
  have hx0 : x0 ∈ Metric.ball x0 R := Metric.mem_ball_self hR
  have hKa : 0 ≤ Ka := (norm_nonneg _).trans (hab x0 hx0).2
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set f : ℝ → ℝ := fun ρ => (d : ℝ) ^ 2 * ((1 / 2 : ℝ) * Ka * ρ ^ μ) with hf
  have hfc : ContinuousAt f 0 := by
    rw [hf]
    exact continuousAt_const.mul (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hμ0.le)))
  have hf0 : f 0 = 0 := by
    rw [hf]; simp [Real.zero_rpow hμ0.ne']
  have e1 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ρ := self_mem_nhdsWithin
  have e2 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ρ < R / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < R / 2))
  have e3 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f ρ < δ :=
    nhdsWithin_le_nhds (hfc.eventually (Iio_mem_nhds (by rw [hf0]; exact hδ)))
  obtain ⟨ρ, hρ, hρR, hρA'⟩ := (e1.and (e2.and e3)).exists
  set Mα : ℝ := (1 / 2 : ℝ) * Ka * ρ ^ μ with hMα
  have hρA : (d : ℝ) ^ 2 * Mα ≤ δ := hρA'.le
  set s0 : Eu d := x0 - ρ • e with hs0
  have hza : ∀ z : Eu d, z + s0 - x0 = z - ρ • e := fun z => by rw [hs0]; abel
  have hinB : ∀ z : Eu d, ‖z - ρ • e‖ ≤ ρ → z + s0 ∈ Metric.ball x0 R := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm, hza]; linarith
  have hcl : ∀ z : Eu d, ‖z - ρ • e‖ ≤ ρ → z + s0 ∈ closure Ω := fun z hz =>
    subset_closure (hball (hinB z hz))
  set T : Set (Eu d) := {z | 0 ≤ inner ℝ z e} with hT
  set q : ℝ := (2 / ρ) ^ μ with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  set Hα : ℝ := (1 / 2 : ℝ) * Ka with hHα
  have hMα0 : 0 ≤ Mα := by positivity
  have hHα0 : 0 ≤ Hα := by positivity
  have hcα : ∀ k l, (∀ z ∈ T, |cutR (ρ • e) ρ z * ((1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l))| ≤ Mα) ∧
      ∀ z ∈ T, ∀ z' ∈ T, |cutR (ρ • e) ρ z * ((1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l)) -
        cutR (ρ • e) ρ z' * ((1 / 2 : ℝ) * (a (z' + s0) k l - a x0 k l))| ≤
        (Hα + Mα * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by
    intro k l
    refine cut_hb (T := T) (c := ρ • e) (f := fun z => (1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l))
      hρ hμ0.le hμ1.le hMα0 hHα0 (fun z _ hzρ => ?_) (fun z _ hzρ z' _ hzρ' => ?_)
    · have h1 := (hah _ (hinB z hzρ) _ hx0).1
      have h2 := entry_le_sum2 (fun i j => |a (z + s0) i j - a x0 i j|) (fun _ _ => abs_nonneg _) k l
      rw [hza] at h1
      show |(1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l)| ≤ Mα
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc (1 / 2 : ℝ) * |a (z + s0) k l - a x0 k l| ≤ (1 / 2 : ℝ) * (Ka * ‖z - ρ • e‖ ^ μ) := by
            gcongr; exact h2.trans h1
        _ ≤ (1 / 2 : ℝ) * (Ka * ρ ^ μ) := by gcongr
        _ = Mα := by rw [hMα]; ring
    · have h1 := (hah _ (hinB z hzρ) _ (hinB z' hzρ')).1
      have h2 := entry_le_sum2 (fun i j => |a (z + s0) i j - a (z' + s0) i j|) (fun _ _ => abs_nonneg _) k l
      rw [add_sub_add_right_eq_sub] at h1
      show |(1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l) - (1 / 2 : ℝ) * (a (z' + s0) k l - a x0 k l)| ≤ _
      have e : (1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l) - (1 / 2 : ℝ) * (a (z' + s0) k l - a x0 k l) =
          (1 / 2 : ℝ) * (a (z + s0) k l - a (z' + s0) k l) := by ring
      rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hHα]
      calc (1 / 2 : ℝ) * |a (z + s0) k l - a (z' + s0) k l| ≤ (1 / 2 : ℝ) * (Ka * ‖z - z'‖ ^ μ) := by
            gcongr; exact h2.trans h1
        _ = _ := by ring
  have hcβ : ∀ k, (∀ z ∈ T, |cutR (ρ • e) ρ z * bb (z + s0) k| ≤ Ka) ∧
      ∀ z ∈ T, ∀ z' ∈ T, |cutR (ρ • e) ρ z * bb (z + s0) k - cutR (ρ • e) ρ z' * bb (z' + s0) k| ≤
        (Ka + Ka * (2 / ρ) ^ μ) * ‖z - z'‖ ^ μ := by
    intro k
    refine cut_hb (T := T) (c := ρ • e) (f := fun z => bb (z + s0) k) hρ hμ0.le hμ1.le hKa hKa
      (fun z _ hzρ => (coord_le _ _).trans (hab _ (hinB z hzρ)).2) (fun z _ hzρ z' _ hzρ' => ?_)
    have h1 := (hah _ (hinB z hzρ) _ (hinB z' hzρ')).2
    rw [add_sub_add_right_eq_sub] at h1
    have : bb (z + s0) k - bb (z' + s0) k = (bb (z + s0) - bb (z' + s0)) k := by simp
    show |bb (z + s0) k - bb (z' + s0) k| ≤ _
    rw [this]; exact (coord_le _ _).trans h1
  set Kt : ℝ := (d : ℝ) ^ 2 * (Hα + Mα * q) + d * Ka + d * (Ka + Ka * q) with hKt
  have hKt1 : 0 ≤ (d : ℝ) ^ 2 * (Hα + Mα * q) := by positivity
  have hKt2 : 0 ≤ (d : ℝ) * Ka := by positivity
  have hKt3 : 0 ≤ (d : ℝ) * (Ka + Ka * q) := by positivity
  have hKt0 : 0 ≤ Kt := by positivity
  obtain ⟨lam0, Cv, hlam0, hCv, hsol⟩ := hVδ Kt hKt0
  have hsum2 : ∀ (f : Fin d → Fin d → ℝ) (m : ℝ), (∀ i j, f i j ≤ m) → ∑ i, ∑ j, f i j ≤ (d : ℝ) ^ 2 * m := by
    intro f m hf
    calc ∑ i, ∑ j, f i j ≤ ∑ _i : Fin d, ∑ _j : Fin d, m :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf i j
      _ = (d : ℝ) ^ 2 * m := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hsum1 : ∀ (f : Fin d → ℝ) (m : ℝ), (∀ i, f i ≤ m) → ∑ i, f i ≤ (d : ℝ) * m := by
    intro f m hf
    calc ∑ i, f i ≤ ∑ _i : Fin d, m := Finset.sum_le_sum fun i _ => hf i
      _ = (d : ℝ) * m := by simp [Finset.sum_const, Finset.card_univ]
  have hA1 : ∀ x : Eu d, 0 ≤ inner ℝ x e →
      ∑ i, ∑ j, |cutR (ρ • e) ρ x * ((1 / 2 : ℝ) * (a (x + s0) i j - a x0 i j))| ≤ δ := fun x hx =>
    (hsum2 _ Mα fun i j => (hcα i j).1 x hx).trans hρA
  have hA2 : ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |cutR (ρ • e) ρ x * ((1 / 2 : ℝ) * (a (x + s0) i j - a x0 i j)) -
        cutR (ρ • e) ρ x' * ((1 / 2 : ℝ) * (a (x' + s0) i j - a x0 i j))| ≤ Kt * ‖x - x'‖ ^ μ := by
    intro x x' hx hx'
    refine (hsum2 _ _ fun i j => (hcα i j).2 x hx x' hx').trans ?_
    have h1 : (d : ℝ) ^ 2 * (Hα + Mα * q) ≤ Kt := by rw [hKt]; linarith
    calc (d : ℝ) ^ 2 * ((Hα + Mα * (2 / ρ) ^ μ) * ‖x - x'‖ ^ μ) =
        ((d : ℝ) ^ 2 * (Hα + Mα * q)) * ‖x - x'‖ ^ μ := by rw [hq]; ring
      _ ≤ Kt * ‖x - x'‖ ^ μ := by gcongr
  have hB1 : ∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, |cutR (ρ • e) ρ x * bb (x + s0) i| ≤ Kt := by
    intro x hx
    refine (hsum1 _ _ fun i => (hcβ i).1 x hx).trans ?_
    rw [hKt]; linarith
  have hB2 : ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |cutR (ρ • e) ρ x * bb (x + s0) i - cutR (ρ • e) ρ x' * bb (x' + s0) i| ≤ Kt * ‖x - x'‖ ^ μ := by
    intro x x' hx hx'
    refine (hsum1 _ _ fun i => (hcβ i).2 x hx x' hx').trans ?_
    have h1 : (d : ℝ) * (Ka + Ka * q) ≤ Kt := by rw [hKt]; linarith
    calc (d : ℝ) * ((Ka + Ka * (2 / ρ) ^ μ) * ‖x - x'‖ ^ μ) =
        ((d : ℝ) * (Ka + Ka * q)) * ‖x - x'‖ ^ μ := by rw [hq]; ring
      _ ≤ Kt * ‖x - x'‖ ^ μ := by gcongr
  refine ⟨ρ / 2, by positivity, by linarith, lam0, Cv * (2 + q), hlam0, by positivity,
    fun lam hlam g M H hM0 hH0 hgM hgH => ?_⟩
  have hgc := cut_hb (T := T) (c := ρ • e) hρ hμ0.le hμ1.le hM0 hH0
    (f := fun z => g (z + s0))
    (fun z _ hzρ => hgM _ (hcl z hzρ))
    (fun z _ hzρ z' _ hzρ' => by
      have h1 := hgH _ (hcl z hzρ) _ (hcl z' hzρ')
      rwa [add_sub_add_right_eq_sub] at h1)
  obtain ⟨v, v1, v2, hvd, hve, hvb, hvs, hvt⟩ :=
    hsol lam hlam (fun z k l => cutR (ρ • e) ρ z * ((1 / 2 : ℝ) * (a (z + s0) k l - a x0 k l)))
      (fun z k => cutR (ρ • e) ρ z * bb (z + s0) k) hA1 hA2 hB1 hB2
      (fun z => cutR (ρ • e) ρ z * g (z + s0)) M (H + M * (2 / ρ) ^ μ) hM0 (by positivity)
      hgc.1 (fun y z hy hz => hgc.2 y hy z hz)
  have hlam1 : 1 ≤ lam := hlam0.trans hlam
  have hlpos : 0 < lam := by linarith
  have hl0 : 0 ≤ 1 / lam := by positivity
  have hlm1 : 1 ≤ lam ^ (μ / 2) := Real.one_le_rpow hlam1 (by linarith)
  set Nt : ℝ := lam ^ (μ / 2) * M + (H + M * (2 / ρ) ^ μ) with hNt
  set N : ℝ := lam ^ (μ / 2) * M + H with hN
  have hlM : 0 ≤ lam ^ (μ / 2) * M := mul_nonneg (zero_le_one.trans hlm1) hM0
  have hNt0 : 0 ≤ Nt := by rw [hNt]; positivity
  have hNtN : Nt ≤ (2 + q) * N := by
    rw [hNt, hN, ← hq]
    have h1 : M ≤ lam ^ (μ / 2) * M := le_mul_of_one_le_left hM0 hlm1
    linarith [mul_le_mul_of_nonneg_left h1 hq0, mul_nonneg hq0 hH0]
  -- membership facts
  have hpos : ∀ x ∈ Metric.ball x0 (ρ / 2), 0 < inner ℝ (x - s0) e := by
    intro x hx
    have h1 : x - s0 = (x - x0) + ρ • e := by rw [hs0]; abel
    rw [h1, inner_add_left, inner_smul_left, hee]
    have h2 := abs_real_inner_le_norm (x - x0) e
    rw [he, mul_one] at h2
    have h3 := hx; rw [Metric.mem_ball, dist_eq_norm] at h3
    simp only [conj_trivial]
    linarith [neg_abs_le (inner ℝ (x - x0) e)]
  have hcut : ∀ x ∈ Metric.ball x0 (ρ / 2), cutR (ρ • e) ρ (x - s0) = 1 := by
    intro x hx
    refine cutR_eq_one hρ ?_
    have h1 : x - s0 - ρ • e = x - x0 := by rw [hs0]; abel
    rw [h1]; have h3 := hx; rw [Metric.mem_ball, dist_eq_norm] at h3; linarith
  have hsubΩ : ∀ x ∈ Metric.ball x0 (ρ / 2), x ∈ Ω := fun x hx =>
    hball (Metric.ball_subset_ball (by linarith) hx)
  have tm0 : ∀ x x' : Eu d, 0 ≤ ‖x - x'‖ ^ μ := fun x x' => Real.rpow_nonneg (norm_nonneg _) _
  have hdiff : ∀ x x' : Eu d, x - s0 - (x' - s0) = x - x' := fun x x' => sub_sub_sub_cancel_right x x' s0
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
  refine ⟨fun y => v (y - s0), fun y => v1 (y - s0), fun y => v2 (y - s0), fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨h1, h2⟩ := hvd (x - s0) (hpos x hx.1)
    have hs : HasFDerivAt (fun y : Eu d => y - s0) (ContinuousLinearMap.id ℝ (Eu d)) x :=
      (hasFDerivAt_id x).sub_const s0
    have k1 := h1.comp x hs
    have k2 := h2.comp x hs
    rw [ContinuousLinearMap.comp_id] at k1 k2
    exact ⟨k1, k2⟩
  · have h := hve (x - s0) (hpos x hx.1).le
    simp only [hcut x hx.1, one_mul, sub_add_cancel] at h
    have e1 : (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * v2 (x - s0) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        (1 / 2 : ℝ) * ∑ i, ∑ j, a x0 i j * v2 (x - s0) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, ∑ j, (1 / 2 : ℝ) * (a x i j - a x0 i j) *
          v2 (x - s0) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e2 : v1 (x - s0) (bb x) = ∑ i, bb x i * v1 (x - s0) (EuclideanSpace.single i 1) := lin_expand _ _
    beta_reduce
    rw [e1, e2]
    linarith
  · exfalso
    have h1 : x ∈ Ω := hsubΩ x hx.1
    exact hx.2.2 (by rw [hΩ.interior_eq]; exact h1)
  · obtain ⟨s0, s1, s2⟩ := hs (x - s0) (hpos x hx.1).le
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
  · obtain ⟨t0, t1, t2⟩ := ht (x - s0) (x' - s0) (hpos x hx.1).le (hpos x' hx'.1).le
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

end InteriorA

end ObliqueLib

theorem solution (d : ℕ) (hd : 0 < d) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
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
    (x0 : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0 < R) (hball : Metric.ball x0 R ⊆ Ω)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Ka : ℝ)
    (hab : ∀ x ∈ Metric.ball x0 R, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 R, ∀ x' ∈ Metric.ball x0 R,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)
    (hpd : (a x0).PosDef) :
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) := by
  exact ObliqueLib.interior_solverA hΩ hμ0 hμ1 c hR hball hd hV hab hah hpd
