-- Prove2me | solution 1 for EthierKurtz.oblique_global_solver_from_pieces
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T23:10:26.668332+00:00
-- url     : https://prove2.me/submissions/803a4466-c5e0-49ea-af84-96300067e6e2

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

/-! Prop-valued shortcut instances (local, scoped to this namespace; speed up typeclass search). -/
local instance instCSEu (d : ℕ) : CompleteSpace (Eu d) := inferInstance
local instance instCSL1 (d : ℕ) : CompleteSpace (Eu d →L[ℝ] ℝ) := inferInstance
local instance instCSL2 (d : ℕ) : CompleteSpace (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
local instance instT2L1 (d : ℕ) : T2Space (Eu d →L[ℝ] ℝ) := inferInstance
local instance instT2L2 (d : ℕ) : T2Space (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
local instance instCSmL1 (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] ℝ) := inferInstance
local instance instCSmL2 (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instNACGL1 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instNSL1 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instSNACGL1 (d : ℕ) : SeminormedAddCommGroup (Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instACGL1 (d : ℕ) : AddCommGroup (Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instModL1 (d : ℕ) : Module ℝ (Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instNACGL2 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instNSL2 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instSNACGL2 (d : ℕ) : SeminormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instACGL2 (d : ℕ) : AddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instModL2 (d : ℕ) : Module ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance
noncomputable local instance instNACGLE (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d) := inferInstance
noncomputable local instance instNSLE (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d) := inferInstance
noncomputable local instance instSNACGLE (d : ℕ) : SeminormedAddCommGroup (Eu d →L[ℝ] Eu d) := inferInstance
noncomputable local instance instACGLE (d : ℕ) : AddCommGroup (Eu d →L[ℝ] Eu d) := inferInstance
noncomputable local instance instModLE (d : ℕ) : Module ℝ (Eu d →L[ℝ] Eu d) := inferInstance

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

end CutDefS

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

section CoverS

variable {d : ℕ}

theorem finite_cover {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} (hcpt : IsCompact (closure Ω))
    (hpiece : ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ)
      (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (lam0 C : ℝ),
      CutData Ω μ c x0 ρ Z τ χ χ1 χ2 ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧ LocSol Ω μ c x0 ρ lam0 C) :
    ∃ (t : Finset (Eu d)) (ρ Z τ : Eu d → ℝ) (χ : Eu d → Eu d → ℝ) (χ1 : Eu d → Eu d → Eu d →L[ℝ] ℝ)
      (χ2 : Eu d → Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (lam0 C : ℝ),
      1 ≤ lam0 ∧ 0 ≤ C ∧ (∀ p ∈ t, p ∈ closure Ω) ∧
      (∀ p ∈ t, CutData Ω μ c p (ρ p) (Z p) (τ p) (χ p) (χ1 p) (χ2 p)) ∧
      (∀ p ∈ t, LocSol Ω μ c p (ρ p) lam0 C) ∧
      closure Ω ⊆ ⋃ p ∈ t, Metric.ball p (min (τ p) (ρ p)) := by
  have h' : ∀ x0 : Eu d, ∃ (ρ Z τ : ℝ) (χ : Eu d → ℝ) (χ1 : Eu d → Eu d →L[ℝ] ℝ)
      (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (lam0 C : ℝ), x0 ∈ closure Ω →
      (CutData Ω μ c x0 ρ Z τ χ χ1 χ2 ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧ LocSol Ω μ c x0 ρ lam0 C) := by
    intro x0
    by_cases hx : x0 ∈ closure Ω
    · obtain ⟨ρ, Z, τ, χ, χ1, χ2, l, C, h⟩ := hpiece x0 hx
      exact ⟨ρ, Z, τ, χ, χ1, χ2, l, C, fun _ => h⟩
    · exact ⟨0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, fun h => absurd h hx⟩
  choose ρ Z τ χ χ1 χ2 l C hP using h'
  obtain ⟨t, ht, hcov⟩ := hcpt.elim_nhds_subcover (fun p => Metric.ball p (min (τ p) (ρ p)))
    (fun p hp => Metric.ball_mem_nhds p (lt_min (hP p hp).1.hτ (hP p hp).1.hρ))
  have hl0 : ∀ q ∈ t, 0 ≤ l q := fun q hq => by linarith [(hP q (ht q hq)).2.1]
  have hC0 : ∀ q ∈ t, 0 ≤ C q := fun q hq => (hP q (ht q hq)).2.2.1
  refine ⟨t, ρ, Z, τ, χ, χ1, χ2, 1 + ∑ p ∈ t, l p, 1 + ∑ p ∈ t, C p, ?_, ?_, ht,
    fun p hp => (hP p (ht p hp)).1, fun p hp => ?_, hcov⟩
  · have : 0 ≤ ∑ p ∈ t, l p := Finset.sum_nonneg hl0
    linarith
  · have : 0 ≤ ∑ p ∈ t, C p := Finset.sum_nonneg hC0
    linarith
  · obtain ⟨_, hl, _, hs⟩ := hP p (ht p hp)
    have h1 := Finset.single_le_sum (f := l) hl0 hp
    have h2 := Finset.single_le_sum (f := C) hC0 hp
    exact hs.mono le_rfl (by linarith) (by linarith) (by linarith)

end CoverS

noncomputable local instance instL2NO (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SO (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section Series

variable {d : ℕ}

/-- `f` is bounded by `M` and `μ`-Hölder with constant `H` on `X`. -/
def HB (X : Set (Eu d)) (μ M H : ℝ) (f : Eu d → ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ X, |f x| ≤ M) ∧ ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ H * ‖x - y‖ ^ μ

lemma tsum_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {c q N : ℝ}
    (hc : 0 ≤ c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hN : 0 ≤ N) (hf : ∀ k, ‖f k‖ ≤ c * (q ^ k * N)) :
    Summable f ∧ ‖∑' k, f k‖ ≤ c * N / (1 - q) := by
  have hg : Summable (fun k : ℕ => c * (q ^ k * N)) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right N).mul_left c
  have hn : Summable (fun k => ‖f k‖) := hg.of_nonneg_of_le (fun k => norm_nonneg _) hf
  refine ⟨hn.of_norm, ?_⟩
  calc ‖∑' k, f k‖ ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, c * (q ^ k * N) := hn.tsum_le_tsum hf hg
    _ = c * N / (1 - q) := by
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]; ring

lemma tsum_telescope {f : ℕ → ℝ} (hf : Summable f) : ∑' k, (f k - f (k + 1)) = f 0 := by
  have h1 : Summable (fun k => f (k + 1)) := (summable_nat_add_iff 1).mpr hf
  rw [hf.tsum_sub h1, hf.tsum_eq_zero_add]; ring

theorem series_solve {X Xo Bd : Set (Eu d)} (hXo : IsOpen Xo) (hXoX : Xo ⊆ X) (hBd : Bd ⊆ X)
    {μ w q lam : ℝ} (hw : 0 < w) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (cf : Eu d → Eu d) (p1 : Eu d → (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ)
    (p2 : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ)
    (R0 : (Eu d → ℝ) → Eu d → ℝ) (R1 : (Eu d → ℝ) → Eu d → Eu d →L[ℝ] ℝ)
    (R2 : (Eu d → ℝ) → Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ)
    {c0 c1 c2 c3 c4 c5 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hR : ∀ (g : Eu d → ℝ) (M H : ℝ), HB X μ M H g →
      (∀ x ∈ Xo, HasFDerivAt (R0 g) (R1 g x) x ∧ HasFDerivAt (R1 g) (R2 g x) x) ∧
      (∀ x ∈ Bd, R1 g x (cf x) = 0) ∧
      (∀ x ∈ X, |R0 g x| ≤ c0 * (w * M + H) ∧ ‖R1 g x‖ ≤ c1 * (w * M + H) ∧
        ‖R2 g x‖ ≤ c2 * (w * M + H)) ∧
      (∀ x ∈ X, ∀ x' ∈ X, |R0 g x - R0 g x'| ≤ c3 * (w * M + H) * ‖x - x'‖ ^ μ ∧
        ‖R1 g x - R1 g x'‖ ≤ c4 * (w * M + H) * ‖x - x'‖ ^ μ ∧
        ‖R2 g x - R2 g x'‖ ≤ c5 * (w * M + H) * ‖x - x'‖ ^ μ) ∧
      ∃ M' H' : ℝ, HB X μ M' H'
          (fun x => g x - (lam * R0 g x - p1 x (R1 g x) - p2 x (R2 g x))) ∧
        w * M' + H' ≤ q * (w * M + H))
    {g : Eu d → ℝ} {M H : ℝ} (hg : HB X μ M H g) :
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Xo, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ Bd, u1 x (cf x) = 0) ∧
      (∀ x ∈ X, lam * u x - p1 x (u1 x) - p2 x (u2 x) = g x) ∧
      (∀ x ∈ X, |u x| ≤ c0 * (w * M + H) / (1 - q) ∧ ‖u1 x‖ ≤ c1 * (w * M + H) / (1 - q) ∧
        ‖u2 x‖ ≤ c2 * (w * M + H) / (1 - q)) ∧
      (∀ x ∈ X, ∀ x' ∈ X, |u x - u x'| ≤ c3 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q) ∧
        ‖u1 x - u1 x'‖ ≤ c4 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q) ∧
        ‖u2 x - u2 x'‖ ≤ c5 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q)) := by
  obtain ⟨gs, hgs0, hgs1⟩ : ∃ gs : ℕ → Eu d → ℝ, gs 0 = g ∧ ∀ k x, gs (k + 1) x =
      gs k x - (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) :=
    ⟨fun k => Nat.rec g (fun _ f x => f x - (lam * R0 f x - p1 x (R1 f x) - p2 x (R2 f x))) k,
      rfl, fun _ _ => rfl⟩
  have hN0p : 0 ≤ w * M + H := by have := hg.1; have := hg.2.1; positivity
  have claim : ∀ k : ℕ, ∃ Mk Hk : ℝ, HB X μ Mk Hk (gs k) ∧ w * Mk + Hk ≤ q ^ k * (w * M + H) := by
    intro k
    induction k with
    | zero => exact ⟨M, H, hgs0 ▸ hg, by simp⟩
    | succ k ih =>
      obtain ⟨Mk, Hk, hk, hkN⟩ := ih
      obtain ⟨M', H', h1, h2⟩ := (hR _ Mk Hk hk).2.2.2.2
      refine ⟨M', H', ?_, ?_⟩
      · have : gs (k + 1) = fun x =>
            gs k x - (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) := funext (hgs1 k)
        rw [this]; exact h1
      · calc w * M' + H' ≤ q * (w * Mk + Hk) := h2
          _ ≤ q * (q ^ k * (w * M + H)) := mul_le_mul_of_nonneg_left hkN hq0
          _ = q ^ (k + 1) * (w * M + H) := by ring
  choose Mk Hk hk hkN using claim
  have hRk := fun k => hR (gs k) (Mk k) (Hk k) (hk k)
  have hcN : ∀ {c : ℝ}, 0 ≤ c → ∀ k, c * (w * Mk k + Hk k) ≤ c * (q ^ k * (w * M + H)) :=
    fun hc k => mul_le_mul_of_nonneg_left (hkN k) hc
  have hcNt : ∀ {c t : ℝ}, 0 ≤ c → 0 ≤ t → ∀ k,
      c * (w * Mk k + Hk k) * t ≤ (c * t) * (q ^ k * (w * M + H)) := fun {c t} hc ht k => by
    calc c * (w * Mk k + Hk k) * t = (c * t) * (w * Mk k + Hk k) := by ring
      _ ≤ (c * t) * (q ^ k * (w * M + H)) := mul_le_mul_of_nonneg_left (hkN k) (mul_nonneg hc ht)
  have S0 : ∀ x ∈ X, Summable (fun k => R0 (gs k) x) ∧
      ‖∑' k, R0 (gs k) x‖ ≤ c0 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc0 hq0 hq1 hN0p fun k => by
      rw [Real.norm_eq_abs]; exact ((hRk k).2.2.1 x hx).1.trans (hcN hc0 k)
  have S1 : ∀ x ∈ X, Summable (fun k => R1 (gs k) x) ∧
      ‖∑' k, R1 (gs k) x‖ ≤ c1 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc1 hq0 hq1 hN0p fun k => ((hRk k).2.2.1 x hx).2.1.trans (hcN hc1 k)
  have S2 : ∀ x ∈ X, Summable (fun k => R2 (gs k) x) ∧
      ‖∑' k, R2 (gs k) x‖ ≤ c2 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc2 hq0 hq1 hN0p fun k => ((hRk k).2.2.1 x hx).2.2.trans (hcN hc2 k)
  have hgeo : ∀ {c : ℝ}, Summable (fun k : ℕ => c * (q ^ k * (w * M + H))) := fun {c} =>
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _).mul_left c
  refine ⟨fun x => ∑' k, R0 (gs k) x, fun x => ∑' k, R1 (gs k) x, fun x => ∑' k, R2 (gs k) x,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hXo x hx
    have hbX : Metric.ball x r ⊆ X := hball.trans hXoX
    have hpc : IsPreconnected (Metric.ball x r) := (convex_ball x r).isPreconnected
    have hx0 : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    exact ⟨hasFDerivAt_tsum_of_isPreconnected hgeo Metric.isOpen_ball hpc
        (fun k y hy => ((hRk k).1 y (hball hy)).1)
        (fun k y hy => ((hRk k).2.2.1 y (hbX hy)).2.1.trans (hcN hc1 k)) hx0 (S0 x (hXoX hx)).1 hx0,
      hasFDerivAt_tsum_of_isPreconnected hgeo Metric.isOpen_ball hpc
        (fun k y hy => ((hRk k).1 y (hball hy)).2)
        (fun k y hy => ((hRk k).2.2.1 y (hbX hy)).2.2.trans (hcN hc2 k)) hx0 (S1 x (hXoX hx)).1 hx0⟩
  · intro x hx
    have hm := (ContinuousLinearMap.apply ℝ ℝ (cf x)).map_tsum (S1 x (hBd hx)).1
    simp only [ContinuousLinearMap.apply_apply] at hm
    show (∑' k, R1 (gs k) x) (cf x) = 0
    have h0 : ∀ k, R1 (gs k) x (cf x) = 0 := fun k => (hRk k).2.1 x hx
    rw [hm]; simp only [h0, tsum_zero]
  · intro x hx
    have e1 := (S0 x hx).1
    have e2 := (S1 x hx).1
    have e3 := (S2 x hx).1
    have hs1 : Summable (fun k => p1 x (R1 (gs k) x)) := e2.mapL (p1 x)
    have hs2 : Summable (fun k => p2 x (R2 (gs k) x)) := e3.mapL (p2 x)
    have hgsum : Summable (fun k => gs k x) := (tsum_bound (c := 1 / w) (by positivity) hq0 hq1 hN0p
      fun k => by
        rw [Real.norm_eq_abs]
        refine ((hk k).2.2.1 x hx).trans ?_
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hw]
        have := (hk k).2.1; have := hkN k; linarith).1
    have hsplit : ∑' k, (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) =
        lam * ∑' k, R0 (gs k) x - ∑' k, p1 x (R1 (gs k) x) - ∑' k, p2 x (R2 (gs k) x) := by
      rw [((e1.mul_left lam).sub hs1).tsum_sub hs2, (e1.mul_left lam).tsum_sub hs1, tsum_mul_left]
    have htel : (fun k => lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) =
        fun k => gs k x - gs (k + 1) x := funext fun k => by rw [hgs1]; ring
    show lam * (∑' k, R0 (gs k) x) - p1 x (∑' k, R1 (gs k) x) - p2 x (∑' k, R2 (gs k) x) = g x
    rw [(p1 x).map_tsum e2, (p2 x).map_tsum e3, ← hsplit, htel, tsum_telescope hgsum, hgs0]
  · intro x hx
    exact ⟨by rw [← Real.norm_eq_abs]; exact (S0 x hx).2, (S1 x hx).2, (S2 x hx).2⟩
  · intro x hx x' hx'
    have ht : 0 ≤ ‖x - x'‖ ^ μ := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have hb := tsum_bound (f := fun k => R0 (gs k) x - R0 (gs k) x') (mul_nonneg hc3 ht) hq0 hq1
        hN0p fun k => by
          rw [Real.norm_eq_abs]; exact ((hRk k).2.2.2.1 x hx x' hx').1.trans (hcNt hc3 ht k)
      show |(∑' k, R0 (gs k) x) - ∑' k, R0 (gs k) x'| ≤ _
      rw [← (S0 x hx).1.tsum_sub (S0 x' hx').1, ← Real.norm_eq_abs]; exact hb.2
    · have hb := tsum_bound (f := fun k => R1 (gs k) x - R1 (gs k) x') (mul_nonneg hc4 ht) hq0 hq1
        hN0p fun k => ((hRk k).2.2.2.1 x hx x' hx').2.1.trans (hcNt hc4 ht k)
      show ‖(∑' k, R1 (gs k) x) - ∑' k, R1 (gs k) x'‖ ≤ _
      rw [← (S1 x hx).1.tsum_sub (S1 x' hx').1]; exact hb.2
    · have hb := tsum_bound (f := fun k => R2 (gs k) x - R2 (gs k) x') (mul_nonneg hc5 ht) hq0 hq1
        hN0p fun k => ((hRk k).2.2.2.1 x hx x' hx').2.2.trans (hcNt hc5 ht k)
      show ‖(∑' k, R2 (gs k) x) - ∑' k, R2 (gs k) x'‖ ≤ _
      rw [← (S2 x hx).1.tsum_sub (S2 x' hx').1]; exact hb.2

end Series

section ZextS

variable {d : ℕ}

theorem zext_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set (Eu d)} {x0 : Eu d}
    {ρ : ℝ} {f : Eu d → F} {f1 : Eu d → Eu d →L[ℝ] F}
    (hd : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt f (f1 x) x)
    (hvan : ∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → f y = 0) :
    ∀ x ∈ Ω, HasFDerivAt ((Metric.ball x0 ρ).indicator f) ((Metric.ball x0 ρ).indicator f1 x) x := by
  intro x hx
  by_cases hxb : x ∈ Metric.ball x0 ρ
  · rw [Set.indicator_of_mem hxb]
    refine (hd x ⟨hxb, hx⟩).congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
    exact Set.indicator_of_mem hy f
  · rw [Set.indicator_of_notMem hxb]
    have hρx : ρ ≤ ‖x - x0‖ := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at hxb; exact hxb
    refine (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq ?_
    have hρ2 : 0 < ρ / 2 ∨ ρ ≤ 0 := by
      rcases lt_or_ge 0 ρ with h | h
      · left; positivity
      · right; exact h
    rcases hρ2 with hρ2 | hρ2
    · filter_upwards [Metric.ball_mem_nhds x hρ2] with y hy
      by_cases hyb : y ∈ Metric.ball x0 ρ
      · rw [Set.indicator_of_mem hyb]
        apply hvan y hyb
        have h1 : ‖x - y‖ < ρ / 2 := by
          rw [Metric.mem_ball, dist_eq_norm] at hy; rwa [norm_sub_rev]
        have h2 : ‖x - x0‖ ≤ ‖x - y‖ + ‖y - x0‖ := norm_sub_le_norm_sub_add_norm_sub x y x0
        linarith
      · exact Set.indicator_of_notMem hyb f
    · filter_upwards with y
      have : y ∉ Metric.ball x0 ρ := by
        rw [Metric.ball_eq_empty.mpr hρ2]; exact Set.notMem_empty y
      exact Set.indicator_of_notMem this f

lemma one_le_scaled_rpow {ρ t μ : ℝ} (hρ : 0 < ρ) (ht : ρ / 2 ≤ t) (hμ : 0 ≤ μ) :
    1 ≤ (2 / ρ) ^ μ * t ^ μ := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  rw [← Real.mul_rpow (by positivity) ht0]
  apply Real.one_le_rpow _ hμ
  rw [div_mul_eq_mul_div, le_div_iff₀ hρ]; linarith

theorem zext_hol {F : Type*} [NormedAddCommGroup F] {X : Set (Eu d)} {x0 : Eu d} {ρ μ S H : ℝ}
    (hρ : 0 < ρ) (hμ : 0 ≤ μ) (hS : 0 ≤ S) (hH : 0 ≤ H) {f : Eu d → F}
    (hb : ∀ x ∈ Metric.ball x0 ρ ∩ X, ‖f x‖ ≤ S)
    (hh : ∀ x ∈ Metric.ball x0 ρ ∩ X, ∀ y ∈ Metric.ball x0 ρ ∩ X, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ μ)
    (hvan : ∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → f y = 0) :
    (∀ x ∈ X, ‖(Metric.ball x0 ρ).indicator f x‖ ≤ S) ∧
    ∀ x ∈ X, ∀ y ∈ X, ‖(Metric.ball x0 ρ).indicator f x - (Metric.ball x0 ρ).indicator f y‖ ≤
      (H + S * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ := by
  have hG : 0 ≤ S * (2 / ρ) ^ μ := mul_nonneg hS (Real.rpow_nonneg (by positivity) _)
  -- one point inside, the other outside
  have key : ∀ x ∈ X, ∀ y, x ∈ Metric.ball x0 ρ → y ∉ Metric.ball x0 ρ →
      ‖f x‖ ≤ (H + S * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ := by
    intro x hxX y hx hy
    have htm : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hfar : ρ / 2 ≤ ‖x - x0‖
    · rw [hvan x hx hfar, norm_zero]; positivity
    · have hxy : ρ / 2 ≤ ‖x - y‖ := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        rw [Metric.mem_ball, not_lt, dist_eq_norm] at hy
        have := norm_sub_le_norm_sub_add_norm_sub y x x0
        rw [norm_sub_rev y x] at this
        linarith
      have h1 := one_le_scaled_rpow hρ hxy hμ
      calc ‖f x‖ ≤ S := hb x ⟨hx, hxX⟩
        _ ≤ S * ((2 / ρ) ^ μ * ‖x - y‖ ^ μ) := le_mul_of_one_le_right hS h1
        _ ≤ (H + S * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ := by linarith [mul_nonneg hH htm]
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · by_cases hxb : x ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hxb]; exact hb x ⟨hxb, hx⟩
    · rw [Set.indicator_of_notMem hxb, norm_zero]; exact hS
  · have htm : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hxb : x ∈ Metric.ball x0 ρ <;> by_cases hyb : y ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hyb]
      exact (hh x ⟨hxb, hx⟩ y ⟨hyb, hy⟩).trans (by linarith [mul_nonneg hG htm])
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_notMem hyb, sub_zero]
      exact key x hx y hxb hyb
    · rw [Set.indicator_of_notMem hxb, Set.indicator_of_mem hyb, zero_sub, norm_neg, norm_sub_rev x y]
      exact key y hy x hyb hxb
    · rw [Set.indicator_of_notMem hxb, Set.indicator_of_notMem hyb, sub_zero, norm_zero]
      positivity

end ZextS

section ProdS

variable {d : ℕ}

noncomputable def prodP (χ W : Eu d → ℝ) : Eu d → ℝ := fun x => χ x * W x

noncomputable def prodP1 (χ W : Eu d → ℝ) (χ1 W1 : Eu d → Eu d →L[ℝ] ℝ) : Eu d → Eu d →L[ℝ] ℝ :=
  fun x => χ x • W1 x + W x • χ1 x

noncomputable def prodP2 (χ W : Eu d → ℝ) (χ1 W1 : Eu d → Eu d →L[ℝ] ℝ)
    (χ2 W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fun x => (χ x • W2 x + (χ1 x).smulRight (W1 x)) + (W x • χ2 x + (W1 x).smulRight (χ1 x))

noncomputable def ecut (W : Eu d → ℝ) (χ1 W1 : Eu d → Eu d →L[ℝ] ℝ)
    (χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : Eu d → ℝ :=
  fun x => ∑ i, χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1) +
    (1 / 2 : ℝ) * W x * ∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma app1_le (ℓ : Eu d →L[ℝ] ℝ) (i : Fin d) : |ℓ (EuclideanSpace.single i 1)| ≤ ‖ℓ‖ := by
  have := ℓ.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs] at this
  exact this

lemma app2_le (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (i : Fin d) :
    |B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ ‖B‖ := by
  have := B.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one, mul_one, Real.norm_eq_abs] at this
  exact this

lemma sum_abs_le_card {f : Fin d → ℝ} {C : ℝ} (h : ∀ i, |f i| ≤ C) : |∑ i, f i| ≤ d * C := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, C := Finset.sum_le_sum fun i _ => h i
    _ = d * C := by simp

lemma smul_hol {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a a' : ℝ} {u u' : F}
    {A U α β h : ℝ} (hA : |a| ≤ A) (hU : ‖u'‖ ≤ U) (hα : |a - a'| ≤ α * h) (hβ : ‖u - u'‖ ≤ β * h) :
    ‖a • u - a' • u'‖ ≤ (A * β + α * U) * h := by
  have e : a • u - a' • u' = a • (u - u') + (a - a') • u' := by rw [smul_sub, sub_smul]; abel
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hαh : 0 ≤ α * h := (abs_nonneg _).trans hα
  calc ‖a • u - a' • u'‖ ≤ ‖a • (u - u')‖ + ‖(a - a') • u'‖ := by rw [e]; exact norm_add_le _ _
    _ = |a| * ‖u - u'‖ + |a - a'| * ‖u'‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ A * (β * h) + (α * h) * U := add_le_add (mul_le_mul hA hβ (norm_nonneg _) hA0)
          (mul_le_mul hα hU (norm_nonneg _) hαh)
    _ = (A * β + α * U) * h := by ring

lemma mul_hol {a a' u u' : ℝ} {A U α β h : ℝ} (hA : |a| ≤ A) (hU : |u'| ≤ U) (hα : |a - a'| ≤ α * h)
    (hβ : |u - u'| ≤ β * h) : |a * u - a' * u'| ≤ (A * β + α * U) * h := by
  have e : a * u - a' * u' = a * (u - u') + (a - a') * u' := by ring
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hαh : 0 ≤ α * h := (abs_nonneg _).trans hα
  rw [e]
  calc |a * (u - u') + (a - a') * u'| ≤ |a * (u - u')| + |(a - a') * u'| := abs_add_le _ _
    _ = |a| * |u - u'| + |a - a'| * |u'| := by rw [abs_mul, abs_mul]
    _ ≤ A * (β * h) + (α * h) * U := add_le_add (mul_le_mul hA hβ (abs_nonneg _) hA0)
          (mul_le_mul hα hU (abs_nonneg _) hαh)
    _ = (A * β + α * U) * h := by ring

lemma smulRight_hol {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ℓ ℓ' : Eu d →L[ℝ] ℝ} {m m' : F}
    {A U α β h : ℝ} (hA : ‖ℓ'‖ ≤ A) (hU : ‖m‖ ≤ U) (hα : ‖ℓ - ℓ'‖ ≤ α * h) (hβ : ‖m - m'‖ ≤ β * h) :
    ‖ℓ.smulRight m - ℓ'.smulRight m'‖ ≤ (α * U + A * β) * h := by
  have e : ℓ.smulRight m - ℓ'.smulRight m' = (ℓ - ℓ').smulRight m + ℓ'.smulRight (m - m') := by
    ext v; simp [sub_smul, smul_sub]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hαh : 0 ≤ α * h := (norm_nonneg _).trans hα
  calc ‖ℓ.smulRight m - ℓ'.smulRight m'‖ ≤ ‖(ℓ - ℓ').smulRight m‖ + ‖ℓ'.smulRight (m - m')‖ := by
        rw [e]; exact norm_add_le _ _
    _ = ‖ℓ - ℓ'‖ * ‖m‖ + ‖ℓ'‖ * ‖m - m'‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ (α * h) * U + A * (β * h) := add_le_add (mul_le_mul hα hU (norm_nonneg _) hαh)
          (mul_le_mul hA hβ (norm_nonneg _) hA0)
    _ = (α * U + A * β) * h := by ring

theorem prod_local {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ Z τ : ℝ} {χ : Eu d → ℝ}
    {χ1 : Eu d → Eu d →L[ℝ] ℝ} {χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hcut : CutData Ω μ c x0 ρ Z τ χ χ1 χ2) {W : Eu d → ℝ} {W1 : Eu d → Eu d →L[ℝ] ℝ}
    {W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hWd : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x)
    (hWbc : ∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) :
    (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt (prodP χ W) (prodP1 χ W χ1 W1 x) x ∧
      HasFDerivAt (prodP1 χ W χ1 W1) (prodP2 χ W χ1 W1 χ2 W2 x) x) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, prodP1 χ W χ1 W1 x (c x) = 0) ∧
    (∀ x, (1 / 2 : ℝ) * ∑ i, prodP2 χ W χ1 W1 χ2 W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      χ x * ((1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) +
        ecut W χ1 W1 χ2 x) ∧
    (∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → prodP χ W y = 0 ∧ prodP1 χ W χ1 W1 y = 0 ∧
      prodP2 χ W χ1 W1 χ2 W2 y = 0 ∧ ecut W χ1 W1 χ2 y = 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_, fun y hy hfar => ?_⟩
  · obtain ⟨hc1, hc2⟩ := hcut.hd x hx
    obtain ⟨hw1, hw2⟩ := hWd x hx
    exact ⟨hc1.mul hw1, (hc1.smul hw2).add (hw1.smul hc2)⟩
  · show χ x • W1 x (c x) + W x • χ1 x (c x) = 0
    rw [hWbc x hx, hcut.bc x hx, smul_zero, smul_zero, add_zero]
  · have hi : ∀ i, prodP2 χ W χ1 W1 χ2 W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
        χ x * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
        2 * (χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1)) +
        W x * χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      intro i
      simp only [prodP2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [ecut]
    ring
  · obtain ⟨h0, h1, h2⟩ := hcut.van y hy hfar
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [prodP, h0]
    · simp [prodP1, h0, h1]
    · ext v w; simp [prodP2, h0, h1, h2]
    · simp [ecut, h1, h2]

theorem prod_bounds {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ Z τ : ℝ} {χ : Eu d → ℝ}
    {χ1 : Eu d → Eu d →L[ℝ] ℝ} {χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hcut : CutData Ω μ c x0 ρ Z τ χ χ1 χ2) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {W : Eu d → ℝ}
    {W1 : Eu d → Eu d →L[ℝ] ℝ} {W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ} {s0 s1 s2 t0 t1 t2 : ℝ}
    (hWb : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, |W x| ≤ s0 ∧ ‖W1 x‖ ≤ s1 ∧ ‖W2 x‖ ≤ s2)
    (hWh : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      |W x - W y| ≤ t0 * ‖x - y‖ ^ μ ∧ ‖W1 x - W1 y‖ ≤ t1 * ‖x - y‖ ^ μ ∧ ‖W2 x - W2 y‖ ≤ t2 * ‖x - y‖ ^ μ) :
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, |prodP χ W x| ≤ s0 ∧ ‖prodP1 χ W χ1 W1 x‖ ≤ s1 + s0 * Z ∧
      ‖prodP2 χ W χ1 W1 χ2 W2 x‖ ≤ (s2 + Z * s1) + (s0 * Z + s1 * Z) ∧
      |ecut W χ1 W1 χ2 x| ≤ d * (Z * s1) + 1 / 2 * (s0 * (d * Z))) ∧
    (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      |prodP χ W x - prodP χ W y| ≤ (1 * t0 + Z * (2 * ρ) ^ (1 - μ) * s0) * ‖x - y‖ ^ μ ∧
      ‖prodP1 χ W χ1 W1 x - prodP1 χ W χ1 W1 y‖ ≤
        ((1 * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + (s0 * (Z * (2 * ρ) ^ (1 - μ)) + t0 * Z)) * ‖x - y‖ ^ μ ∧
      ‖prodP2 χ W χ1 W1 χ2 W2 x - prodP2 χ W χ1 W1 χ2 W2 y‖ ≤
        (((1 * t2 + Z * (2 * ρ) ^ (1 - μ) * s2) + (Z * (2 * ρ) ^ (1 - μ) * s1 + Z * t1)) +
          ((s0 * Z + t0 * Z) + (t1 * Z + s1 * (Z * (2 * ρ) ^ (1 - μ))))) * ‖x - y‖ ^ μ ∧
      |ecut W χ1 W1 χ2 x - ecut W χ1 W1 χ2 y| ≤
        (d * (Z * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + 1 / 2 * (s0 * (d * Z) + t0 * (d * Z))) * ‖x - y‖ ^ μ) := by
  have hC := hcut.c2b
  have hZ : 0 ≤ Z := hC.hK
  set L := Z * (2 * ρ) ^ (1 - μ) with hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdist : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      ‖x - y‖ ≤ (2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ := by
    intro x hx y hy
    have h1 : dist x x0 < ρ := hx.1
    have h2 : dist y x0 < ρ := hy.1
    refine lip_le_hol (norm_nonneg _) ?_ hμ0 hμ1
    rw [← dist_eq_norm]; linarith [dist_triangle_right x y x0]
  have hχh : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      |χ x - χ y| ≤ L * ‖x - y‖ ^ μ := by
    intro x hx y hy
    have := hC.lip x hx y hy
    rw [Real.norm_eq_abs] at this
    calc |χ x - χ y| ≤ Z * ‖x - y‖ := this
      _ ≤ Z * ((2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ) := mul_le_mul_of_nonneg_left (hdist x hx y hy) hZ
      _ = L * ‖x - y‖ ^ μ := by rw [hL]; ring
  have hχ1h : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      ‖χ1 x - χ1 y‖ ≤ L * ‖x - y‖ ^ μ := by
    intro x hx y hy
    calc ‖χ1 x - χ1 y‖ ≤ Z * ‖x - y‖ := hC.lip1 x hx y hy
      _ ≤ Z * ((2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ) := mul_le_mul_of_nonneg_left (hdist x hx y hy) hZ
      _ = L * ‖x - y‖ ^ μ := by rw [hL]; ring
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [(hcut.rng x).1, (hcut.rng x).2]
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨b0, b1, b2⟩ := hWb x hx
    have c1 := hC.b1 x hx
    have c2 := hC.b2 x hx
    have hs0 : 0 ≤ s0 := (abs_nonneg _).trans b0
    have hs1 : 0 ≤ s1 := (norm_nonneg _).trans b1
    refine ⟨?_, ?_, ?_, ?_⟩
    · show |χ x * W x| ≤ s0
      rw [abs_mul]
      have := mul_le_mul (hχb x) b0 (abs_nonneg _) zero_le_one
      linarith
    · show ‖χ x • W1 x + W x • χ1 x‖ ≤ s1 + s0 * Z
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have e1 : |χ x| * ‖W1 x‖ ≤ 1 * s1 := mul_le_mul (hχb x) b1 (norm_nonneg _) zero_le_one
      have e2 : |W x| * ‖χ1 x‖ ≤ s0 * Z := mul_le_mul b0 c1 (norm_nonneg _) hs0
      linarith
    · show ‖(χ x • W2 x + (χ1 x).smulRight (W1 x)) + (W x • χ2 x + (W1 x).smulRight (χ1 x))‖ ≤ _
      have nA := norm_add_le (χ x • W2 x) ((χ1 x).smulRight (W1 x))
      have nB := norm_add_le (W x • χ2 x) ((W1 x).smulRight (χ1 x))
      have nC := norm_add_le (χ x • W2 x + (χ1 x).smulRight (W1 x)) (W x • χ2 x + (W1 x).smulRight (χ1 x))
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs] at nA
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs] at nB
      have e1 : |χ x| * ‖W2 x‖ ≤ 1 * s2 := mul_le_mul (hχb x) b2 (norm_nonneg _) zero_le_one
      have e2 : ‖χ1 x‖ * ‖W1 x‖ ≤ Z * s1 := mul_le_mul c1 b1 (norm_nonneg _) hZ
      have e3 : |W x| * ‖χ2 x‖ ≤ s0 * Z := mul_le_mul b0 c2 (norm_nonneg _) hs0
      have e4 : ‖W1 x‖ * ‖χ1 x‖ ≤ s1 * Z := mul_le_mul b1 c1 (norm_nonneg _) hs1
      linarith
    · show |∑ i, χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1) +
        (1 / 2 : ℝ) * W x * ∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ _
      have f1 : |∑ i, χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1)| ≤ d * (Z * s1) :=
        sum_abs_le_card fun i => by
          rw [abs_mul]
          exact mul_le_mul ((app1_le _ i).trans c1) ((app1_le _ i).trans b1) (abs_nonneg _) hZ
      have f2 : |∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ d * Z :=
        sum_abs_le_card fun i => (app2_le _ i).trans c2
      have f3 : |(1 / 2 : ℝ) * W x * ∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤
          1 / 2 * (s0 * (d * Z)) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul b0 f2 (abs_nonneg _) hs0) (by norm_num)
      exact (abs_add_le _ _).trans (add_le_add f1 f3)
  · obtain ⟨b0, b1, b2⟩ := hWb y hy
    obtain ⟨b0x, b1x, b2x⟩ := hWb x hx
    obtain ⟨h0, h1, h2⟩ := hWh x hx y hy
    have c1 := hC.b1 x hx
    have c1y := hC.b1 y hy
    have c2y := hC.b2 y hy
    have c2h := hC.hol2 x hx y hy
    have hs0 : 0 ≤ s0 := (abs_nonneg _).trans b0
    have hs1 : 0 ≤ s1 := (norm_nonneg _).trans b1
    have htm : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mul_hol (hχb x) b0 (hχh x hx y hy) h0
    · show ‖(χ x • W1 x + W x • χ1 x) - (χ y • W1 y + W y • χ1 y)‖ ≤ _
      rw [add_sub_add_comm, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (smul_hol (hχb x) b1 (hχh x hx y hy) h1)
        (smul_hol b0x c1y h0 (hχ1h x hx y hy)))
    · show ‖((χ x • W2 x + (χ1 x).smulRight (W1 x)) + (W x • χ2 x + (W1 x).smulRight (χ1 x))) -
        ((χ y • W2 y + (χ1 y).smulRight (W1 y)) + (W y • χ2 y + (W1 y).smulRight (χ1 y)))‖ ≤ _
      have e : ((χ x • W2 x + (χ1 x).smulRight (W1 x)) + (W x • χ2 x + (W1 x).smulRight (χ1 x))) -
          ((χ y • W2 y + (χ1 y).smulRight (W1 y)) + (W y • χ2 y + (W1 y).smulRight (χ1 y))) =
          ((χ x • W2 x - χ y • W2 y) + ((χ1 x).smulRight (W1 x) - (χ1 y).smulRight (W1 y))) +
          ((W x • χ2 x - W y • χ2 y) + ((W1 x).smulRight (χ1 x) - (W1 y).smulRight (χ1 y))) := by abel
      rw [e]
      have k1 := smul_hol (hχb x) b2 (hχh x hx y hy) h2
      have k2 := smulRight_hol (m := W1 x) (m' := W1 y) c1y b1x (hχ1h x hx y hy) h1
      have k3 := smul_hol b0x c2y h0 c2h
      have k4 := smulRight_hol (m := χ1 x) (m' := χ1 y) b1 c1 h1 (hχ1h x hx y hy)
      have nA := norm_add_le (χ x • W2 x - χ y • W2 y) ((χ1 x).smulRight (W1 x) - (χ1 y).smulRight (W1 y))
      have nB := norm_add_le (W x • χ2 x - W y • χ2 y) ((W1 x).smulRight (χ1 x) - (W1 y).smulRight (χ1 y))
      have nC := norm_add_le ((χ x • W2 x - χ y • W2 y) + ((χ1 x).smulRight (W1 x) - (χ1 y).smulRight (W1 y)))
        ((W x • χ2 x - W y • χ2 y) + ((W1 x).smulRight (χ1 x) - (W1 y).smulRight (χ1 y)))
      linarith
    · show |(∑ i, χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1) +
          (1 / 2 : ℝ) * W x * ∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) -
        (∑ i, χ1 y (EuclideanSpace.single i 1) * W1 y (EuclideanSpace.single i 1) +
          (1 / 2 : ℝ) * W y * ∑ i, χ2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))| ≤ _
      rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
      have f1 : |∑ i, (χ1 x (EuclideanSpace.single i 1) * W1 x (EuclideanSpace.single i 1) -
          χ1 y (EuclideanSpace.single i 1) * W1 y (EuclideanSpace.single i 1))| ≤
          d * ((Z * t1 + L * s1) * ‖x - y‖ ^ μ) := by
        refine sum_abs_le_card fun i => mul_hol ((app1_le _ i).trans c1) ((app1_le _ i).trans b1) ?_ ?_
        · rw [← ContinuousLinearMap.sub_apply]; exact (app1_le _ i).trans (hχ1h x hx y hy)
        · rw [← ContinuousLinearMap.sub_apply]; exact (app1_le _ i).trans h1
      have g1 : |∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ d * Z :=
        sum_abs_le_card fun i => (app2_le _ i).trans (hC.b2 x hx)
      have g2 : |∑ i, χ2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ d * Z :=
        sum_abs_le_card fun i => (app2_le _ i).trans c2y
      have g3 : |∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) -
          ∑ i, χ2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ (d * Z) * ‖x - y‖ ^ μ := by
        rw [← Finset.sum_sub_distrib]
        have hi : ∀ i, |χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) -
            χ2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ Z * ‖x - y‖ ^ μ := fun i => by
          have h' := (app2_le (χ2 x - χ2 y) i).trans c2h
          rwa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply] at h'
        have := sum_abs_le_card hi
        linarith [this]
      have f2 := mul_hol b0x g2 h0 g3
      have f3 : |(1 / 2 : ℝ) * W x * ∑ i, χ2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) -
          (1 / 2 : ℝ) * W y * ∑ i, χ2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤
          1 / 2 * ((s0 * (d * Z) + t0 * (d * Z)) * ‖x - y‖ ^ μ) := by
        rw [mul_assoc, mul_assoc, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left f2 (by norm_num)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ d * ((Z * t1 + L * s1) * ‖x - y‖ ^ μ) + 1 / 2 * ((s0 * (d * Z) + t0 * (d * Z)) * ‖x - y‖ ^ μ) :=
            add_le_add f1 f3
        _ = _ := by rw [hL]; ring

end ProdS

section PatchS

variable {d : ℕ}

theorem patch_glue {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ Z τ : ℝ} {χ : Eu d → ℝ}
    {χ1 : Eu d → Eu d →L[ℝ] ℝ} {χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hcut : CutData Ω μ c x0 ρ Z τ χ χ1 χ2) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {lam : ℝ} {g : Eu d → ℝ}
    {W : Eu d → ℝ} {W1 : Eu d → Eu d →L[ℝ] ℝ} {W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    {s0 s1 s2 t0 t1 t2 : ℝ} (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1)
    (ht2 : 0 ≤ t2)
    (hWd : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x)
    (hWbc : ∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0)
    (hWeq : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
      lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x)
    (hWb : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, |W x| ≤ s0 ∧ ‖W1 x‖ ≤ s1 ∧ ‖W2 x‖ ≤ s2)
    (hWh : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω,
      |W x - W y| ≤ t0 * ‖x - y‖ ^ μ ∧ ‖W1 x - W1 y‖ ≤ t1 * ‖x - y‖ ^ μ ∧ ‖W2 x - W2 y‖ ≤ t2 * ‖x - y‖ ^ μ) :
    (∀ x ∈ Ω, HasFDerivAt ((Metric.ball x0 ρ).indicator (prodP χ W))
        ((Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x) x ∧
      HasFDerivAt ((Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1))
        ((Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x) x) ∧
    (∀ x ∈ frontier Ω, (Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x (c x) = 0) ∧
    (∀ x ∈ closure Ω, lam * (Metric.ball x0 ρ).indicator (prodP χ W) x - (1 / 2 : ℝ) *
        ∑ i, (Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single i 1) =
      (Metric.ball x0 ρ).indicator χ x * g x - (Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) x) ∧
    (∀ y, 0 ≤ (Metric.ball x0 ρ).indicator χ y ∧ (Metric.ball x0 ρ).indicator χ y ≤ 1) ∧
    (∀ y ∈ Metric.ball x0 (min τ ρ), (Metric.ball x0 ρ).indicator χ y = 1) ∧
    (∀ x ∈ closure Ω, |(Metric.ball x0 ρ).indicator (prodP χ W) x| ≤ s0 ∧
      ‖(Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x‖ ≤ s1 + s0 * Z ∧
      ‖(Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x‖ ≤ (s2 + Z * s1) + (s0 * Z + s1 * Z) ∧
      |(Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) x| ≤ d * (Z * s1) + 1 / 2 * (s0 * (d * Z))) ∧
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
      |(Metric.ball x0 ρ).indicator χ x - (Metric.ball x0 ρ).indicator χ y| ≤
        (Z * (2 * ρ) ^ (1 - μ) + 1 * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ ∧
      |(Metric.ball x0 ρ).indicator (prodP χ W) x - (Metric.ball x0 ρ).indicator (prodP χ W) y| ≤
        ((1 * t0 + Z * (2 * ρ) ^ (1 - μ) * s0) + s0 * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ ∧
      ‖(Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x - (Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) y‖ ≤
        (((1 * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + (s0 * (Z * (2 * ρ) ^ (1 - μ)) + t0 * Z)) +
          (s1 + s0 * Z) * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ ∧
      ‖(Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x -
          (Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) y‖ ≤
        ((((1 * t2 + Z * (2 * ρ) ^ (1 - μ) * s2) + (Z * (2 * ρ) ^ (1 - μ) * s1 + Z * t1)) +
          ((s0 * Z + t0 * Z) + (t1 * Z + s1 * (Z * (2 * ρ) ^ (1 - μ))))) +
          ((s2 + Z * s1) + (s0 * Z + s1 * Z)) * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ ∧
      |(Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) x - (Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) y| ≤
        ((d * (Z * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + 1 / 2 * (s0 * (d * Z) + t0 * (d * Z))) +
          (d * (Z * s1) + 1 / 2 * (s0 * (d * Z))) * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ) := by
  have hρ := hcut.hρ
  have hZ : 0 ≤ Z := hcut.c2b.hK
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL : 0 ≤ Z * (2 * ρ) ^ (1 - μ) := mul_nonneg hZ (Real.rpow_nonneg (by linarith) _)
  obtain ⟨hPd, hPbc, hPlap, hPvan⟩ := prod_local hcut hWd hWbc
  obtain ⟨hPb, hPh⟩ := prod_bounds hcut hμ0 hμ1 hWb hWh
  have hsub : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, x ∈ Metric.ball x0 ρ ∩ closure Ω := fun x hx => hx
  refine ⟨fun x hx => ⟨zext_hasFDerivAt (fun y hy => (hPd y hy).1) (fun y hy hf => (hPvan y hy hf).1) x hx,
      zext_hasFDerivAt (fun y hy => (hPd y hy).2) (fun y hy hf => (hPvan y hy hf).2.1) x hx⟩,
    fun x hx => ?_, fun x hx => ?_, fun y => ?_, fun y hy => ?_, ?_⟩
  · by_cases hxb : x ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hxb]; exact hPbc x ⟨hxb, hx⟩
    · rw [Set.indicator_of_notMem hxb, ContinuousLinearMap.zero_apply]
  · by_cases hxb : x ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hxb, Set.indicator_of_mem hxb,
        Set.indicator_of_mem hxb, hPlap x, ← hWeq x ⟨hxb, hx⟩]
      simp only [prodP]
      ring
    · simp only [Set.indicator_of_notMem hxb, ContinuousLinearMap.zero_apply, Finset.sum_const_zero]
      ring
  · by_cases hyb : y ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hyb]; exact hcut.rng y
    · rw [Set.indicator_of_notMem hyb]; exact ⟨le_rfl, zero_le_one⟩
  · have hyb : y ∈ Metric.ball x0 ρ := Metric.ball_subset_ball (min_le_right τ ρ) hy
    rw [Set.indicator_of_mem hyb]
    exact hcut.one y (Metric.ball_subset_ball (min_le_left τ ρ) hy)
  -- sup / Hölder via zext_hol on X = closure Ω
  have hH0 : 0 ≤ 1 * t0 + Z * (2 * ρ) ^ (1 - μ) * s0 := add_nonneg (by linarith) (mul_nonneg hL hs0)
  have hS1 : 0 ≤ s1 + s0 * Z := add_nonneg hs1 (mul_nonneg hs0 hZ)
  have hH1 : 0 ≤ (1 * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + (s0 * (Z * (2 * ρ) ^ (1 - μ)) + t0 * Z) :=
    add_nonneg (add_nonneg (by linarith) (mul_nonneg hL hs1)) (add_nonneg (mul_nonneg hs0 hL) (mul_nonneg ht0 hZ))
  have hS2 : 0 ≤ (s2 + Z * s1) + (s0 * Z + s1 * Z) :=
    add_nonneg (add_nonneg hs2 (mul_nonneg hZ hs1)) (add_nonneg (mul_nonneg hs0 hZ) (mul_nonneg hs1 hZ))
  have hH2 : 0 ≤ ((1 * t2 + Z * (2 * ρ) ^ (1 - μ) * s2) + (Z * (2 * ρ) ^ (1 - μ) * s1 + Z * t1)) +
      ((s0 * Z + t0 * Z) + (t1 * Z + s1 * (Z * (2 * ρ) ^ (1 - μ)))) :=
    add_nonneg (add_nonneg (add_nonneg (by linarith) (mul_nonneg hL hs2))
      (add_nonneg (mul_nonneg hL hs1) (mul_nonneg hZ ht1)))
      (add_nonneg (add_nonneg (mul_nonneg hs0 hZ) (mul_nonneg ht0 hZ))
        (add_nonneg (mul_nonneg ht1 hZ) (mul_nonneg hs1 hL)))
  have hS3 : 0 ≤ d * (Z * s1) + 1 / 2 * (s0 * (d * Z)) :=
    add_nonneg (mul_nonneg hd0 (mul_nonneg hZ hs1)) (mul_nonneg (by norm_num) (mul_nonneg hs0 (mul_nonneg hd0 hZ)))
  have hH3 : 0 ≤ d * (Z * t1 + Z * (2 * ρ) ^ (1 - μ) * s1) + 1 / 2 * (s0 * (d * Z) + t0 * (d * Z)) :=
    add_nonneg (mul_nonneg hd0 (add_nonneg (mul_nonneg hZ ht1) (mul_nonneg hL hs1)))
      (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hs0 (mul_nonneg hd0 hZ)) (mul_nonneg ht0 (mul_nonneg hd0 hZ))))
  have z0 := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 hs0 hH0 (f := prodP χ W)
    (fun x hx => by rw [Real.norm_eq_abs]; exact (hPb x hx).1)
    (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hPh x hx y hy).1)
    (fun y hy hf => (hPvan y hy hf).1)
  have z1 := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 hS1 hH1 (f := prodP1 χ W χ1 W1)
    (fun x hx => (hPb x hx).2.1) (fun x hx y hy => (hPh x hx y hy).2.1)
    (fun y hy hf => (hPvan y hy hf).2.1)
  have z2 := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 hS2 hH2 (f := prodP2 χ W χ1 W1 χ2 W2)
    (fun x hx => (hPb x hx).2.2.1) (fun x hx y hy => (hPh x hx y hy).2.2.1)
    (fun y hy hf => (hPvan y hy hf).2.2.1)
  have z3 := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 hS3 hH3 (f := ecut W χ1 W1 χ2)
    (fun x hx => by rw [Real.norm_eq_abs]; exact (hPb x hx).2.2.2)
    (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hPh x hx y hy).2.2.2)
    (fun y hy hf => (hPvan y hy hf).2.2.2)
  have zc := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 zero_le_one hL (f := χ)
    (fun x _ => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hcut.rng x).1, (hcut.rng x).2])
    (fun x hx y hy => by
      have h1 : dist x x0 < ρ := hx.1
      have h2 : dist y x0 < ρ := hy.1
      have hd : ‖x - y‖ ≤ (2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ := by
        refine lip_le_hol (norm_nonneg _) ?_ hμ0 hμ1
        rw [← dist_eq_norm]; linarith [dist_triangle_right x y x0]
      calc ‖χ x - χ y‖ ≤ Z * ‖x - y‖ := hcut.c2b.lip x hx y hy
        _ ≤ Z * ((2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ) := mul_le_mul_of_nonneg_left hd hZ
        _ = Z * (2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ := by ring)
    (fun y hy hf => (hcut.van y hy hf).1)
  refine ⟨fun x hx => ⟨?_, z1.1 x hx, z2.1 x hx, ?_⟩, fun x hx y hy => ⟨?_, ?_, z1.2 x hx y hy, z2.2 x hx y hy, ?_⟩⟩
  · have := z0.1 x hx; rwa [Real.norm_eq_abs] at this
  · have := z3.1 x hx; rwa [Real.norm_eq_abs] at this
  · have := zc.2 x hx y hy; rwa [Real.norm_eq_abs] at this
  · have := z0.2 x hx y hy; rwa [Real.norm_eq_abs] at this
  · have := z3.2 x hx y hy; rwa [Real.norm_eq_abs] at this

end PatchS

section CanonS

variable {d : ℕ}

noncomputable def hbM (X : Set (Eu d)) (g : Eu d → ℝ) : ℝ := sInf {M : ℝ | 0 ≤ M ∧ ∀ x ∈ X, |g x| ≤ M}

noncomputable def hbH (X : Set (Eu d)) (μ : ℝ) (g : Eu d → ℝ) : ℝ :=
  sInf {H : ℝ | 0 ≤ H ∧ ∀ x ∈ X, ∀ y ∈ X, |g x - g y| ≤ H * ‖x - y‖ ^ μ}

theorem hb_canon {X : Set (Eu d)} {μ M H : ℝ} {g : Eu d → ℝ} (h : HB X μ M H g) :
    HB X μ (hbM X g) (hbH X μ g) g ∧ hbM X g ≤ M ∧ hbH X μ g ≤ H := by
  obtain ⟨hM, hH, hb, hh⟩ := h
  have nM : ({M : ℝ | 0 ≤ M ∧ ∀ x ∈ X, |g x| ≤ M}).Nonempty := ⟨M, hM, hb⟩
  have nH : ({H : ℝ | 0 ≤ H ∧ ∀ x ∈ X, ∀ y ∈ X, |g x - g y| ≤ H * ‖x - y‖ ^ μ}).Nonempty := ⟨H, hH, hh⟩
  have bM : BddBelow {M : ℝ | 0 ≤ M ∧ ∀ x ∈ X, |g x| ≤ M} := ⟨0, fun m hm => hm.1⟩
  have bH : BddBelow {H : ℝ | 0 ≤ H ∧ ∀ x ∈ X, ∀ y ∈ X, |g x - g y| ≤ H * ‖x - y‖ ^ μ} :=
    ⟨0, fun m hm => hm.1⟩
  refine ⟨⟨le_csInf nM fun m hm => hm.1, le_csInf nH fun m hm => hm.1,
    fun x hx => le_csInf nM fun m hm => hm.2 x hx, fun x hx y hy => ?_⟩,
    csInf_le bM ⟨hM, hb⟩, csInf_le bH ⟨hH, hh⟩⟩
  have ha : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
  rcases ha.lt_or_eq with ha | ha
  · have : |g x - g y| / ‖x - y‖ ^ μ ≤ hbH X μ g :=
      le_csInf nH fun m hm => (div_le_iff₀ ha).mpr (hm.2 x hx y hy)
    exact (div_le_iff₀ ha).mp this
  · have := hh x hx y hy
    rw [← ha, mul_zero] at this ⊢
    exact this

lemma HB.congr {X : Set (Eu d)} {μ M H : ℝ} {f f' : Eu d → ℝ} (h : HB X μ M H f) (he : ∀ x ∈ X, f x = f' x) :
    HB X μ M H f' := by
  obtain ⟨hM, hH, hb, hh⟩ := h
  refine ⟨hM, hH, fun x hx => (he x hx) ▸ hb x hx, fun x hx y hy => ?_⟩
  rw [← he x hx, ← he y hy]; exact hh x hx y hy

theorem quot_cover {X : Set (Eu d)} {μ : ℝ} {ι : Type*} (t : Finset ι) (χ : ι → Eu d → ℝ) (hc : ι → ℝ)
    (hc0 : ∀ p ∈ t, 0 ≤ hc p) (hrng : ∀ p ∈ t, ∀ y, 0 ≤ χ p y ∧ χ p y ≤ 1)
    (hhol : ∀ p ∈ t, ∀ x ∈ X, ∀ y ∈ X, |χ p x - χ p y| ≤ hc p * ‖x - y‖ ^ μ)
    (hone : ∀ x ∈ X, ∃ p ∈ t, χ p x = 1) :
    (∀ x ∈ X, 1 ≤ ∑ p ∈ t, χ p x) ∧
    (∀ x ∈ X, ∀ y ∈ X, |∑ p ∈ t, χ p x - ∑ p ∈ t, χ p y| ≤ (∑ p ∈ t, hc p) * ‖x - y‖ ^ μ) ∧
    ∀ (g : Eu d → ℝ) (M H : ℝ), HB X μ M H g →
      HB X μ M (H + M * ∑ p ∈ t, hc p) (fun x => g x / ∑ p ∈ t, χ p x) := by
  have hS1 : ∀ x ∈ X, 1 ≤ ∑ p ∈ t, χ p x := by
    intro x hx
    obtain ⟨p, hp, h1⟩ := hone x hx
    rw [← h1]
    exact Finset.single_le_sum (f := fun q => χ q x) (fun q hq => (hrng q hq x).1) hp
  have hSh : ∀ x ∈ X, ∀ y ∈ X, |∑ p ∈ t, χ p x - ∑ p ∈ t, χ p y| ≤ (∑ p ∈ t, hc p) * ‖x - y‖ ^ μ := by
    intro x hx y hy
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => hhol p hp x hx y hy)
  refine ⟨hS1, hSh, fun g M H hg => ?_⟩
  obtain ⟨hM, hH, hb, hh⟩ := hg
  have hsum0 : 0 ≤ ∑ p ∈ t, hc p := Finset.sum_nonneg hc0
  refine ⟨hM, add_nonneg hH (mul_nonneg hM hsum0), fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h1 := hS1 x hx
    dsimp only
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < ∑ p ∈ t, χ p x)]
    exact (div_le_self (abs_nonneg _) h1).trans (hb x hx)
  · have h1 := hS1 x hx
    have h2 := hS1 y hy
    have hSxy := hSh x hx y hy
    dsimp only
    set Sx := ∑ p ∈ t, χ p x with hSx
    set Sy := ∑ p ∈ t, χ p y with hSy
    set a := ‖x - y‖ ^ μ with ha
    have hx0 : Sx ≠ 0 := by linarith
    have hy0 : Sy ≠ 0 := by linarith
    have key : g x / Sx - g y / Sy = (g x - g y) / Sx + g y * (Sy - Sx) / (Sx * Sy) := by
      field_simp; ring
    have e1 : |(g x - g y) / Sx| ≤ H * a := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Sx)]
      exact (div_le_self (abs_nonneg _) h1).trans (hh x hx y hy)
    have e2 : |g y * (Sy - Sx) / (Sx * Sy)| ≤ M * ((∑ p ∈ t, hc p) * a) := by
      have hpos : 0 < Sx * Sy := by nlinarith
      rw [abs_div, abs_of_pos hpos]
      refine (div_le_self (abs_nonneg _) (by nlinarith)).trans ?_
      rw [abs_mul]
      exact mul_le_mul (hb y hy) (by rw [abs_sub_comm]; exact hSxy) (abs_nonneg _) hM
    calc |g x / Sx - g y / Sy| = |(g x - g y) / Sx + g y * (Sy - Sx) / (Sx * Sy)| := by rw [key]
      _ ≤ |(g x - g y) / Sx| + |g y * (Sy - Sx) / (Sx * Sy)| := abs_add_le _ _
      _ ≤ H * a + M * ((∑ p ∈ t, hc p) * a) := add_le_add e1 e2
      _ = (H + M * ∑ p ∈ t, hc p) * a := by ring

end CanonS

section LinS

variable {d : ℕ}

theorem patch_lin {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ Z τ : ℝ} {χ : Eu d → ℝ}
    {χ1 : Eu d → Eu d →L[ℝ] ℝ} {χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hcut : CutData Ω μ c x0 ρ Z τ χ χ1 χ2) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {C lam N : ℝ} (hC : 0 ≤ C)
    (hlam : 1 ≤ lam) (hN : 0 ≤ N) {g : Eu d → ℝ}
    {W : Eu d → ℝ} {W1 : Eu d → Eu d →L[ℝ] ℝ} {W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hWd : ∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x)
    (hWbc : ∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0)
    (hWeq : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
      lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x)
    (hWb : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * N ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * N ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * N)
    (hWh : ∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * N * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * N * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * N * ‖x - x'‖ ^ μ) :
    ∃ eM eH : ℝ, 0 ≤ eM ∧ 0 ≤ eH ∧
      lam ^ (μ / 2) * eM + eH ≤
        4 * d * (Z + Z * (2 / ρ) ^ μ + Z * (2 * ρ) ^ (1 - μ)) * C * (1 / lam) ^ (1 / 2 : ℝ) ∧
      (∀ x ∈ closure Ω,
        |(Metric.ball x0 ρ).indicator (prodP χ W) x| ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N ∧
        ‖(Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x‖ ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N ∧
        ‖(Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x‖ ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N ∧
        |(Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) x| ≤ eM * N) ∧
      (∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
        |(Metric.ball x0 ρ).indicator (prodP χ W) x - (Metric.ball x0 ρ).indicator (prodP χ W) y| ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N * ‖x - y‖ ^ μ ∧
        ‖(Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) x -
            (Metric.ball x0 ρ).indicator (prodP1 χ W χ1 W1) y‖ ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N * ‖x - y‖ ^ μ ∧
        ‖(Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) x -
            (Metric.ball x0 ρ).indicator (prodP2 χ W χ1 W1 χ2 W2) y‖ ≤
          C * (4 * (1 + Z + Z * (2 * ρ) ^ (1 - μ) + (2 / ρ) ^ μ + Z * (2 / ρ) ^ μ)) * N * ‖x - y‖ ^ μ ∧
        |(Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) x - (Metric.ball x0 ρ).indicator (ecut W χ1 W1 χ2) y| ≤
          eH * N * ‖x - y‖ ^ μ) := by
  have hρ := hcut.hρ
  have hZ : 0 ≤ Z := hcut.c2b.hK
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlam0 : 0 < lam := by linarith
  have hℓ0 : 0 < 1 / lam := by positivity
  have hℓ1 : 1 / lam ≤ 1 := by rw [div_le_one hlam0]; exact hlam
  have hwE : lam ^ (μ / 2) * (1 / lam) ^ (μ / 2) = 1 := by
    rw [← Real.mul_rpow hlam0.le hℓ0.le, mul_one_div_cancel hlam0.ne', Real.one_rpow]
  have hE0 : 0 ≤ (1 / lam) ^ (μ / 2) := Real.rpow_nonneg hℓ0.le _
  have hE1 : (1 / lam) ^ (μ / 2) ≤ 1 := Real.rpow_le_one hℓ0.le hℓ1 (by linarith)
  have hs0 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hℓ0.le _
  have hs1 : (1 / lam) ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hℓ0.le hℓ1 (by norm_num)
  have hℓs : 1 / lam ≤ (1 / lam) ^ (1 / 2 : ℝ) := by
    calc 1 / lam = (1 / lam) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hℓ0 hℓ1 (by norm_num)
  have hL : 0 ≤ Z * (2 * ρ) ^ (1 - μ) := mul_nonneg hZ (Real.rpow_nonneg (by linarith) _)
  have hG : 0 ≤ (2 / ρ) ^ μ := Real.rpow_nonneg (by positivity) _
  set ℓ := 1 / lam with hℓdef
  set s := ℓ ^ (1 / 2 : ℝ) with hsdef
  set E := ℓ ^ (μ / 2) with hEdef
  set w := lam ^ (μ / 2) with hwdef
  set L := Z * (2 * ρ) ^ (1 - μ) with hLdef
  set G := (2 / ρ) ^ μ with hGdef
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  -- refined application (exact LocSol weights) for the residual
  obtain ⟨-, -, -, -, -, hB1, hH1⟩ := patch_glue hcut hμ0 hμ1 (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hWd hWbc hWeq hWb hWh
  -- crude application (all weights `C N`)
  have hℓE : ℓ * E ≤ 1 := mul_le_one₀ hℓ1 hE0 hE1
  have hsE : s * E ≤ 1 := mul_le_one₀ hs1 hE0 hE1
  obtain ⟨-, -, -, -, -, hB2, hH2⟩ := patch_glue hcut hμ0 hμ1 hCN hCN hCN hCN hCN hCN hWd hWbc hWeq
    (fun x hx => by
      obtain ⟨b0, b1, b2⟩ := hWb x hx
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
      · have := mul_le_of_le_one_right hCN hℓE
        linarith
      · have := mul_le_of_le_one_right hCN hsE
        linarith
      · have := mul_le_of_le_one_right hCN hE1
        linarith)
    (fun x hx y hy => by
      obtain ⟨b0, b1, b2⟩ := hWh x hx y hy
      have hp : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
      · have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hCN hℓ1) hp
        linarith
      · have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hCN hs1) hp
        linarith
      · exact le_rfl)
  -- the crude constant
  set K0 := 4 * (1 + Z + L + G + Z * G) with hK0
  have hZG : 0 ≤ Z * G := mul_nonneg hZ hG
  have up : ∀ Q : ℝ, 0 ≤ K0 - Q → C * N * Q ≤ C * K0 * N := fun Q hQ => by
    have := mul_nonneg hCN hQ
    linarith
  refine ⟨d * (Z * (C * s * E)) + 1 / 2 * (C * ℓ * E * (d * Z)),
    (d * (Z * (C * s) + L * (C * s * E)) + 1 / 2 * (C * ℓ * E * (d * Z) + C * ℓ * (d * Z))) +
      (d * (Z * (C * s * E)) + 1 / 2 * (C * ℓ * E * (d * Z))) * G, by positivity, by positivity, ?_,
    fun x hx => ⟨?_, ?_, ?_, ?_⟩, fun x hx y hy => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- residual scaling
    have e1 : w * (d * (Z * (C * s * E)) + 1 / 2 * (C * ℓ * E * (d * Z))) =
        (d * Z * C * s + 1 / 2 * (C * ℓ * d * Z)) * (w * E) := by ring
    rw [e1, hwE, mul_one]
    have hdZC : 0 ≤ d * Z * C := by positivity
    have f1 : C * ℓ * d * Z ≤ d * Z * C * s := by
      have := mul_le_mul_of_nonneg_left hℓs hdZC; linarith
    have f2 : d * (L * (C * s * E)) ≤ d * L * C * s := by
      have := mul_le_of_le_one_right (by positivity : 0 ≤ d * L * C * s) hE1; linarith
    have f3 : C * ℓ * E * (d * Z) ≤ d * Z * C * s := by
      have h1 : ℓ * E ≤ s := (mul_le_of_le_one_right hℓ0.le hE1).trans hℓs
      have := mul_le_mul_of_nonneg_left h1 hdZC; linarith
    have f4 : d * (Z * (C * s * E)) ≤ d * Z * C * s := by
      have := mul_le_of_le_one_right (by positivity : 0 ≤ d * Z * C * s) hE1; linarith
    have f5 : (d * (Z * (C * s * E)) + 1 / 2 * (C * ℓ * E * (d * Z))) * G ≤ (3 / 2) * (d * Z * C * s) * G :=
      mul_le_mul_of_nonneg_right (by linarith) hG
    have g1 : 0 ≤ d * Z * C * s := by positivity
    have g2 : 0 ≤ d * L * C * s := by positivity
    have g3 : 0 ≤ d * Z * C * s * G := by positivity
    have e2 : 4 * d * (Z + Z * G + L) * C * s = 4 * (d * Z * C * s) + 4 * (d * Z * C * s * G) + 4 * (d * L * C * s) := by
      ring
    have e3 : (3 / 2) * (d * Z * C * s) * G = (3 / 2) * (d * Z * C * s * G) := by ring
    rw [e2]
    linarith
  · have := (hB2 x hx).1
    have h := up 1 (by linarith)
    linarith
  · have := (hB2 x hx).2.1
    have h := up (1 + Z) (by linarith)
    linarith
  · have := (hB2 x hx).2.2.1
    have h := up (1 + 3 * Z) (by linarith)
    linarith
  · have := (hB1 x hx).2.2.2
    linarith
  · have := (hH2 x hx y hy).2.1
    have h := up (1 + L + G) (by linarith)
    have hp : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have := mul_le_mul_of_nonneg_right h hp
    linarith
  · have := (hH2 x hx y hy).2.2.1
    have h := up (1 + 2 * L + Z + G + Z * G) (by linarith)
    have hp : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have := mul_le_mul_of_nonneg_right h hp
    linarith
  · have := (hH2 x hx y hy).2.2.2.1
    have h := up (1 + 3 * L + 4 * Z + G + 3 * (Z * G)) (by linarith)
    have hp : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have := mul_le_mul_of_nonneg_right h hp
    linarith
  · have := (hH1 x hx y hy).2.2.2.2
    linarith

end LinS

section GlobalS

variable {d : ℕ}

noncomputable def halfLap : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))

lemma halfLap_apply (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :
    halfLap B = (1 / 2 : ℝ) * ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp only [halfLap, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]

def LocOut (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (ρ C lam : ℝ) (g : Eu d → ℝ) (M H : ℝ)
    (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : Prop :=
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

lemma LocSol.out {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ lam0 C lam : ℝ}
    (h : LocSol Ω μ c x0 ρ lam0 C) (hl : lam0 ≤ lam) (g : Eu d → ℝ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hgb : ∀ x ∈ closure Ω, |g x| ≤ M) (hgh : ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) :
    ∃ W W1 W2, LocOut Ω μ c x0 ρ C lam g M H W W1 W2 :=
  h lam hl g M H hM hH hgb hgh

theorem cut_ind {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ Z τ : ℝ} {χ : Eu d → ℝ}
    {χ1 : Eu d → Eu d →L[ℝ] ℝ} {χ2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ}
    (hcut : CutData Ω μ c x0 ρ Z τ χ χ1 χ2) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∀ y, 0 ≤ (Metric.ball x0 ρ).indicator χ y ∧ (Metric.ball x0 ρ).indicator χ y ≤ 1) ∧
    (∀ y ∈ Metric.ball x0 (min τ ρ), (Metric.ball x0 ρ).indicator χ y = 1) ∧
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
      |(Metric.ball x0 ρ).indicator χ x - (Metric.ball x0 ρ).indicator χ y| ≤
        (Z * (2 * ρ) ^ (1 - μ) + 1 * (2 / ρ) ^ μ) * ‖x - y‖ ^ μ) := by
  have hρ := hcut.hρ
  have hZ : 0 ≤ Z := hcut.c2b.hK
  have hL : 0 ≤ Z * (2 * ρ) ^ (1 - μ) := mul_nonneg hZ (Real.rpow_nonneg (by linarith) _)
  refine ⟨fun y => ?_, fun y hy => ?_, fun x hx y hy => ?_⟩
  · by_cases hyb : y ∈ Metric.ball x0 ρ
    · rw [Set.indicator_of_mem hyb]; exact hcut.rng y
    · rw [Set.indicator_of_notMem hyb]; exact ⟨le_rfl, zero_le_one⟩
  · have hyb : y ∈ Metric.ball x0 ρ := Metric.ball_subset_ball (min_le_right τ ρ) hy
    rw [Set.indicator_of_mem hyb]
    exact hcut.one y (Metric.ball_subset_ball (min_le_left τ ρ) hy)
  · have zc := zext_hol (X := closure Ω) (x0 := x0) hρ hμ0 zero_le_one hL (f := χ)
      (fun x _ => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hcut.rng x).1, (hcut.rng x).2])
      (fun x hx y hy => by
        have h1 : dist x x0 < ρ := hx.1
        have h2 : dist y x0 < ρ := hy.1
        have hd : ‖x - y‖ ≤ (2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ := by
          refine lip_le_hol (norm_nonneg _) ?_ hμ0 hμ1
          rw [← dist_eq_norm]; linarith [dist_triangle_right x y x0]
        calc ‖χ x - χ y‖ ≤ Z * ‖x - y‖ := hcut.c2b.lip x hx y hy
          _ ≤ Z * ((2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ) := mul_le_mul_of_nonneg_left hd hZ
          _ = Z * (2 * ρ) ^ (1 - μ) * ‖x - y‖ ^ μ := by ring)
      (fun y hy hf => (hcut.van y hy hf).1)
    have := zc.2 x hx y hy
    rwa [Real.norm_eq_abs] at this

end GlobalS

section SolveS

variable {d : ℕ}

set_option maxHeartbeats 2000000 in
theorem global_solver {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) {c : Eu d → Eu d}
    (t : Finset (Eu d)) (ρ Z τ : Eu d → ℝ) (χ : Eu d → Eu d → ℝ) (χ1 : Eu d → Eu d → Eu d →L[ℝ] ℝ)
    (χ2 : Eu d → Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ) {lam0 C : ℝ} (hl : 1 ≤ lam0) (hC : 0 ≤ C)
    (hcut : ∀ p ∈ t, CutData Ω μ c p (ρ p) (Z p) (τ p) (χ p) (χ1 p) (χ2 p))
    (hloc : ∀ p ∈ t, LocSol Ω μ c p (ρ p) lam0 C)
    (hcov : closure Ω ⊆ ⋃ p ∈ t, Metric.ball p (min (τ p) (ρ p))) :
    ∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : Eu d → ℝ) (M H : ℝ), HB (closure Ω) μ M H g →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
      (∀ x ∈ closure Ω, lam * u x -
        (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
        ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpos : ∀ p ∈ t, 0 ≤ Z p ∧ 0 ≤ (2 * ρ p) ^ (1 - μ) ∧ 0 ≤ (2 / ρ p) ^ μ := fun p hp => by
    have hρ := (hcut p hp).hρ
    exact ⟨(hcut p hp).c2b.hK, Real.rpow_nonneg (by linarith) _, Real.rpow_nonneg (by positivity) _⟩
  have hc0 : ∀ p ∈ t, 0 ≤ Z p * (2 * ρ p) ^ (1 - μ) + 1 * (2 / ρ p) ^ μ := fun p hp => by
    obtain ⟨a, b, e⟩ := hpos p hp; positivity
  have hκ0 : ∀ p ∈ t, 0 ≤ 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ)) := fun p hp => by
    obtain ⟨a, b, e⟩ := hpos p hp; positivity
  have hK00 : ∀ p ∈ t,
      0 ≤ C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ + Z p * (2 / ρ p) ^ μ)) :=
    fun p hp => by obtain ⟨a, b, e⟩ := hpos p hp; positivity
  have hHS0 : 0 ≤ ∑ p ∈ t, (Z p * (2 * ρ p) ^ (1 - μ) + 1 * (2 / ρ p) ^ μ) := Finset.sum_nonneg hc0
  have hK1 : 0 ≤ ∑ p ∈ t, 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ)) :=
    Finset.sum_nonneg hκ0
  obtain ⟨cc, hcc⟩ : ∃ v : ℝ, v = (1 + ∑ p ∈ t, (Z p * (2 * ρ p) ^ (1 - μ) + 1 * (2 / ρ p) ^ μ)) *
      ∑ p ∈ t, C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ + Z p * (2 / ρ p) ^ μ)) :=
    ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hcc]; exact mul_nonneg (by linarith) (Finset.sum_nonneg hK00)
  obtain ⟨Q, hQ⟩ : ∃ v : ℝ, v = (∑ p ∈ t, 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ))) *
      C * (1 + ∑ p ∈ t, (Z p * (2 * ρ p) ^ (1 - μ) + 1 * (2 / ρ p) ^ μ)) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact mul_nonneg (mul_nonneg hK1 hC) (by linarith)
  refine ⟨max lam0 ((2 * Q + 1) ^ 2), le_max_of_le_left hl, fun lam hlam g M H hg => ?_⟩
  have hlam0 : lam0 ≤ lam := (le_max_left _ _).trans hlam
  have hlam1 : 1 ≤ lam := hl.trans hlam0
  have hlpos : 0 < lam := by linarith
  have hℓ0 : 0 < 1 / lam := by positivity
  have hw1 : 1 ≤ lam ^ (μ / 2) := Real.one_le_rpow hlam1 (by linarith)
  have hs0 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hℓ0.le _
  have hsq : ((1 / lam) ^ (1 / 2 : ℝ)) ^ 2 = 1 / lam := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]; norm_num
  have hQs : Q * (1 / lam) ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    have hA : (2 * Q + 1) ^ 2 ≤ lam := (le_max_right _ _).trans hlam
    have h1 : ((1 / lam) ^ (1 / 2 : ℝ) * (2 * Q + 1)) ^ 2 ≤ 1 := by
      rw [mul_pow, hsq, div_mul_eq_mul_div, one_mul, div_le_one hlpos]; exact hA
    have h3 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) * (2 * Q + 1) := by positivity
    have h2 : (1 / lam) ^ (1 / 2 : ℝ) * (2 * Q + 1) ≤ 1 := by nlinarith
    nlinarith
  -- cutoff indicators and the quotient by their sum
  have hci := fun p (hp : p ∈ t) => cut_ind (hcut p hp) hμ0.le hμ1.le
  obtain ⟨hS1, -, hquot⟩ := quot_cover (X := closure Ω) (μ := μ) t
    (fun p => (Metric.ball p (ρ p)).indicator (χ p)) (fun p => Z p * (2 * ρ p) ^ (1 - μ) + 1 * (2 / ρ p) ^ μ)
    hc0 (fun p hp => (hci p hp).1) (fun p hp x hx y hy => (hci p hp).2.2 x hx y hy)
    (fun x hx => by
      have := hcov hx
      rw [Set.mem_iUnion₂] at this
      obtain ⟨p, hp, hxp⟩ := this
      exact ⟨p, hp, (hci p hp).2.1 x hxp⟩)
  -- the selected local solutions (canonical constants)
  have hsel : ∀ p ∈ t, ∀ g' : Eu d → ℝ, ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ)
      (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      HB (closure Ω) μ (hbM (closure Ω) g') (hbH (closure Ω) μ g') g' →
      LocOut Ω μ c p (ρ p) C lam (fun x => g' x / ∑ q ∈ t, (Metric.ball q (ρ q)).indicator (χ q) x)
        (hbM (closure Ω) g')
        (hbH (closure Ω) μ g' + hbM (closure Ω) g' * ∑ q ∈ t, (Z q * (2 * ρ q) ^ (1 - μ) + 1 * (2 / ρ q) ^ μ))
        W W1 W2 := by
    intro p hp g'
    by_cases h : HB (closure Ω) μ (hbM (closure Ω) g') (hbH (closure Ω) μ g') g'
    · obtain ⟨hM', hH', hb', hh'⟩ := hquot g' _ _ h
      obtain ⟨W, W1, W2, hW⟩ := (hloc p hp).out hlam0 _ _ _ hM' hH' hb' hh'
      exact ⟨W, W1, W2, fun _ => hW⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
  choose! W W1 W2 hW using hsel
  have hss := series_solve hΩ subset_closure frontier_subset_closure (μ := μ) (w := lam ^ (μ / 2))
    (q := 1 / 2) (lam := lam) (by positivity) (by norm_num) (by norm_num) c (fun _ => 0) (fun _ => halfLap)
    (fun g' x => ∑ p ∈ t, (Metric.ball p (ρ p)).indicator (prodP (χ p) (W p g')) x)
    (fun g' x => ∑ p ∈ t, (Metric.ball p (ρ p)).indicator (prodP1 (χ p) (W p g') (χ1 p) (W1 p g')) x)
    (fun g' x => ∑ p ∈ t,
      (Metric.ball p (ρ p)).indicator (prodP2 (χ p) (W p g') (χ1 p) (W1 p g') (χ2 p) (W2 p g')) x)
    (c0 := cc) (c1 := cc) (c2 := cc) (c3 := cc) (c4 := cc) (c5 := cc)
    hcc0 hcc0 hcc0 hcc0 hcc0 hcc0 ?hR hg
  case hR =>
    intro g' M' H' hg'
    obtain ⟨hcan, hMle, hHle⟩ := hb_canon hg'
    have hMs0 : 0 ≤ hbM (closure Ω) g' := hcan.1
    have hHs0 : 0 ≤ hbH (closure Ω) μ g' := hcan.2.1
    have hM'0 : 0 ≤ M' := hg'.1
    have hH'0 : 0 ≤ H' := hg'.2.1
    set HS := ∑ q ∈ t, (Z q * (2 * ρ q) ^ (1 - μ) + 1 * (2 / ρ q) ^ μ) with hHS
    set Ns := lam ^ (μ / 2) * hbM (closure Ω) g' + (hbH (closure Ω) μ g' + hbM (closure Ω) g' * HS) with hNs
    have hNs0 : 0 ≤ Ns := by positivity
    have hNsle : Ns ≤ (1 + HS) * (lam ^ (μ / 2) * M' + H') := by
      have a1 : lam ^ (μ / 2) * hbM (closure Ω) g' ≤ lam ^ (μ / 2) * M' :=
        mul_le_mul_of_nonneg_left hMle (by linarith)
      have a0 : M' ≤ lam ^ (μ / 2) * M' := le_mul_of_one_le_left hM'0 hw1
      have a2 : hbM (closure Ω) g' * HS ≤ lam ^ (μ / 2) * M' * HS :=
        mul_le_mul_of_nonneg_right (hMle.trans a0) hHS0
      have a3 : 0 ≤ H' * HS := mul_nonneg hH'0 hHS0
      have e : (1 + HS) * (lam ^ (μ / 2) * M' + H') = lam ^ (μ / 2) * M' + H' + lam ^ (μ / 2) * M' * HS + H' * HS := by
        ring
      rw [e]; linarith
    have hWp := fun p (hp : p ∈ t) => hW p hp g' hcan
    have hglue := fun p (hp : p ∈ t) => patch_glue (hcut p hp) hμ0.le hμ1.le (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (hWp p hp).1 (hWp p hp).2.2.1 (hWp p hp).2.1 (hWp p hp).2.2.2.1 (hWp p hp).2.2.2.2
    have hlin := fun p (hp : p ∈ t) => patch_lin (hcut p hp) hμ0.le hμ1.le hC hlam1 hNs0
      (hWp p hp).1 (hWp p hp).2.2.1 (hWp p hp).2.1 (hWp p hp).2.2.2.1 (hWp p hp).2.2.2.2
    choose! eM eH heM heH hκb hsup hhol using hlin
    have hsumN : ∀ a : Eu d → ℝ, (∀ p ∈ t, a p ≤ C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ +
        Z p * (2 / ρ p) ^ μ)) * Ns) → ∑ p ∈ t, a p ≤ cc * (lam ^ (μ / 2) * M' + H') := by
      intro a ha
      calc ∑ p ∈ t, a p ≤ ∑ p ∈ t, C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ +
            Z p * (2 / ρ p) ^ μ)) * Ns := Finset.sum_le_sum ha
        _ = (∑ p ∈ t, C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ +
            Z p * (2 / ρ p) ^ μ))) * Ns := by rw [Finset.sum_mul]
        _ ≤ (∑ p ∈ t, C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) + (2 / ρ p) ^ μ +
            Z p * (2 / ρ p) ^ μ))) * ((1 + HS) * (lam ^ (μ / 2) * M' + H')) :=
          mul_le_mul_of_nonneg_left hNsle (Finset.sum_nonneg hK00)
        _ = cc * (lam ^ (μ / 2) * M' + H') := by rw [hcc]; ring
    have hsumH : ∀ (a : Eu d → ℝ) (r : ℝ), 0 ≤ r → (∀ p ∈ t, a p ≤ C * (4 * (1 + Z p + Z p * (2 * ρ p) ^ (1 - μ) +
        (2 / ρ p) ^ μ + Z p * (2 / ρ p) ^ μ)) * Ns * r) → ∑ p ∈ t, a p ≤ cc * (lam ^ (μ / 2) * M' + H') * r := by
      intro a r hr ha
      have := hsumN (fun p => a p / r)
      rcases hr.lt_or_eq with hr | hr
      · have h2 := this (fun p hp => by rw [div_le_iff₀ hr]; exact ha p hp)
        rw [← Finset.sum_div, div_le_iff₀ hr] at h2
        exact h2
      · subst hr
        simp only [mul_zero] at ha ⊢
        exact Finset.sum_nonpos ha
    refine ⟨fun x hx => ⟨HasFDerivAt.fun_sum fun p hp => ((hglue p hp).1 x hx).1,
        HasFDerivAt.fun_sum fun p hp => ((hglue p hp).1 x hx).2⟩, fun x hx => ?_, fun x hx => ⟨?_, ?_, ?_⟩,
      fun x hx y hy => ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ContinuousLinearMap.sum_apply]
      exact Finset.sum_eq_zero fun p hp => (hglue p hp).2.1 x hx
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (hsumN _ fun p hp => (hsup p hp x hx).1)
    · exact (norm_sum_le _ _).trans (hsumN _ fun p hp => (hsup p hp x hx).2.1)
    · exact (norm_sum_le _ _).trans (hsumN _ fun p hp => (hsup p hp x hx).2.2.1)
    · have hp0 : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (hsumH _ _ hp0 fun p hp => (hhol p hp x hx y hy).1)
    · have hp0 : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (hsumH _ _ hp0 fun p hp => (hhol p hp x hx y hy).2.1)
    · have hp0 : 0 ≤ ‖x - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (hsumH _ _ hp0 fun p hp => (hhol p hp x hx y hy).2.2.1)
    · -- the residual is `Σ_p Ẽ_p` on closure Ω
      refine ⟨∑ p ∈ t, eM p * Ns, ∑ p ∈ t, eH p * Ns, HB.congr (f := fun x => ∑ p ∈ t,
        (Metric.ball p (ρ p)).indicator (ecut (W p g') (χ1 p) (W1 p g') (χ2 p)) x)
        ⟨Finset.sum_nonneg fun p hp => mul_nonneg (heM p hp) hNs0,
         Finset.sum_nonneg fun p hp => mul_nonneg (heH p hp) hNs0,
         fun x hx => (Finset.abs_sum_le_sum_abs _ _).trans
           (Finset.sum_le_sum fun p hp => (hsup p hp x hx).2.2.2),
         fun x hx y hy => by
           rw [← Finset.sum_sub_distrib, Finset.sum_mul]
           exact (Finset.abs_sum_le_sum_abs _ _).trans
             (Finset.sum_le_sum fun p hp => (hhol p hp x hx y hy).2.2.2)⟩ ?_, ?_⟩
      · intro x hx
        have hS : (∑ q ∈ t, (Metric.ball q (ρ q)).indicator (χ q) x) ≠ 0 := by
          have := hS1 x hx; linarith
        have e := fun p (hp : p ∈ t) => (hglue p hp).2.2.1 x hx
        show _ = g' x - (lam * ∑ p ∈ t, _ - (0 : (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ) _ - halfLap (∑ p ∈ t, _))
        rw [ContinuousLinearMap.zero_apply, sub_zero, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        simp only [halfLap_apply]
        rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_div_cancel₀ _ hS]
        ring
      · calc lam ^ (μ / 2) * ∑ p ∈ t, eM p * Ns + ∑ p ∈ t, eH p * Ns
            = (∑ p ∈ t, (lam ^ (μ / 2) * eM p + eH p)) * Ns := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
              exact Finset.sum_congr rfl fun p _ => by ring
          _ ≤ (∑ p ∈ t, 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ)) * C *
              (1 / lam) ^ (1 / 2 : ℝ)) * Ns := mul_le_mul_of_nonneg_right (Finset.sum_le_sum hκb) hNs0
          _ = (∑ p ∈ t, 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ))) * C *
              (1 / lam) ^ (1 / 2 : ℝ) * Ns := by simp only [Finset.sum_mul]
          _ ≤ (∑ p ∈ t, 4 * d * (Z p + Z p * (2 / ρ p) ^ μ + Z p * (2 * ρ p) ^ (1 - μ))) * C *
              (1 / lam) ^ (1 / 2 : ℝ) * ((1 + HS) * (lam ^ (μ / 2) * M' + H')) :=
              mul_le_mul_of_nonneg_left hNsle (by positivity)
          _ = Q * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M' + H') := by rw [hQ]; ring
          _ ≤ 1 / 2 * (lam ^ (μ / 2) * M' + H') :=
              mul_le_mul_of_nonneg_right hQs (by positivity)
  obtain ⟨u, u1, u2, hd, hbc, heq, hb, hh⟩ := hss
  refine ⟨u, u1, u2, hd, hbc, fun x hx => ?_, ⟨_, fun x hx => hb x hx⟩, ⟨cc * (lam ^ (μ / 2) * M + H) / (1 - 1 / 2),
    fun x hx y hy => ?_⟩⟩
  · have := heq x hx
    rwa [ContinuousLinearMap.zero_apply, sub_zero, halfLap_apply] at this
  · obtain ⟨h0, h1, h2⟩ := hh x hx y hy
    refine ⟨h0.trans_eq (by ring), h1.trans_eq (by ring), h2.trans_eq (by ring)⟩

end SolveS

/-- The conclusion of `global_solver`, as a Prop interface. -/
def GSol {d : ℕ} (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) : Prop :=
  ∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : Eu d → ℝ) (M H : ℝ), HB (closure Ω) μ M H g →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
      (∀ x ∈ closure Ω, lam * u x -
        (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
        ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)

lemma hol_contOn {d : ℕ} {F : Type*} [SeminormedAddCommGroup F] {f : Eu d → F} {X : Set (Eu d)}
    {B μ : ℝ} (hμ : 0 < μ) (h : ∀ x ∈ X, ∀ y ∈ X, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ μ) :
    ContinuousOn f X := by
  intro x hx
  have hg : Tendsto (fun y : Eu d => B * ‖y - x‖ ^ μ) (𝓝[X] x) (𝓝 0) := by
    have hc : Continuous (fun y : Eu d => B * ‖y - x‖ ^ μ) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hμ.le)
    have h0 : Tendsto (fun y : Eu d => B * ‖y - x‖ ^ μ) (𝓝[X] x) (𝓝 (B * ‖x - x‖ ^ μ)) :=
      (hc.tendsto x).mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hμ.ne'] using h0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h y hy x hx

theorem glue_def {d : ℕ} {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {c : Eu d → Eu d} (hG : GSol Ω μ c) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : BoundedContinuousFunction (closure Ω) ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ0.le⟩ ⇑h →
        ∃ fg ∈ EthierKurtz.obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by
  obtain ⟨lam1, hl1, hsol⟩ := hG
  refine ⟨lam1, by linarith, fun h C hC => ?_⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Eu d → ℝ, g = EthierKurtz.closedRegionRestriction h := ⟨_, rfl⟩
  have hgx : ∀ x (hx : x ∈ closure Ω), g x = h ⟨x, hx⟩ := fun x hx => by
    rw [hgdef, EthierKurtz.closedRegionRestriction, dif_pos hx]
  have hHB : HB (closure Ω) μ ‖h‖ C g := by
    refine ⟨norm_nonneg _, C.2, fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [hgx x hx, ← Real.norm_eq_abs]; exact h.norm_coe_le_norm _
    · rw [hgx x hx, hgx y hy, ← Real.dist_eq]
      have : dist (h ⟨x, hx⟩) (h ⟨y, hy⟩) ≤ (C : ℝ) * dist (⟨x, hx⟩ : closure Ω) ⟨y, hy⟩ ^ μ :=
        hC.dist_le ⟨x, hx⟩ ⟨y, hy⟩
      simpa [Subtype.dist_eq, dist_eq_norm] using this
  obtain ⟨u, u1, u2, hder, hbc, heq, ⟨B0, hB0⟩, ⟨B, hB⟩⟩ := hsol lam1 le_rfl g ‖h‖ C hHB
  have hcu : ContinuousOn u (closure Ω) :=
    hol_contOn hμ0 (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hB x hx y hy).1)
  have hcu1 : ContinuousOn u1 (closure Ω) := hol_contOn hμ0 (fun x hx y hy => (hB x hx y hy).2.1)
  have hcu2 : ContinuousOn u2 (closure Ω) := hol_contOn hμ0 (fun x hx y hy => (hB x hx y hy).2.2)
  obtain ⟨f, hf⟩ : ∃ f : BoundedContinuousFunction (closure Ω) ℝ, ∀ x : closure Ω, f x = u x :=
    ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => u x, hcu.restrict⟩ (2 * B0) (fun x y => by
      have h1 := abs_le.1 (hB0 x x.2).1
      have h2 := abs_le.1 (hB0 y y.2).1
      show dist (u x) (u y) ≤ 2 * B0
      rw [Real.dist_eq]; exact abs_le.2 ⟨by linarith, by linarith⟩), fun x => rfl⟩
  have hF : ∀ x ∈ closure Ω, EthierKurtz.closedRegionRestriction f x = u x := fun x hx => by
    rw [EthierKurtz.closedRegionRestriction, dif_pos hx, hf]
  have hFev : ∀ x ∈ Ω, EthierKurtz.closedRegionRestriction f =ᶠ[𝓝 x] u := fun x hx =>
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => hF y (subset_closure hy))
  have hD1 : ∀ x ∈ Ω, HasFDerivAt (EthierKurtz.closedRegionRestriction f) (u1 x) x := fun x hx =>
    (hder x hx).1.congr_of_eventuallyEq (hFev x hx)
  have hfd : ∀ x ∈ Ω, fderiv ℝ (EthierKurtz.closedRegionRestriction f) x = u1 x := fun x hx =>
    (hD1 x hx).fderiv
  have hD2 : ∀ x ∈ Ω, HasFDerivAt (fderiv ℝ (EthierKurtz.closedRegionRestriction f)) (u2 x) x :=
    fun x hx => (hder x hx).2.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) hfd)
  have hD2j : ∀ x ∈ Ω, ∀ v w : Eu d,
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y w) x v = u2 x v w := by
    intro x hx v w
    have hh : HasFDerivAt (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y w)
        ((ContinuousLinearMap.apply ℝ ℝ w).comp (u2 x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x (hD2 x hx)
    rw [hh.fderiv]; rfl
  have hcont2 : ContDiffOn ℝ 2 (EthierKurtz.closedRegionRestriction f) Ω := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from one_add_one_eq_two.symm,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hD1 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hD2 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (hcu2.mono subset_closure).congr (fun x hx => (hD2 x hx).fderiv)
  have hCH : ∀ i j : Fin d, EthierKurtz.ComponentHolder Ω μ (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) := by
    intro i j
    have hval := fun x hx => hD2j x hx (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
    refine ⟨?_, 1, 2 * max B 0, one_pos, by positivity, fun ρ hρ _ x z _ y hy w hw => ?_⟩
    · have hc := hcu2.mono (subset_closure (s := Ω))
      exact ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).congr hval
    · dsimp only
      have hy' := connectedComponentIn_subset _ _ hy
      have hw' := connectedComponentIn_subset _ _ hw
      rw [hval y hy'.1, hval w hw'.1]
      have e : u2 y (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) -
          u2 w (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
          (u2 y - u2 w) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by simp
      rw [e, ← Real.norm_eq_abs]
      have hyw : ‖y - w‖ ≤ 2 * ρ := by
        have a1 : dist y x < ρ := hy'.2
        have a2 : dist w x < ρ := hw'.2
        rw [← dist_eq_norm]; linarith [dist_triangle_right y w x]
      have hpow : ‖y - w‖ ^ μ ≤ 2 * ρ ^ μ := by
        calc ‖y - w‖ ^ μ ≤ (2 * ρ) ^ μ := Real.rpow_le_rpow (norm_nonneg _) hyw hμ0.le
          _ = 2 ^ μ * ρ ^ μ := Real.mul_rpow (by norm_num) hρ.le
          _ ≤ 2 * ρ ^ μ := by
            gcongr
            calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
              _ = 2 := Real.rpow_one 2
      have hB' := (hB y (subset_closure hy'.1) w (subset_closure hw'.1)).2.2
      calc ‖(u2 y - u2 w) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖
          ≤ ‖u2 y - u2 w‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ = ‖u2 y - u2 w‖ := by simp [EuclideanSpace.norm_single]
        _ ≤ B * ‖y - w‖ ^ μ := hB'
        _ ≤ max B 0 * ‖y - w‖ ^ μ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ max B 0 * (2 * ρ ^ μ) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
        _ = 2 * max B 0 * ρ ^ μ := by ring
  refine ⟨(f, lam1 • f - h), ?_, sub_sub_cancel _ _⟩
  simp only [EthierKurtz.obliqueDiffusionGraph, Set.mem_setOf_eq]
  refine ⟨⟨hcont2, hCH⟩, fun x hx => ?_, fun x => u1 x, hcu1.restrict, fun x hx => (hfd x hx).symm,
    fun x hx => hbc x hx⟩
  have hxc : x ∈ closure Ω := subset_closure hx
  have h1 : EthierKurtz.closedRegionRestriction (lam1 • f - h) x = lam1 * u x - g x := by
    rw [EthierKurtz.closedRegionRestriction, dif_pos hxc, hgx x hxc]
    simp [hf]
  have hs : ∑ i : Fin d, ∑ j : Fin d, (1 : Matrix (Fin d) (Fin d) ℝ) i j *
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      ∑ i : Fin d, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    exact Finset.sum_congr rfl (fun i _ => hD2j x hx _ _)
  rw [h1, hs, map_zero, add_zero]
  have := heq x hxc
  linarith

end ObliqueLib

open scoped BoundedContinuousFunction

open EthierKurtz in
theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpiece : ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ))) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ0.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by
  apply ObliqueLib.glue_def hopen hμ0 hμ1.le
  have hcpt : IsCompact (closure Ω) := hbounded.isCompact_closure
  obtain ⟨t, ρ, Z, τ, χ, χ1, χ2, lam0, C, hl, hC, -, hcut, hloc, hcov⟩ :=
    ObliqueLib.finite_cover (μ := μ) (c := c) hcpt (fun x0 hx0 => by
      obtain ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, ⟨a1, a2, a3, a4, a5, a6, a7, k1, k2, k3, k4, k5, k6⟩, hl, hC, hloc⟩ :=
        hpiece x0 hx0
      exact ⟨ρ, Z, τ, χ, χ1, χ2, lam0, C, ⟨a1, a2, a3, a4, a5, a6, a7, ⟨k1, k2, k3, k4, k5, k6⟩⟩, hl, hC, hloc⟩)
  exact ObliqueLib.global_solver hopen hμ0 hμ1 t ρ Z τ χ χ1 χ2 hl hC hcut hloc hcov
