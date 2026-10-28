-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.infDist_exactStates_eq
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T04:34:17.541543+00:00
-- url     : https://prove2.me/submissions/69ba3fcb-83da-4ac1-ba36-9b9a116f1d2d

import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterSirkTrotterKato

open BookProof BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport BookProof.BrstReducedTransfer
open Filter Topology
open scoped InnerProductSpace

universe u

/-- core: a functional vanishing on the whole orbit kills `T x`. -/
theorem brt_core {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : UnboundedSelfAdjoint H) (x : T.domain) (φ : H →L[ℂ] ℂ)
    (h : ∀ t : ℝ, φ (T.stoneU t (x : H)) = 0) : φ (T.op x) = 0 := by
  have hx0 : φ (x : H) = 0 := by simpa using h 0
  -- bound for each n
  have hb : ∀ n : ℝ, ‖φ (T.yosida n (x : H))‖ ≤ ‖φ‖ * ‖T.op x - T.yosida n (x : H)‖ := by
    intro n
    set g : ℝ → ℂ := fun s => φ (T.approxU n s (x : H)) with hg
    have hd : HasDerivAt g (φ ((T.approxU n 0 * T.yosidaGen n) (x : H))) 0 :=
      (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (T.hasDerivAt_approxU_apply n 0 (x : H))
    have h1 : T.approxU n 0 = 1 := by simp [UnboundedSelfAdjoint.approxU]
    rw [h1, one_mul, UnboundedSelfAdjoint.yosidaGen] at hd
    have hs := hd.tendsto_slope_zero
    have hg0 : g 0 = 0 := by simp [hg, h1, hx0]
    have hbound : ∀ t : ℝ, t ≠ 0 → ‖t⁻¹ • (g (0 + t) - g 0)‖ ≤ ‖φ‖ * ‖T.op x - T.yosida n (x : H)‖ := by
      intro t ht
      rw [zero_add, hg0, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
      have e1 : g t = φ (T.approxU n t (x : H)) - φ (T.stoneU t (x : H)) := by
        rw [h t, sub_zero]
      have e2 : ‖g t‖ ≤ ‖φ‖ * (|t| * ‖T.op x - T.yosida n (x : H)‖) := by
        rw [e1, ← map_sub]
        refine (φ.le_opNorm _).trans ?_
        gcongr
        rw [norm_sub_rev]
        exact T.norm_stoneU_sub_approxU_le n t x
      have hta : 0 < |t| := abs_pos.mpr ht
      rw [inv_mul_le_iff₀ hta]
      nlinarith [e2]
    have hlim := hs.norm
    have hle : ‖φ ((-Complex.I • T.yosida n) (x : H))‖ ≤ ‖φ‖ * ‖T.op x - T.yosida n (x : H)‖ := by
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hbound t ht
    simpa [norm_smul] using hle
  -- pass to the limit along n = k+1
  have hy := T.yosida_tendsto x
  have hA : Tendsto (fun k : ℕ => ‖φ (T.yosida ((k : ℝ) + 1) (x : H))‖) atTop (𝓝 ‖φ (T.op x)‖) :=
    ((φ.continuous.tendsto _).comp hy).norm
  have hB : Tendsto (fun k : ℕ => ‖φ‖ * ‖T.op x - T.yosida ((k : ℝ) + 1) (x : H)‖) atTop (𝓝 (‖φ‖ * 0)) := by
    refine Tendsto.const_mul _ ?_
    have := ((tendsto_const_nhds (x := T.op x)).sub hy).norm
    simpa using this
  have hle : ‖φ (T.op x)‖ ≤ ‖φ‖ * 0 := le_of_tendsto_of_tendsto' hA hB (fun k => hb _)
  simpa using hle

abbrev HH : Type := EuclideanSpace ℂ (Fin 2)
noncomputable def e0 : HH := EuclideanSpace.single 0 1
noncomputable def e1 : HH := EuclideanSpace.single 1 1

lemma in00 : ⟪e0, e0⟫_ℂ = 1 := by simp [e0]
lemma in01 : ⟪e0, e1⟫_ℂ = 0 := by
  rw [e0, e1, EuclideanSpace.inner_single_left]; simp [EuclideanSpace.single_apply]
lemma in10 : ⟪e1, e0⟫_ℂ = 0 := by
  rw [e0, e1, EuclideanSpace.inner_single_left]; simp [EuclideanSpace.single_apply]
lemma in11 : ⟪e1, e1⟫_ℂ = 1 := by simp [e0, e1]

/-- rank-one projection onto `e0` -/
noncomputable def AA : HH →L[ℂ] HH := (innerSL ℂ e0).smulRight e0

lemma AA_apply (y : HH) : AA y = ⟪e0, y⟫_ℂ • e0 := rfl

noncomputable def TT : UnboundedSelfAdjoint HH where
  domain := ⊤
  op := (AA : HH →ₗ[ℂ] HH) ∘ₗ (⊤ : Submodule ℂ HH).subtype
  denseDomain := by simp
  symmetric := by
    intro p q
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe, AA_apply,
      inner_smul_left, inner_smul_right, ← inner_conj_symm (p : HH) e0]
    ring
  selfAdjoint := by
    ext phi
    simp only [adjointDomain, Set.mem_ofPred_eq, Submodule.top_coe, Set.mem_univ, iff_true]
    refine ⟨AA phi, fun p => ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe, AA_apply,
      inner_smul_left, inner_smul_right, ← inner_conj_symm (p : HH) e0]
    ring

noncomputable def xx : HH := e0 + e1
noncomputable def φφ : HH →L[ℂ] ℂ := innerSL ℂ (e0 - e1)

lemma φφ_xx : φφ xx = 0 := by
  simp only [φφ, xx, innerSL_apply_apply, inner_add_right, inner_sub_left, in00, in01, in10, in11]
  ring
lemma φφ_e0 : φφ e0 = 1 := by
  simp only [φφ, innerSL_apply_apply, inner_sub_left, in00, in10]
  ring

/-- the key consequence: the orbit of `xx` leaves `ker φφ`. -/
lemma orbit_leaves : ¬ ∀ t : ℝ, φφ (TT.stoneU t xx) = 0 := by
  intro h
  have := brt_core TT ⟨xx, Submodule.mem_top⟩ φφ h
  have e : TT.op ⟨xx, Submodule.mem_top⟩ = e0 := by
    show AA xx = e0
    rw [AA_apply, xx, inner_add_right, in00, in01, add_zero, one_smul]
  rw [e, φφ_e0] at this
  exact one_ne_zero this

noncomputable def Om2 : HH →L[ℂ] HH := (innerSL ℂ e0).smulRight xx

lemma exact_sub : ∀ z ∈ exactStates Om2, φφ z = 0 := by
  have hle : exactStates Om2 ≤ LinearMap.ker (φφ : HH →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rintro _ ⟨y, rfl⟩
      simp [Om2, φφ_xx]
    · exact isClosed_eq φφ.continuous continuous_const
  intro z hz
  exact hle hz

lemma xx_mem : xx ∈ exactStates Om2 := by
  have h := mem_exactStates_of_apply Om2 e0
  have e : Om2 e0 = xx := by
    simp only [Om2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, in00, one_smul]
  rwa [e] at h

lemma closed_mem {z : HH} (hz : Metric.infDist z (exactStates Om2) = 0) :
    z ∈ exactStates Om2 := by
  have hne : ((exactStates Om2 : Set HH)).Nonempty := ⟨0, Submodule.zero_mem _⟩
  have := (Metric.mem_closure_iff_infDist_zero hne).mpr hz
  rwa [(isClosed_exactStates Om2).closure_eq] at this

theorem solution : ¬ (∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Om : H →L[ℂ] H) (U : ℝ → (H →L[ℂ] H)) (_hzero : ∀ x : H, U 0 x = x)
    (_hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (_hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H),
    Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om)) := by
  intro h
  apply orbit_leaves
  intro t
  have h2 := h Om2 (fun s => TT.stoneU s) (fun x => by simp)
    (fun s r x => TT.stoneU_apply_stoneU s r x) (fun r x => TT.norm_stoneU_apply r x) t xx
  rw [Metric.infDist_zero_of_mem xx_mem] at h2
  exact exact_sub _ (closed_mem h2)
