-- Prove2me | solution 1 for BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:21:07.366101+00:00
-- url     : https://prove2.me/submissions/e2aec28f-37f8-4ef4-9d86-3e981717917d

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. -/
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFriedrichsExtension
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000

/-!
# The general Stone theorem, part V: `A` generates `e^{-itA}`

We show that the strongly continuous unitary group `U t = e^{-itA}` constructed in
`BookProof.ChapterStoneUnitary` leaves the domain of `A` invariant, commutes with `A`
there, and satisfies the Schrödinger equation `d/dt U t x = -i A (U t x)` for every `x`
in the domain.
-/

open scoped InnerProductSpace
open Filter Topology NormedSpace

namespace BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnboundedSelfAdjoint

variable (T : UnboundedSelfAdjoint H)

/-! ## Commutation with the resolvent and invariance of the domain -/

theorem yosidaGen_commute_resCLM (n l : ℝ) : Commute (T.yosidaGen n) (T.resCLM l) := by
  have h : ∀ a b : ℝ, Commute (T.resCLM a) (T.resCLM b) := T.resCLM_commute
  have hy : Commute (T.yosida n) (T.resCLM l) := by
    unfold yosida
    refine Commute.add_left (Commute.smul_left ?_ _) (Commute.smul_left ?_ _)
    · exact h _ _
    · exact (h _ _).mul_left (h _ _)
  exact hy.smul_left _

theorem approxU_commute_resCLM (n t l : ℝ) : Commute (T.approxU n t) (T.resCLM l) :=
  (((T.yosidaGen_commute_resCLM n l).smul_left t)).exp_left

theorem stoneU_commute_resCLM (t l : ℝ) (y : H) :
    T.stoneU t (T.resCLM l y) = T.resCLM l (T.stoneU t y) := by
  have h1 : Tendsto (fun k : ℕ => T.approxU ((k : ℝ) + 1) t (T.resCLM l y)) atTop
      (𝓝 (T.stoneU t (T.resCLM l y))) := T.tendsto_stoneU t _
  have h2 : Tendsto (fun k : ℕ => T.resCLM l (T.approxU ((k : ℝ) + 1) t y)) atTop
      (𝓝 (T.resCLM l (T.stoneU t y))) :=
    ((T.resCLM l).continuous.tendsto _).comp (T.tendsto_stoneU t y)
  have heq : (fun k : ℕ => T.approxU ((k : ℝ) + 1) t (T.resCLM l y))
      = fun k : ℕ => T.resCLM l (T.approxU ((k : ℝ) + 1) t y) := by
    funext k
    exact congrArg (fun (S : H →L[ℂ] H) => S y) ((T.approxU_commute_resCLM ((k : ℝ) + 1) t l).eq)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- The unitary group leaves the domain of `A` invariant. -/
theorem stoneU_mem_domain (t : ℝ) (x : T.domain) : T.stoneU t (x : H) ∈ T.domain := by
  have hx : ((T.res 1 (T.shift 1 x) : T.domain) : H) = (x : H) := by
    rw [T.res_shift one_ne_zero]
  have h : T.stoneU t (x : H) = T.resCLM 1 (T.stoneU t (T.shift 1 x)) := by
    rw [← T.stoneU_commute_resCLM]
    congr 1
    exact hx.symm
  rw [h]
  exact T.resCLM_mem 1 _

/-- On the domain, the unitary group commutes with `A`. -/
theorem stoneU_op (t : ℝ) (x : T.domain) :
    T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x) := by
  set y : H := T.shift 1 x with hy
  have hx : ((T.res 1 y : T.domain) : H) = (x : H) := T.res_shift one_ne_zero x ▸ rfl
  have hAx : T.op x = y + ((1 : ℂ) * Complex.I) • (x : H) := by
    have h := T.op_res (l := 1) one_ne_zero y
    rw [show ((T.res 1 y : T.domain) : H) = (x : H) from hx] at h
    have hxx : (T.res 1 y : T.domain) = x := by
      have := T.res_shift (l := 1) one_ne_zero x
      simpa [hy] using this
    rw [hxx] at h
    simpa using h
  have hU : T.stoneU t (x : H) = T.resCLM 1 (T.stoneU t y) := by
    rw [← T.stoneU_commute_resCLM]
    congr 1
    exact hx.symm
  have hmem : T.stoneU t (x : H) ∈ T.domain := T.stoneU_mem_domain t x
  have hop : T.op ⟨T.stoneU t (x : H), hmem⟩
      = T.stoneU t y + ((1 : ℂ) * Complex.I) • T.resCLM 1 (T.stoneU t y) := by
    have h := T.op_res (l := 1) one_ne_zero (T.stoneU t y)
    have hcoe : (⟨T.stoneU t (x : H), hmem⟩ : T.domain) = T.res 1 (T.stoneU t y) := by
      apply Subtype.ext
      simpa using hU
    rw [hcoe]
    simpa using h
  rw [hop, ← hU, hAx, map_add, map_smul]

/-! ## The Schrödinger equation -/

/-- A second-order Taylor estimate for the approximating groups. -/
theorem norm_approxU_sub_smul_le (n h : ℝ) (x : H) :
    ‖T.approxU n h x - x - h • T.yosidaGen n x‖
      ≤ (|h| * ‖T.yosida n (T.yosidaGen n x)‖) * |h| := by
  set v : H := T.yosidaGen n x with hv
  set M : ℝ := ‖T.yosida n v‖ with hM
  set g : ℝ → H := fun s => T.approxU n s x - x - s • v with hg
  have hderiv : ∀ s : ℝ, HasDerivAt g (T.approxU n s v - v) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => T.approxU n s x) ((T.approxU n s * T.yosidaGen n) x) s :=
      T.hasDerivAt_approxU_apply n s x
    have h2 : HasDerivAt (fun s : ℝ => s • v) v s := by
      simpa using (hasDerivAt_id s).smul_const v
    convert (h1.sub_const x).sub h2 using 1 <;> first | rfl | (ext u; rfl) | simp [hg, hv]
  have hbound : ∀ s ∈ Set.uIcc (0 : ℝ) h, ‖T.approxU n s v - v‖ ≤ |h| * M := by
    intro s hs
    have hsh : |s| ≤ |h| := by
      rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
        exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
        linarith
    have h0 : ‖T.approxU n s v - v‖ ≤ |s| * ‖T.yosida n v‖ := by
      have := T.norm_approxU_sub_apply_le n 0 s v
      simpa [approxU, yosidaGen] using this
    calc ‖T.approxU n s v - v‖ ≤ |s| * M := h0
      _ ≤ |h| * M := by
          exact mul_le_mul_of_nonneg_right hsh (norm_nonneg _)
  have hmvt : ‖g h - g 0‖ ≤ (|h| * M) * ‖h - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hderiv s).hasDerivWithinAt) hbound (convex_uIcc 0 h)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  exact hmvt

/-- **Stone's equation at `t = 0`**: the generator of `e^{-itA}` is `-iA`. -/
theorem hasDerivAt_stoneU_zero (x : T.domain) :
    HasDerivAt (fun t : ℝ => T.stoneU t (x : H)) ((-Complex.I) • T.op x) 0 := by
  set w : H := (-Complex.I) • T.op x with hw
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- choose an approximation index `k` with `‖A x - A_k x‖` small
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖T.op x - T.yosida ((k : ℝ) + 1) (x : H)‖ < c / 4 := by
    have h := (T.yosida_tendsto x)
    have := Metric.tendsto_atTop.mp h (c / 4) (by linarith)
    obtain ⟨N, hN⟩ := this
    exact ⟨N, by
      have := hN N le_rfl
      rwa [dist_eq_norm, norm_sub_rev] at this⟩
  set n : ℝ := (k : ℝ) + 1 with hn
  set M : ℝ := ‖T.yosida n (T.yosidaGen n (x : H))‖ with hM
  have hMpos : (0 : ℝ) < M + 1 := by positivity
  set δ : ℝ := (c / 4) / (M + 1) with hδ
  have hδpos : 0 < δ := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with h hh
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
  have habs : |h| < δ := hh
  -- three-term estimate
  have e1 : ‖T.stoneU h (x : H) - T.approxU n h (x : H)‖
      ≤ |h| * ‖T.op x - T.yosida n (x : H)‖ := T.norm_stoneU_sub_approxU_le n h x
  have e2 : ‖T.approxU n h (x : H) - (x : H) - h • T.yosidaGen n (x : H)‖ ≤ (|h| * M) * |h| :=
    T.norm_approxU_sub_smul_le n h (x : H)
  have e3 : ‖h • T.yosidaGen n (x : H) - h • w‖ = |h| * ‖T.op x - T.yosida n (x : H)‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    congr 1
    have hstep : T.yosidaGen n (x : H) - w = (-Complex.I) • (T.yosida n (x : H) - T.op x) := by
      rw [hw, yosidaGen]
      simp [smul_sub]
    rw [hstep, norm_smul]
    simp [norm_sub_rev]
  have hsplit : T.stoneU h (x : H) - (x : H) - h • w
      = (T.stoneU h (x : H) - T.approxU n h (x : H))
        + (T.approxU n h (x : H) - (x : H) - h • T.yosidaGen n (x : H))
        + (h • T.yosidaGen n (x : H) - h • w) := by
    abel
  have hMbound : |h| * M ≤ c / 4 := by
    have h1 : |h| * (M + 1) < c / 4 := by
      rw [hδ] at habs
      rw [← lt_div_iff₀ hMpos]
      exact habs
    nlinarith [abs_nonneg h, norm_nonneg (T.yosida n (T.yosidaGen n (x : H)))]
  have hfinal : ‖T.stoneU h (x : H) - (x : H) - h • w‖ ≤ c * ‖h‖ := by
    have hc4 : ‖T.op x - T.yosida n (x : H)‖ ≤ c / 4 := le_of_lt hk
    have hb1 : ‖T.stoneU h (x : H) - T.approxU n h (x : H)‖ ≤ |h| * (c / 4) :=
      e1.trans (mul_le_mul_of_nonneg_left hc4 (abs_nonneg h))
    have hb2 : ‖T.approxU n h (x : H) - (x : H) - h • T.yosidaGen n (x : H)‖ ≤ (c / 4) * |h| :=
      e2.trans (mul_le_mul_of_nonneg_right hMbound (abs_nonneg h))
    have hb3 : ‖h • T.yosidaGen n (x : H) - h • w‖ ≤ |h| * (c / 4) := by
      rw [e3]
      exact mul_le_mul_of_nonneg_left hc4 (abs_nonneg h)
    calc ‖T.stoneU h (x : H) - (x : H) - h • w‖
        ≤ ‖T.stoneU h (x : H) - T.approxU n h (x : H)‖
          + ‖T.approxU n h (x : H) - (x : H) - h • T.yosidaGen n (x : H)‖
          + ‖h • T.yosidaGen n (x : H) - h • w‖ := by
          rw [hsplit]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |h| * (c / 4) + (c / 4) * |h| + |h| * (c / 4) := by
          exact add_le_add (add_le_add hb1 hb2) hb3
      _ ≤ c * ‖h‖ := by
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg h]
  simpa using hfinal

/-- **Stone's equation**: `d/dt e^{-itA} x = -i A e^{-itA} x` for `x` in the domain. -/
theorem hasDerivAt_stoneU (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) (T.stoneU t ((-Complex.I) • T.op x)) t := by
  have hz : HasDerivAt (fun u : ℝ => T.stoneU u (x : H)) ((-Complex.I) • T.op x) (t - t) := by
    simpa using T.hasDerivAt_stoneU_zero x
  have h2 : HasDerivAt (fun s : ℝ => T.stoneU (s - t) (x : H)) ((-Complex.I) • T.op x) t :=
    HasDerivAt.comp_sub_const t t hz
  have h3 : HasDerivAt (fun s : ℝ => T.stoneU t (T.stoneU (s - t) (x : H)))
      (T.stoneU t ((-Complex.I) • T.op x)) t :=
    ((T.stoneU t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  have heq : (fun s : ℝ => T.stoneU t (T.stoneU (s - t) (x : H)))
      = fun s : ℝ => T.stoneU s (x : H) := by
    funext s
    rw [T.stoneU_apply_stoneU]
    have hts : t + (s - t) = s := by ring
    rw [hts]
  rwa [heq] at h3

/-- **The Schrödinger equation** in its final form: for `x` in the domain of the
self-adjoint operator `A`, the orbit `t ↦ e^{-itA} x` stays in the domain and solves
`d/dt (e^{-itA} x) = -i A (e^{-itA} x)`. -/
theorem hasDerivAt_stoneU_op (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H))
      ((-Complex.I) • T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩) t := by
  have h := T.hasDerivAt_stoneU x t
  rw [T.stoneU_op t x, ← map_smul]
  exact h

end UnboundedSelfAdjoint

end BookProof.ChapterStoneResolvent

namespace BookProof.StoneBridge
open Filter Topology
open scoped InnerProductSpace
open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem isSelfAdjointExtension_of_positive {D Dom : Submodule ℂ F} {H : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsPositiveSelfAdjointExtension H A) : IsSelfAdjointExtension H A :=
  ⟨h.1, h.2.1, h.2.2.2⟩
theorem isStoneFlow_stoneU (T : UnboundedSelfAdjoint F) : IsStoneFlow T T.stoneU := by
  refine ⟨T.stoneU_zero, ?_, ?_, ?_⟩
  · intro s t
    exact T.stoneU_add s t
  · intro t x
    exact T.norm_stoneU_apply t x
  · intro x hx t
    exact ⟨T.stoneU_mem_domain t ⟨x, hx⟩, T.hasDerivAt_stoneU_op ⟨x, hx⟩ t⟩

theorem exists_stone_flow_of_selfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U :=
  ⟨unboundedSelfAdjointOf hdense h, _, rfl, HEq.rfl,
    isStoneFlow_stoneU (unboundedSelfAdjointOf hdense h)⟩

theorem exists_stone_flow_of_positive {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsPositiveSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U :=
  exists_stone_flow_of_selfAdjointExtension hdense (isSelfAdjointExtension_of_positive h)

theorem exists_stone_flow_of_esa {D : Submodule ℂ F} (Hc : D →ₗ[ℂ] F)
    (hdense : Dense ((D : Submodule ℂ F) : Set F)) (hsym : SymmetricOn D Hc)
    (hesa : EssentiallySelfAdjointOn D Hc) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      IsSelfAdjointExtension Hc T.op ∧ IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := exists_isSelfAdjointExtension_of_esa Hc hdense hsym hesa
  exact ⟨unboundedSelfAdjointOf hdense hA, _, hA,
    isStoneFlow_stoneU (unboundedSelfAdjointOf hdense hA)⟩
end BookProof.StoneBridge
-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
open BookProof.StoneBridge






open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]










variable [CompleteSpace F]
theorem solution {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U := by
  exact BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension hdense h
#print axioms solution
