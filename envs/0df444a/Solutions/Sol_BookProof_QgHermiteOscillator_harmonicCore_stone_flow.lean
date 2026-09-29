-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.harmonicCore_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:28:15.341315+00:00
-- url     : https://prove2.me/submissions/4acfd67a-83ff-478d-a1a4-72276c5826f5

import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgHermiteOscillatorEsa
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

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.QgHermiteOscillator
noncomputable section
namespace BookProof.HermiteProductBasis
variable {d : ℕ}
@[simp] theorem hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

theorem pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, map_mul,
        Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [mul_comm, mul_assoc, algebraMap_eq]

theorem pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [h, algebraMap_eq]

theorem pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by
  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]

theorem pderiv_hermiteFactor_other {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := pderiv_aeval_other h _

theorem pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) :=
    fun b hb => Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  have hzero : pderiv i (∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j)) = 0 := by
    refine Finset.prod_induction _ (fun p => pderiv i p = 0) ?_ (by simp) ?_
    · intro p q hp hq
      rw [Derivation.leibniz, hp, hq]; simp
    · intro j hj
      exact pderiv_aeval_other (Finset.ne_of_mem_erase hj).symm _
  rw [hermiteMv_erase i a, hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hsub, hsi,
    Derivation.leibniz, hzero, pderiv_hermiteFactor_self]
  simp [mul_comm]

@[simp] theorem annPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = pderiv i p := rfl

@[simp] theorem crePoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl

theorem crePoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by
  rw [crePoly_apply, hermiteMv_X_mul, pderiv_hermiteMv]
  abel
end BookProof.HermiteProductBasis
namespace BookProof.QgHermiteFriedrichs
variable {d : ℕ}

@[simp] theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_mul (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p * q) = cpoly p * cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_X (j : Fin d) : cpoly (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [cpoly]

@[simp] theorem cpoly_C (a : ℂ) :
    cpoly (C a : MvPolynomial (Fin d) ℂ) = C (starRingEnd ℂ a) := by
  simp [cpoly]

theorem cpoly_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (pderiv j p) = pderiv j (cpoly p) := pderiv_map.symm

theorem conj_polyEval (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [cpoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp only [cpoly] at hp ⊢; simp [hp]

theorem conj_pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun p x) = pgFun (cpoly p) x := by
  simp only [pgFun, map_mul, Complex.conj_ofReal, conj_polyEval]

@[simp] theorem cpoly_sub (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p - q) = cpoly p - cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_neg (p : MvPolynomial (Fin d) ℂ) : cpoly (-p) = -cpoly p := by
  simp [cpoly]

theorem cpoly_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    cpoly (∑ i ∈ s, f i) = ∑ i ∈ s, cpoly (f i) :=
  map_sum (MvPolynomial.map (starRingEnd ℂ)) f s

theorem cpoly_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (coreD j p) = coreD j (cpoly p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  unfold coreD
  rw [cpoly_sub, cpoly_pderiv, cpoly_mul, cpoly_mul, cpoly_X, cpoly_C, hhalf]

theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, conj_pgFun]
  simp only [pgFun, map_mul, gaussWD_eq_sq]
  push_cast
  ring

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h : r - s = r + (-1 : ℂ) • s := by module
  rw [h, gaussInt_add, gaussInt_smul]
  ring

theorem gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by
  have h : -r = (-1 : ℂ) • r := by module
  rw [h, gaussInt_smul]
  ring

theorem gaussInt_coreD_raw (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    gaussInt (coreD j a * b) = -gaussInt (a * coreD j b) := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have hsum : coreD j a * b + a * coreD j b = pderiv j (a * b) - X j * (a * b) := by
    simp only [coreD, pderiv_mul, sub_mul, mul_sub]
    linear_combination (-(X j * a * b)) * hC2
  have h0 : gaussInt (coreD j a * b + a * coreD j b) = 0 := by
    rw [hsum, gaussInt_sub, gaussInt_pderiv, sub_self]
  rw [gaussInt_add] at h0
  linear_combination h0

theorem gaussInt_coreD (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * q) = -gaussInt (cpoly p * coreD j q) := by
  rw [cpoly_coreD, gaussInt_coreD_raw]

theorem cpoly_kinPoly (p : MvPolynomial (Fin d) ℂ) :
    cpoly (kinPoly p) = kinPoly (cpoly p) := by
  simp only [kinPoly, cpoly_neg, cpoly_sum, cpoly_coreD]

theorem gaussInt_kinPoly (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPoly q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly p * kinPoly q = -∑ j : Fin d, cpoly p * coreD j (coreD j q) := by
    simp only [kinPoly, Finset.mul_sum, mul_neg]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD j p (coreD j q)]

theorem gaussInt_kinPoly_left (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly (kinPoly p) * q = -∑ j : Fin d, coreD j (coreD j (cpoly p)) * q := by
    rw [cpoly_kinPoly]
    simp only [kinPoly, Finset.sum_mul, neg_mul]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD_raw j (coreD j (cpoly p)) q, cpoly_coreD, neg_neg]

variable (W : Vd d → ℝ)

theorem potLp_coeFn (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp

theorem coreEquiv_apply (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreEquiv_symm_pgLp (p : MvPolynomial (Fin d) ℂ) :
    coreEquiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  apply coreEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext rfl

theorem hamCore_pgLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = hamPoly W hWc hWb p := by
  simp only [hamCore, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

theorem inner_L2_eq (f g : L2d d) :
    (inner ℂ f g : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) ((f : Vd d → ℂ) x) * (g : Vd d → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply]
  ring

theorem inner_pgLp_potLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (potLp W hWc hWb q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (((W x : ℝ) : ℂ) * pgFun q x) := by
  rw [inner_pgLp]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb q] with x hx
  rw [hx]

theorem inner_potLp_pgLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (((W x : ℝ) : ℂ) * pgFun p x) * pgFun q x := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb p, pgLp_coeFn q] with x hx hy
  rw [hx, hy]

theorem inner_potLp_symm (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (potLp W hWc hWb q) := by
  rw [inner_potLp_pgLp, inner_pgLp_potLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem hamCore_symmetricOn (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (hamCore W hWc hWb) := by
  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, hamCore_pgLp, hamCore_pgLp]
  change (inner ℂ (hamPoly W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (hamPoly W hWc hWb q)
  simp only [hamPoly, inner_add_left, inner_add_right]
  congr 1
  · rw [inner_pgLp_pgLp, inner_pgLp_pgLp, gaussInt_kinPoly_left, gaussInt_kinPoly]
  · exact inner_potLp_symm W hWc hWb p q

theorem re_gaussInt_kinPoly_self (p : MvPolynomial (Fin d) ℂ) :
    (gaussInt (cpoly p * kinPoly p)).re = ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 := by
  rw [gaussInt_kinPoly]
  have h : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j p)
      = ((‖pgLp (coreD j p)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  simp only [h, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem norm_sq_pgLp (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp p‖ ^ 2 = ∫ x : Vd d, ‖pgFun p x‖ ^ 2 := by
  have h1 : (inner ℂ (pgLp p) (pgLp p) : ℂ) = ((∫ x : Vd d, ‖pgFun p x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p] with x hx
    rw [hx, conj_mul_self]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h1
  refine Complex.ofReal_inj.mp ?_
  push_cast
  exact h1

theorem integrable_potential_normSq (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d => W x * ‖pgFun p x‖ ^ 2) (volume : Measure (Vd d)) := by
  have hu : MemLp (fun x : Vd d => ‖pgFun p x‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm
  have hv : MemLp (fun x : Vd d => W x * ‖pgFun p x‖) 2 (volume : Measure (Vd d)) := by
    refine (memLp_mul_pgFun_of_expBounded hWc hWb p).of_le
      ((hWc.mul ((continuous_pgFun p).norm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (pgFun p x))]
  have hmul := hv.integrable_mul hu
  refine hmul.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

theorem hamCore_quadForm_ge (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) (x : (polyGaussCore (d := d))) :
    -c * ‖(x : L2d d)‖ ^ 2 ≤ quadForm (hamCore W hWc hWb) x := by
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  -- the potential part, as a real integral
  have hpot : (inner ℂ (pgLp p) (potLp W hWc hWb p) : ℂ)
      = ((∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_pgLp_potLp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hy : (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y : ℝ) : ℂ) * ((starRingEnd ℂ) (pgFun p y) * pgFun p y) := by ring
    change (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ)
    rw [hy, conj_mul_self]
    push_cast
    ring
  have hint : Integrable (fun y : Vd d => W y * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) :=
    integrable_potential_normSq W hWc hWb p
  have hint2 : Integrable (fun y : Vd d => -c * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) := by
    have h1 : MemLp (fun y : Vd d => ‖pgFun p y‖) 2 (volume : Measure (Vd d)) :=
      (memLp_pgFun p).norm
    have h2 := h1.integrable_mul h1
    refine (h2.const_mul (-c)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have hmono : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 ≤ ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    refine integral_mono hint2 hint fun y => ?_
    have := hlb y
    nlinarith [sq_nonneg ‖pgFun p y‖]
  have hconst : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 = -c * ‖pgLp p‖ ^ 2 := by
    rw [integral_const_mul, ← norm_sq_pgLp]
  -- assemble
  have hquad : quadForm (hamCore W hWc hWb) ⟨pgLp p, pgLp_mem_core p⟩
      = (∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2) + ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    simp only [quadForm, hamCore_pgLp, hamPoly, inner_add_right, Complex.add_re]
    rw [inner_pgLp_pgLp, re_gaussInt_kinPoly_self, hpot, Complex.ofReal_re]
  rw [hquad]
  have hkin : 0 ≤ ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hnorm : ‖((⟨pgLp p, pgLp_mem_core p⟩ : (polyGaussCore (d := d))) : L2d d)‖ = ‖pgLp p‖ := rfl
  rw [hnorm]
  linarith [hconst ▸ hmono]

theorem hamCore_quadForm_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) (x : (polyGaussCore (d := d))) :
    0 ≤ quadForm (hamCore W hWc hWb) x := by
  have h := hamCore_quadForm_ge W hWc hWb 0 (by simpa using hW0) x
  simpa using h
end BookProof.QgHermiteFriedrichs
namespace BookProof.QgHermiteOscillator
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι : Type*} {D : Submodule ℂ F}
variable {d : ℕ}
theorem eq_zero_of_inner_basis_eq_zero (b : HilbertBasis ι ℂ F) {w : F}
    (h : ∀ i, (inner ℂ (b i) w : ℂ) = 0) : w = 0 := by
  have hrep : b.repr w = 0 := by
    ext i
    rw [b.repr_apply_apply]
    simpa using h i
  have := congrArg b.repr.symm hrep
  simpa using this

theorem deficiencyTrivialAt_of_eigenbasis (T : D →ₗ[ℂ] F) (b : HilbertBasis ι ℂ F)
    (lam : ι → ℝ) (hmem : ∀ i, (b i : F) ∈ D)
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F))
    {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt D T z := by
  intro w hw
  refine eq_zero_of_inner_basis_eq_zero b fun i => ?_
  have key := hw ⟨b i, hmem i⟩
  rw [heig i, inner_smul_left] at key
  have hconj : (starRingEnd ℂ) ((lam i : ℝ) : ℂ) = ((lam i : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hconj] at key
  have hne : ((lam i : ℝ) : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simpa [sub_eq_zero] using this.symm
  have : (((lam i : ℝ) : ℂ) - z) * (inner ℂ (b i) w : ℂ) = 0 := by
    rw [sub_mul]
    simpa using sub_eq_zero.mpr key
  exact (mul_eq_zero.mp this).resolve_left hne

theorem essentiallySelfAdjointOn_of_eigenbasis (T : D →ₗ[ℂ] F) (b : HilbertBasis ι ℂ F)
    (lam : ι → ℝ) (hmem : ∀ i, (b i : F) ∈ D)
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F)) :
    EssentiallySelfAdjointOn D T :=
  ⟨deficiencyTrivialAt_of_eigenbasis T b lam hmem heig (by simp),
    deficiencyTrivialAt_of_eigenbasis T b lam hmem heig (by simp)⟩

theorem eval_harmPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (harmPoly (d := d)) = ((harmW x : ℝ) : ℂ) := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := norm_sq_eq_sum x
  unfold harmPoly harmW
  rw [map_sum, hnorm]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem potLp_harmW (p : MvPolynomial (Fin d) ℂ) :
    potLp harmW continuous_harmW expBounded_harmW p = pgLp (harmPoly * p) := by
  unfold potLp pgLp
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards with x
  simp only [pgFun, map_mul, eval_harmPoly]
  ring

theorem coreD_sq_add_harm (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    -coreD j (coreD j p) + C (1 / 4 : ℂ) * (X j ^ 2 * p)
      = crePoly j (annPoly j p) + C (1 / 2 : ℂ) * p := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have h14 : (C (1 / 4 : ℂ) : MvPolynomial (Fin d) ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) := by
    rw [← C_mul]; norm_num
  simp only [coreD, map_sub, pderiv_mul, pderiv_C, pderiv_X_self, crePoly_apply, annPoly_apply,
    h14]
  linear_combination (X j * pderiv j p) * hC2

theorem kinPoly_add_harmPoly (p : MvPolynomial (Fin d) ℂ) :
    kinPoly p + harmPoly * p
      = (∑ j : Fin d, crePoly j (annPoly j p)) + C ((d : ℂ) / 2) * p := by
  have hsum : kinPoly p + harmPoly * p
      = ∑ j : Fin d, (-coreD j (coreD j p) + C (1 / 4 : ℂ) * (X j ^ 2 * p)) := by
    simp only [kinPoly, harmPoly, Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  simp only [coreD_sq_add_harm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((d : MvPolynomial (Fin d) ℂ)) = C (d : ℂ) := by
    simp
  rw [this, ← mul_assoc, ← C_mul]
  congr 2
  ring

theorem sub_add_single_cancel {i : Fin d} {a : Fin d →₀ ℕ} (h : 1 ≤ a i) :
    (a - Finsupp.single i 1) + Finsupp.single i 1 = a := by
  classical
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · simp [hj]

theorem crePoly_annPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (annPoly i (hermiteMv a)) = ((a i : ℂ)) • hermiteMv a := by
  rw [annPoly_apply, pderiv_hermiteMv, map_smul, crePoly_hermiteMv]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]
    simp
  · rw [sub_add_single_cancel hpos]

theorem kinPoly_add_harmPoly_hermiteMv (a : Fin d →₀ ℕ) :
    kinPoly (hermiteMv a) + harmPoly * hermiteMv a
      = (((mvDeg a : ℂ) + (d : ℂ) / 2)) • hermiteMv a := by
  rw [kinPoly_add_harmPoly]
  simp only [crePoly_annPoly_hermiteMv]
  rw [← Finset.sum_smul]
  have hdeg : (∑ i : Fin d, ((a i : ℂ))) = (mvDeg a : ℂ) := by
    unfold mvDeg
    push_cast
    rfl
  rw [hdeg, add_smul]
  congr 1
  exact (MvPolynomial.smul_eq_C_mul _ _).symm

theorem harmCore_pgLp (p : MvPolynomial (Fin d) ℂ) :
    harmCore ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (kinPoly p + harmPoly * p) := by
  unfold harmCore
  rw [hamCore_pgLp]
  unfold hamPoly
  rw [potLp_harmW]
  exact (map_add (pgMap (d := d)) (kinPoly p) (harmPoly * p)).symm

theorem harmCore_hermiteMvLp (a : Fin d →₀ ℕ) :
    harmCore ⟨hermiteMvLp a, hermiteMvLp_mem_core a⟩
      = (((mvDeg a : ℝ) + (d : ℝ) / 2 : ℝ) : ℂ) • (hermiteMvLp a : L2d d) := by
  have hsm : (hermiteMvLp (d := d) a) = ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv a) := rfl
  have hmem : (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv a)) ∈ polyGaussCore (d := d) := by
    rw [← hsm]
    exact hermiteMvLp_mem_core a
  have hstep : harmCore ⟨((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv a), hmem⟩
      = ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • harmCore ⟨pgLp (hermiteMv a), pgLp_mem_core _⟩ := by
    rw [← map_smul]
    congr 1
  have hcast : ((((mvDeg a : ℝ) + (d : ℝ) / 2 : ℝ)) : ℂ) = ((mvDeg a : ℂ) + (d : ℂ) / 2) := by
    push_cast
    ring
  simp only [hsm]
  rw [hstep, harmCore_pgLp, kinPoly_add_harmPoly_hermiteMv,
    ← HermiteProductCore.pgMap_apply, map_smul, HermiteProductCore.pgMap_apply, hcast,
    smul_comm]

theorem harmonicCore_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) harmCore := by
  refine essentiallySelfAdjointOn_of_eigenbasis harmCore hermiteMvBasis
    (fun a => (mvDeg a : ℝ) + (d : ℝ) / 2) (fun a => by
      rw [hermiteMvBasis_apply]; exact hermiteMvLp_mem_core a) fun a => ?_
  have := harmCore_hermiteMvLp (d := d) a
  simpa using this

theorem harmonicCore_dense : Dense ((polyGaussCore (d := d) : Submodule ℂ (L2d d)) : Set (L2d d)) :=
  polyGaussCore_dense

theorem harmonicCore_symmetricOn : SymmetricOn (polyGaussCore (d := d)) harmCore :=
  hamCore_symmetricOn harmW continuous_harmW expBounded_harmW

theorem harmonicCore_quadForm_nonneg (x : polyGaussCore (d := d)) : 0 ≤ quadForm harmCore x :=
  hamCore_quadForm_nonneg harmW continuous_harmW expBounded_harmW
    (fun x => by unfold harmW; positivity) x

theorem potCore_pgLp (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    potCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = potLp W hWc hWb p := by
  simp only [potCore, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl

theorem potCore_symmetricOn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (potCore W hWc hWb) := by
  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, potCore_pgLp, potCore_pgLp]
  exact inner_potLp_symm W hWc hWb p q

theorem hamCore_add_potential (V W : Vd d → ℝ) (hVc : Continuous V) (hVb : ExpBounded V)
    (hWc : Continuous W) (hWb : ExpBounded W)
    (hsc : Continuous fun x => V x + W x) (hsb : ExpBounded fun x => V x + W x) :
    hamCore (fun x => V x + W x) hsc hsb = hamCore V hVc hVb + potCore W hWc hWb := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hsplit : potLp (fun x => V x + W x) hsc hsb p
      = potLp V hVc hVb p + potLp W hWc hWb p := by
    unfold potLp
    rw [← MemLp.toLp_add (memLp_mul_pgFun_of_expBounded hVc hVb p)
      (memLp_mul_pgFun_of_expBounded hWc hWb p)]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards with y
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [hx, hamCore_pgLp, LinearMap.add_apply, hamCore_pgLp, potCore_pgLp]
  unfold hamPoly
  rw [hsplit, add_assoc]

theorem expBounded_of_bounded {B : Vd d → ℝ} {M : ℝ} (hM : ∀ x, |B x| ≤ M) : ExpBounded B :=
  ⟨M, 0, le_rfl, fun x => by simpa using hM x⟩

theorem norm_potLp_le {B : Vd d → ℝ} {M : ℝ} (hBc : Continuous B) (hBb : ExpBounded B)
    (hM : ∀ x, |B x| ≤ M) (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp B hBc hBb p‖ ≤ M * ‖pgLp p‖ := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hle : ‖potLp B hBc hBb p‖ ≤ ‖((M : ℝ) : ℂ) • pgLp p‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [potLp_coeFn B hBc hBb p, Lp.coeFn_smul ((M : ℝ) : ℂ) (pgLp p),
      pgLp_coeFn p] with x hx hy hz
    rw [hx, hy, Pi.smul_apply, hz]
    simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hM x).trans (le_abs_self M)) (norm_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
end BookProof.QgHermiteOscillator

variable {d : ℕ}
theorem solution :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (harmCore (d := d)) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa harmCore harmonicCore_dense harmonicCore_symmetricOn
    harmonicCore_essentiallySelfAdjoint
#print axioms solution
