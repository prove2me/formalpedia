-- Prove2me | solution 1 for EthierKurtz.oblique_existence_from_base_and_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T11:54:07.811659+00:00
-- url     : https://prove2.me/submissions/2cff733b-592a-44a1-b27f-fca79ab82cbd

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction
import Definitions.Def_EthierKurtz_ComponentHolder
import Definitions.Def_EthierKurtz_CTwiceHolder

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace P211c1a39

open EthierKurtz

/-- A: domination by a function vanishing to first order. -/
lemma vanish_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K G : E → ℝ} {y : E} (hKG : ∀ z, |K z| ≤ |G z|) (hG0 : G y = 0)
    (hG : HasFDerivAt G (0 : E →L[ℝ] ℝ) y) : HasFDerivAt K (0 : E →L[ℝ] ℝ) y := by
  have hK0 : K y = 0 := by
    have := hKG y; rw [hG0, abs_zero] at this; exact abs_nonpos_iff.mp this
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hG ⊢
  have h1 : (fun h => K (y + h) - K y - (0 : E →L[ℝ] ℝ) h) =O[𝓝 0]
      (fun h => G (y + h) - G y - (0 : E →L[ℝ] ℝ) h) :=
    Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => by
      simp [hK0, hG0, Real.norm_eq_abs, hKG])
  exact h1.trans_isLittleO hG

/-- B: a bounded nonempty set in a nontrivial normed space has nonempty frontier. -/
lemma frontier_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {Ω : Set E} (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) : (frontier Ω).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨hne, fun h => NormedSpace.unbounded_univ ℝ E (h ▸ hb)⟩

/-- the embedding of the first n coordinates. -/
noncomputable def ιc (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Fin.lastCases (0 : ℝ) (fun i => z i))
      map_add' := by
        intro z w; ext k
        refine Fin.lastCases ?_ (fun i => ?_) k <;> simp
      map_smul' := by
        intro c z; ext k
        refine Fin.lastCases ?_ (fun i => ?_) k <;> simp }

lemma ιc_apply_last {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ιc n z (Fin.last n) = 0 := by
  simp [ιc]

lemma ιc_apply_cs {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ιc n z (Fin.castSucc i) = z i := by
  simp [ιc]

lemma graph_eq {n : ℕ} (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    (WithLp.toLp 2 (Fin.lastCases s (fun i => z i)) : EuclideanSpace ℝ (Fin (n + 1))) =
      s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [ιc_apply_last]
  · simp [ιc_apply_cs, (Fin.castSucc_lt_last i).ne]

/-- graph points are frontier points. -/
lemma graph_mem_frontier {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    {U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (himg : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D) :
    x₀ + U.symm (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) ∈ frontier Ω ∧
    x₀ + U.symm (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) ∈ Metric.ball x₀ ρ := by
  have : (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
      EuclideanSpace ℝ (Fin (n + 1))) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) := by
    rw [himg]; exact ⟨z, hz, rfl⟩
  obtain ⟨x, hx, hxe⟩ := this
  have : x = x₀ + U.symm (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) := by
    rw [← hxe]; simp
  rw [← this]; exact hx

/-- frontier points in the ball come from the graph. -/
lemma frontier_mem_graph {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    {U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (himg : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ frontier Ω) (hxb : x ∈ Metric.ball x₀ ρ) :
    ∃ z ∈ D, (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
      EuclideanSpace ℝ (Fin (n + 1))) = U (x - x₀) := by
  have : U (x - x₀) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) := ⟨x, ⟨hx, hxb⟩, rfl⟩
  rw [himg] at this
  obtain ⟨z, hz, hze⟩ := this
  exact ⟨z, hz, hze⟩

/-- a C^1 defining function vanishes on the frontier inside its chart. -/
lemma defn_zero_on_frontier {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V) {r : EuclideanSpace ℝ (Fin d) → ℝ}
    (hr : ContinuousOn r V) (hΩ : ∀ y ∈ V, y ∈ Ω ↔ r y < 0)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ frontier Ω) (hpV : p ∈ V) : r p = 0 := by
  have hpΩ : p ∉ Ω := by
    rw [hopen.frontier_eq] at hp; exact hp.2
  have h1 : 0 ≤ r p := by
    by_contra h; push Not at h; exact hpΩ ((hΩ p hpV).2 h)
  have hcl : p ∈ closure Ω := frontier_subset_closure hp
  have h2 : r p ≤ 0 := by
    have hc : ContinuousAt r p := hr.continuousAt (hV.mem_nhds hpV)
    rw [mem_closure_iff_nhdsWithin_neBot] at hcl
    have ht : Tendsto r (𝓝[Ω] p) (𝓝 (r p)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hV.mem_nhds hpV)] with y hy hyV
    exact ((hΩ y hyV).1 hy).le
  linarith

/-- C: orientation of the outward normal relative to the chart. -/
lemma orient {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hopen : IsOpen Ω)
    {x₀ ν : EuclideanSpace ℝ (Fin (n + 1))} (hν : IsOutwardUnitNormal Ω x₀ ν) {ρ : ℝ}
    {U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : IsOpen D) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ D)
    (hu : DifferentiableAt ℝ u 0) (hu0 : u 0 = 0) (hdu : fderiv ℝ u 0 = 0)
    (himg : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D) :
    ∀ i : Fin n, U ν (Fin.castSucc i) = 0 := by
  obtain ⟨_, _, V, hV, hx₀V, r, scale, hscale, hrC, _, hΩ, hdr⟩ := hν
  set e : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) (1 : ℝ)
  set y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z => x₀ + U.symm (u z • e + ιc n z) with hy
  have hyeq : ∀ z, y z = x₀ + U.symm (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) := by
    intro z; rw [graph_eq]
  have hy0 : y 0 = x₀ := by simp [hy, hu0]
  -- derivative of y at 0
  have hγ : HasFDerivAt (fun z => u z • e + ιc n z)
      ((fderiv ℝ u 0).smulRight e + ιc n) 0 :=
    (hu.hasFDerivAt.smul_const e).add (ιc n).hasFDerivAt
  rw [hdu] at hγ
  have hyd : HasFDerivAt y (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).smulRight e + ιc n)) 0 := by
    have := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : EuclideanSpace ℝ (Fin n)) hγ
    exact this.const_add x₀
  have hrd : HasFDerivAt r (fderiv ℝ r x₀) x₀ :=
    ((hrC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx₀V)).hasFDerivAt
  rw [← hy0] at hrd
  have hcomp := hrd.comp (0 : EuclideanSpace ℝ (Fin n)) hyd
  -- r ∘ y vanishes near 0
  have hyc : ContinuousAt y 0 := hyd.continuousAt
  have hev : (r ∘ y) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have hV' : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), y z ∈ V :=
      hyc (by rw [hy0]; exact hV.mem_nhds hx₀V)
    filter_upwards [hV', hD.mem_nhds h0] with z hzV hzD
    have hfr := (graph_mem_frontier himg hzD).1
    rw [← hyeq] at hfr
    exact defn_zero_on_frontier hopen hV (hrC.continuousOn) hΩ hfr hzV
  have hzero : HasFDerivAt (r ∘ y) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ (Fin n))).congr_of_eventuallyEq hev
  have huniq := hcomp.unique hzero
  intro i
  have h1 := congrArg (fun L => L (EuclideanSpace.single i (1 : ℝ))) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.zero_apply, zero_smul, zero_add,
    hy0] at h1
  rw [hdr] at h1
  have hs : (∑ k, ν k * (U.symm (ιc n (EuclideanSpace.single i 1))) k) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hscale.ne'
    · exact h
  have hinner : (∑ k, ν k * (U.symm (ιc n (EuclideanSpace.single i 1))) k) =
      U ν (Fin.castSucc i) := by
    have e1 : (∑ k, ν k * (U.symm (ιc n (EuclideanSpace.single i 1))) k) =
        inner ℝ ν (U.symm (ιc n (EuclideanSpace.single i 1))) := by
      simp [PiLp.inner_apply, mul_comm]
    have e2 : inner ℝ ν (U.symm (ιc n (EuclideanSpace.single i 1))) =
        inner ℝ (U ν) (ιc n (EuclideanSpace.single i 1)) := by
      rw [← U.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    rw [e1, e2, PiLp.inner_apply, Fin.sum_univ_castSucc]
    simp [ιc_apply_cs, ιc_apply_last, EuclideanSpace.single_apply]
  rw [hinner] at hs; exact hs

lemma inner_self_one {d : ℕ} {ν : EuclideanSpace ℝ (Fin d)} (h : ‖ν‖ = 1) :
    (∑ i, ν i * ν i) = 1 := by
  have h2 := EuclideanSpace.norm_sq_eq ν
  rw [h, one_pow] at h2
  rw [h2]; congr 1; ext i; rw [Real.norm_eq_abs, sq_abs, sq]

/-- the two sides of the outward normal. -/
lemma normal_sides {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x₀ ν : EuclideanSpace ℝ (Fin d)} (hν : IsOutwardUnitNormal Ω x₀ ν) :
    (∀ᶠ t in 𝓝[>] (0:ℝ), x₀ - t • ν ∈ Ω) ∧ (∀ᶠ t in 𝓝[>] (0:ℝ), x₀ + t • ν ∉ closure Ω) := by
  obtain ⟨_, hνn, V, hV, hx₀V, r, scale, hscale, hrC, hr0, hΩ, hdr⟩ := hν
  have hrd : HasFDerivAt r (fderiv ℝ r x₀) x₀ :=
    ((hrC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx₀V)).hasFDerivAt
  have hval : fderiv ℝ r x₀ ν = scale := by
    rw [hdr, inner_self_one hνn, mul_one]
  have hW : IsOpen (V ∩ r ⁻¹' Set.Ioi 0) := hrC.continuousOn.isOpen_inter_preimage hV isOpen_Ioi
  have hdisj : Disjoint (closure Ω) (V ∩ r ⁻¹' Set.Ioi 0) := by
    refine Disjoint.closure_left ?_ hW
    rw [Set.disjoint_left]
    intro y hy hy'
    have := (hΩ y hy'.1).1 hy
    have h2 : (0:ℝ) < r y := hy'.2
    linarith
  constructor
  · have hlin : HasDerivAt (fun t : ℝ => x₀ - t • ν) (-ν) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const ν).const_sub x₀
    have hlin' : HasDerivAt (fun t : ℝ => x₀ - t • ν) (-ν) 0 := hlin
    have hx : (fun t : ℝ => x₀ - t • ν) 0 = x₀ := by simp
    rw [← hx] at hrd
    have hg := hrd.comp_hasDerivAt (0:ℝ) hlin'
    rw [hx, map_neg, hval] at hg
    have hsl := (hasDerivAt_iff_tendsto_slope_zero.1 hg).mono_left
      (nhdsWithin_mono _ (fun t (ht : (0:ℝ) < t) => ne_of_gt ht))
    have hev := hsl.eventually (gt_mem_nhds (show -scale < 0 by linarith))
    have hVev : ∀ᶠ t in 𝓝[>] (0:ℝ), x₀ - t • ν ∈ V := by
      apply nhdsWithin_le_nhds
      have hc : Continuous (fun t : ℝ => x₀ - t • ν) := by fun_prop
      have := hc.continuousAt (x := 0) (hV.mem_nhds (by simpa using hx₀V))
      exact this
    filter_upwards [hev, hVev, self_mem_nhdsWithin] with t ht hVt htpos
    simp only [Function.comp_apply, zero_add, hx, hr0, sub_zero, smul_eq_mul] at ht
    have htpos' : (0:ℝ) < t := htpos
    have : r (x₀ - t • ν) < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ t⁻¹ * r (x₀ - t • ν) := mul_nonneg (inv_nonneg.2 htpos'.le) hc
      linarith
    exact (hΩ _ hVt).2 this
  · have hlin : HasDerivAt (fun t : ℝ => x₀ + t • ν) ν 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const ν).const_add x₀
    have hx : (fun t : ℝ => x₀ + t • ν) 0 = x₀ := by simp
    rw [← hx] at hrd
    have hg := hrd.comp_hasDerivAt (0:ℝ) hlin
    rw [hx, hval] at hg
    have hsl := (hasDerivAt_iff_tendsto_slope_zero.1 hg).mono_left
      (nhdsWithin_mono _ (fun t (ht : (0:ℝ) < t) => ne_of_gt ht))
    have hev := hsl.eventually (lt_mem_nhds (show 0 < scale by linarith))
    have hVev : ∀ᶠ t in 𝓝[>] (0:ℝ), x₀ + t • ν ∈ V := by
      apply nhdsWithin_le_nhds
      have hc : Continuous (fun t : ℝ => x₀ + t • ν) := by fun_prop
      have := hc.continuousAt (x := 0) (hV.mem_nhds (by simpa using hx₀V))
      exact this
    filter_upwards [hev, hVev, self_mem_nhdsWithin] with t ht hVt htpos
    simp only [Function.comp_apply, zero_add, hx, hr0, sub_zero, smul_eq_mul] at ht
    have htpos' : (0:ℝ) < t := htpos
    have : 0 < r (x₀ + t • ν) := by
      by_contra hc; push Not at hc
      have : t⁻¹ * r (x₀ + t • ν) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htpos'.le) hc
      linarith
    intro hcl
    exact Set.disjoint_left.1 hdisj hcl ⟨hVt, this⟩

/-- projection to the first n coordinates. -/
noncomputable def πc (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (fun i => p (Fin.castSucc i))
      map_add' := by intro p q; ext i; simp
      map_smul' := by intro c p; ext i; simp }

lemma πc_apply {n : ℕ} (p : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    πc n p i = p (Fin.castSucc i) := by simp [πc]

lemma decomp {n : ℕ} (p : EuclideanSpace ℝ (Fin (n + 1))) :
    p = p (Fin.last n) • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n (πc n p) := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [ιc_apply_last]
  · simp [ιc_apply_cs, πc_apply, (Fin.castSucc_lt_last i).ne]

lemma comb_last {n : ℕ} (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    (s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z) (Fin.last n) = s := by
  simp [ιc_apply_last]

lemma comb_πc {n : ℕ} (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    πc n (s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z) = z := by
  ext i; simp [πc_apply, ιc_apply_cs, (Fin.castSucc_lt_last i).ne]

lemma comb_normsq {n : ℕ} (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z‖ ^ 2 = s ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [ιc_apply_cs, ιc_apply_last, (Fin.castSucc_lt_last _).ne]
  ring

lemma comb_norm_le {n : ℕ} (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z‖ ≤ |s| + ‖z‖ := by
  have h := comb_normsq s z
  have hs : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  nlinarith [norm_nonneg (s • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z), norm_nonneg z,
    abs_nonneg s]

lemma abs_of_sq_one {α : ℝ} (hα : α ^ 2 = 1) : |α| = 1 := by
  have h : |α| ^ 2 = 1 ^ 2 := by rw [sq_abs, hα, one_pow]
  exact (pow_left_inj₀ (abs_nonneg α) zero_le_one two_ne_zero).1 h

/-- the chart parametrisation: base point z, height t (t > 0 is the Ω side). -/
noncomputable def Qm {n : ℕ} (x₀ : EuclideanSpace ℝ (Fin (n + 1)))
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  x₀ + U.symm ((u z - α * t) • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z)

lemma Qm_U {n : ℕ} (x₀ : EuclideanSpace ℝ (Fin (n + 1)))
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    U (Qm x₀ U u α z t - x₀) =
      (u z - α * t) • EuclideanSpace.single (Fin.last n) (1 : ℝ) + ιc n z := by
  simp [Qm]

/-- D-box: in chart coordinates, Ω is exactly the positive-height side. -/
lemma box {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hopen : IsOpen Ω)
    {x₀ ν : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    {U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (himg : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    (huc : ContinuousOn u D) {α : ℝ} (hα : α ^ 2 = 1)
    (hUν : U ν = α • EuclideanSpace.single (Fin.last n) (1 : ℝ))
    {δ1 δ2 : ℝ} (hδ1 : 0 < δ1) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1 ⊆ D)
    (hubd : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, |u z| ≤ ‖z‖)
    (hu0 : u 0 = 0) (hsize : 2 * δ1 + δ2 ≤ ρ)
    (hin : ∃ t ∈ Set.Ioo 0 δ2, x₀ - t • ν ∈ Ω)
    (hout : ∃ t ∈ Set.Ioo 0 δ2, x₀ + t • ν ∉ closure Ω) :
    ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, ∀ t : ℝ, |t| < δ2 →
      (0 < t → Qm x₀ U u α z t ∈ Ω) ∧ (t < 0 → Qm x₀ U u α z t ∉ closure Ω) ∧
      (t = 0 → Qm x₀ U u α z t ∈ frontier Ω) := by
  set e : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) (1 : ℝ) with he
  have hαa : |α| = 1 := abs_of_sq_one hα
  have hαne : α ≠ 0 := by intro h; rw [h] at hαa; norm_num at hαa
  have hν : ν = α • U.symm e := by
    rw [← map_smul, ← hUν]; simp
  have hQ0 : ∀ t, Qm x₀ U u α 0 t = x₀ - t • ν := by
    intro t; simp only [Qm, hu0, map_zero, add_zero, zero_sub, hν, map_smul, smul_smul]
    rw [neg_smul, ← sub_eq_add_neg, mul_comm]
  have hcont : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Qm x₀ U u α p.1 p.2)
      (Metric.ball 0 δ1 ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1)
        (Metric.ball 0 δ1 ×ˢ Set.univ) :=
      huc.comp continuousOn_fst (fun p hp => hball hp.1)
    have h2 : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        (u p.1 - α * p.2) • e + ιc n p.1) (Metric.ball 0 δ1 ×ˢ Set.univ) :=
      ((h1.sub (continuousOn_const.mul continuousOn_snd)).smul continuousOn_const).add
        ((ιc n).continuous.comp_continuousOn continuousOn_fst)
    exact continuousOn_const.add (U.symm.continuous.comp_continuousOn h2)
  have hnf : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, ∀ t : ℝ, |t| < δ2 → t ≠ 0 →
      Qm x₀ U u α z t ∉ frontier Ω := by
    intro z hz t ht ht0 hfr
    have hzn : ‖z‖ < δ1 := by simpa using hz
    have hQb : Qm x₀ U u α z t ∈ Metric.ball x₀ ρ := by
      rw [Metric.mem_ball, dist_eq_norm, ← U.norm_map, Qm_U]
      have h1 := comb_norm_le (u z - α * t) z
      have h2 : |u z - α * t| ≤ |u z| + |t| := by
        calc |u z - α * t| ≤ |u z| + |α * t| := abs_sub _ _
          _ = |u z| + |t| := by rw [abs_mul, hαa, one_mul]
      have h3 := hubd z hz
      linarith
    obtain ⟨z', _, hze⟩ := frontier_mem_graph himg hfr hQb
    rw [graph_eq, Qm_U] at hze
    have h1 := congrArg (πc n) hze
    rw [comb_πc, comb_πc] at h1
    have h2 := congrArg (fun p : EuclideanSpace ℝ (Fin (n + 1)) => p (Fin.last n)) hze
    simp only [comb_last] at h2
    rw [h1] at h2
    have : α * t = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hαne h
    · exact ht0 h
  have hcov : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, ∀ t : ℝ, |t| < δ2 → t ≠ 0 →
      Qm x₀ U u α z t ∈ Ω ∪ (closure Ω)ᶜ := by
    intro z hz t ht ht0
    by_cases hc : Qm x₀ U u α z t ∈ closure Ω
    · left
      have : Qm x₀ U u α z t ∈ closure Ω \ frontier Ω := ⟨hc, hnf z hz t ht ht0⟩
      rwa [closure_diff_frontier, hopen.interior_eq] at this
    · right; exact hc
  have hdisj : Disjoint Ω (closure Ω)ᶜ := Set.disjoint_compl_right_iff_subset.2 subset_closure
  have hδ1' : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1 :=
    Metric.mem_ball_self hδ1
  have hpc : ∀ I : Set ℝ, IsPreconnected I →
      IsPreconnected ((fun p : EuclideanSpace ℝ (Fin n) × ℝ => Qm x₀ U u α p.1 p.2) ''
        (Metric.ball 0 δ1 ×ˢ I)) := by
    intro I hI
    exact ((convex_ball (0 : EuclideanSpace ℝ (Fin n)) δ1).isPreconnected.prod hI).image _
      (hcont.mono (Set.prod_mono le_rfl (Set.subset_univ _)))
  have hpos : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Qm x₀ U u α p.1 p.2) ''
      (Metric.ball 0 δ1 ×ˢ Set.Ioo 0 δ2) ⊆ Ω := by
    refine IsPreconnected.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl hdisj
      ?_ ?_ (hpc _ isPreconnected_Ioo)
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      exact hcov z hz t (abs_lt.2 ⟨by linarith [ht.1, ht.2], ht.2⟩) (ne_of_gt ht.1)
    · obtain ⟨t, ht, htΩ⟩ := hin
      exact ⟨_, ⟨(0, t), ⟨hδ1', ht⟩, rfl⟩, by simp only; rw [hQ0]; exact htΩ⟩
  have hneg : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Qm x₀ U u α p.1 p.2) ''
      (Metric.ball 0 δ1 ×ˢ Set.Ioo (-δ2) 0) ⊆ (closure Ω)ᶜ := by
    refine IsPreconnected.subset_right_of_subset_union hopen isClosed_closure.isOpen_compl hdisj
      ?_ ?_ (hpc _ isPreconnected_Ioo)
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      exact hcov z hz t (abs_lt.2 ⟨ht.1, by linarith [ht.1, ht.2]⟩) (ne_of_lt ht.2)
    · obtain ⟨t, ht, htc⟩ := hout
      refine ⟨_, ⟨(0, -t), ⟨hδ1', ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩, rfl⟩, ?_⟩
      simp only; rw [hQ0, neg_smul, sub_neg_eq_add]; exact htc
  intro z hz t ht
  refine ⟨fun htp => hpos ⟨(z, t), ⟨hz, htp, (abs_lt.1 ht).2⟩, rfl⟩,
    fun htn => hneg ⟨(z, t), ⟨hz, (abs_lt.1 ht).1, htn⟩, rfl⟩, fun ht0 => ?_⟩
  subst ht0
  have := (graph_mem_frontier himg (hball hz)).1
  rw [graph_eq] at this
  simpa [Qm] using this

lemma part_norms {n : ℕ} (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖πc n p‖ ≤ ‖p‖ ∧ |p (Fin.last n)| ≤ ‖p‖ := by
  have h := comb_normsq (p (Fin.last n)) (πc n p)
  rw [← decomp] at h
  have h1 := norm_nonneg p
  have h2 := norm_nonneg (πc n p)
  constructor
  · nlinarith [sq_nonneg (p (Fin.last n))]
  · have : (p (Fin.last n)) ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [sq_nonneg ‖πc n p‖]
    exact abs_le_of_sq_le_sq' this h1 |> fun h => abs_le.2 h

/-- bounded and μ-Hölder on a set. -/
def HB {E : Type*} [NormedAddCommGroup E] (A : Set E) (μ : ℝ) (φ : E → ℝ) : Prop :=
  ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧ (∀ y ∈ A, |φ y| ≤ M) ∧
    ∀ y ∈ A, ∀ w ∈ A, |φ y - φ w| ≤ K * ‖y - w‖ ^ μ

section HBsec
variable {E : Type*} [NormedAddCommGroup E] {A : Set E} {μ : ℝ}

lemma HB.mono {φ : E → ℝ} (h : HB A μ φ) {B : Set E} (hBA : B ⊆ A) : HB B μ φ := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := h
  exact ⟨K, M, hK, hM, fun y hy => hb y (hBA hy), fun y hy w hw => hh y (hBA hy) w (hBA hw)⟩

lemma HB.const (c : ℝ) : HB A μ (fun _ => c) :=
  ⟨0, |c|, le_rfl, abs_nonneg _, fun _ _ => le_rfl, fun _ _ _ _ => by simp⟩

lemma HB.add {φ ψ : E → ℝ} (hφ : HB A μ φ) (hψ : HB A μ ψ) : HB A μ (fun y => φ y + ψ y) := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := hφ
  obtain ⟨K', M', hK', hM', hb', hh'⟩ := hψ
  refine ⟨K + K', M + M', by positivity, by positivity, fun y hy => ?_, fun y hy w hw => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (hb y hy) (hb' y hy))
  · have h1 := hh y hy w hw; have h2 := hh' y hy w hw
    calc |φ y + ψ y - (φ w + ψ w)| = |(φ y - φ w) + (ψ y - ψ w)| := by ring_nf
      _ ≤ |φ y - φ w| + |ψ y - ψ w| := abs_add_le _ _
      _ ≤ (K + K') * ‖y - w‖ ^ μ := by rw [add_mul]; linarith

lemma HB.mul {φ ψ : E → ℝ} (hφ : HB A μ φ) (hψ : HB A μ ψ) : HB A μ (fun y => φ y * ψ y) := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := hφ
  obtain ⟨K', M', hK', hM', hb', hh'⟩ := hψ
  refine ⟨M * K' + M' * K, M * M', by positivity, by positivity, fun y hy => ?_, fun y hy w hw => ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hb y hy) (hb' y hy) (abs_nonneg _) hM
  · have h1 := hh y hy w hw; have h2 := hh' y hy w hw
    have hr : 0 ≤ ‖y - w‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    calc |φ y * ψ y - φ w * ψ w| = |φ y * (ψ y - ψ w) + ψ w * (φ y - φ w)| := by ring_nf
      _ ≤ |φ y| * |ψ y - ψ w| + |ψ w| * |φ y - φ w| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ M * (K' * ‖y - w‖ ^ μ) + M' * (K * ‖y - w‖ ^ μ) := by
          gcongr
          · exact hb y hy
          · exact hb' w hw
      _ = (M * K' + M' * K) * ‖y - w‖ ^ μ := by ring

lemma HB.const_mul {φ : E → ℝ} (hφ : HB A μ φ) (c : ℝ) : HB A μ (fun y => c * φ y) :=
  (HB.const c).mul hφ

lemma HB.neg {φ : E → ℝ} (hφ : HB A μ φ) : HB A μ (fun y => -φ y) := by
  have := hφ.const_mul (-1); simpa using this

lemma HB.sub {φ ψ : E → ℝ} (hφ : HB A μ φ) (hψ : HB A μ ψ) : HB A μ (fun y => φ y - ψ y) := by
  have := hφ.add hψ.neg; simpa [sub_eq_add_neg] using this

lemma HB.sum {ι : Type*} (s : Finset ι) {φ : ι → E → ℝ} (h : ∀ i ∈ s, HB A μ (φ i)) :
    HB A μ (fun y => ∑ i ∈ s, φ i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HB.const (A := A) (μ := μ) (0 : ℝ))
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simpa [Finset.sum_insert ha] using this

lemma HB.congr {φ ψ : E → ℝ} (hφ : HB A μ φ) (he : ∀ y ∈ A, φ y = ψ y) : HB A μ ψ := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := hφ
  refine ⟨K, M, hK, hM, fun y hy => ?_, fun y hy w hw => ?_⟩
  · rw [← he y hy]; exact hb y hy
  · rw [← he y hy, ← he w hw]; exact hh y hy w hw

lemma HB.comp {E' : Type*} [NormedAddCommGroup E'] {A' : Set E'} {φ : E' → ℝ}
    (h : HB A' μ φ) (hμ : 0 ≤ μ) {g : E → E'} (hg : ∀ y ∈ A, g y ∈ A')
    (hl : ∀ y ∈ A, ∀ w ∈ A, ‖g y - g w‖ ≤ ‖y - w‖) : HB A μ (fun y => φ (g y)) := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := h
  refine ⟨K, M, hK, hM, fun y hy => hb _ (hg y hy), fun y hy w hw => ?_⟩
  calc |φ (g y) - φ (g w)| ≤ K * ‖g y - g w‖ ^ μ := hh _ (hg y hy) _ (hg w hw)
    _ ≤ K * ‖y - w‖ ^ μ := by
        gcongr; exact hl y hy w hw

lemma HB_of_lip (hμ : 0 ≤ μ ∧ μ ≤ 1) {φ : E → ℝ} {Dm L M : ℝ} (hL0 : 0 ≤ L)
    (hD : ∀ y ∈ A, ∀ w ∈ A, ‖y - w‖ ≤ Dm) (hL : ∀ y ∈ A, ∀ w ∈ A, |φ y - φ w| ≤ L * ‖y - w‖)
    (hM : ∀ y ∈ A, |φ y| ≤ M) (hM0 : 0 ≤ M) : HB A μ φ := by
  refine ⟨L * max Dm 0 ^ (1 - μ), M, by positivity, hM0, hM, fun y hy w hw => ?_⟩
  have ht : 0 ≤ ‖y - w‖ := norm_nonneg _
  have hsplit : ‖y - w‖ = ‖y - w‖ ^ μ * ‖y - w‖ ^ (1 - μ) := by
    rw [← Real.rpow_add' ht (by norm_num)]; simp
  have h2 : ‖y - w‖ ^ (1 - μ) ≤ max Dm 0 ^ (1 - μ) :=
    Real.rpow_le_rpow ht ((hD y hy w hw).trans (le_max_left _ _)) (by linarith)
  calc |φ y - φ w| ≤ L * ‖y - w‖ := hL y hy w hw
    _ = L * (‖y - w‖ ^ μ * ‖y - w‖ ^ (1 - μ)) := by rw [← hsplit]
    _ ≤ L * (‖y - w‖ ^ μ * max Dm 0 ^ (1 - μ)) := by
        gcongr
    _ = L * max Dm 0 ^ (1 - μ) * ‖y - w‖ ^ μ := by ring

lemma HB_of_hol (hμ0 : 0 ≤ μ) {φ : E → ℝ} {Dm K : ℝ} (hK0 : 0 ≤ K)
    (hD : ∀ y ∈ A, ∀ w ∈ A, ‖y - w‖ ≤ Dm)
    (hK : ∀ y ∈ A, ∀ w ∈ A, |φ y - φ w| ≤ K * ‖y - w‖ ^ μ) : HB A μ φ := by
  rcases A.eq_empty_or_nonempty with hA | ⟨y₀, hy₀⟩
  · subst hA; exact ⟨0, 0, le_rfl, le_rfl, fun _ h => h.elim, fun _ h => h.elim⟩
  refine ⟨K, |φ y₀| + K * max Dm 0 ^ μ, hK0, by positivity, fun y hy => ?_, hK⟩
  have h1 := hK y hy y₀ hy₀
  have h2 : ‖y - y₀‖ ^ μ ≤ max Dm 0 ^ μ :=
    Real.rpow_le_rpow (norm_nonneg _) ((hD y hy y₀ hy₀).trans (le_max_left _ _)) hμ0
  have h3 : |φ y| ≤ |φ y - φ y₀| + |φ y₀| := by
    have := abs_add_le (φ y - φ y₀) (φ y₀); simpa using this
  nlinarith

/-- globalise: Hölder near c and zero away from c gives a global Hölder bound on S. -/
lemma HB.glob (hμ : 0 < μ) {S : Set E} {c : E} {r : ℝ} (hr : 0 < r) {φ : E → ℝ}
    (h : HB (S ∩ Metric.ball c r) μ φ) (h0 : ∀ y ∈ S, r / 2 ≤ ‖y - c‖ → φ y = 0) :
    ∃ K, 0 ≤ K ∧ ∀ y ∈ S, ∀ w ∈ S, |φ y - φ w| ≤ K * ‖y - w‖ ^ μ := by
  obtain ⟨K, M, hK, hM, hb, hh⟩ := h
  refine ⟨K + M * (2 / r) ^ μ, by positivity, ?_⟩
  have key : ∀ y ∈ S, ∀ w ∈ S, ‖y - c‖ < r / 2 → r ≤ ‖w - c‖ →
      |φ y - φ w| ≤ (K + M * (2 / r) ^ μ) * ‖y - w‖ ^ μ := by
    intro y hy w hw hyc hwc
    rw [h0 w hw (by linarith), sub_zero]
    have hyw : r / 2 ≤ ‖y - w‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub w y c
      rw [norm_sub_rev w y] at this; linarith
    have hone : 1 ≤ (2 / r * ‖y - w‖) ^ μ := by
      apply Real.one_le_rpow _ hμ.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]; linarith
    have hyB : y ∈ S ∩ Metric.ball c r := ⟨hy, by rw [Metric.mem_ball, dist_eq_norm]; linarith⟩
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at hone
    have hr' : 0 ≤ ‖y - w‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith [hb y hyB]
  intro y hy w hw
  by_cases hyr : ‖y - c‖ < r
  · by_cases hwr : ‖w - c‖ < r
    · have := hh y ⟨hy, by rwa [Metric.mem_ball, dist_eq_norm]⟩ w
        ⟨hw, by rwa [Metric.mem_ball, dist_eq_norm]⟩
      have hr' : 0 ≤ ‖y - w‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
      have hp := Real.rpow_nonneg (show (0:ℝ) ≤ 2 / r by positivity) μ
      have hq := mul_nonneg (mul_nonneg hM hp) hr'
      rw [add_mul]; linarith
    · push Not at hwr
      by_cases hyr2 : ‖y - c‖ < r / 2
      · exact key y hy w hw hyr2 hwr
      · push Not at hyr2
        rw [h0 y hy hyr2, h0 w hw (by linarith), sub_self, abs_zero]; positivity
  · push Not at hyr
    by_cases hwr2 : ‖w - c‖ < r / 2
    · rw [abs_sub_comm, norm_sub_rev]; exact key w hw y hy hwr2 hyr
    · push Not at hwr2
      rw [h0 y hy (by linarith), h0 w hw hwr2, sub_self, abs_zero]; positivity

end HBsec


/-- ComponentHolder on D gives HB on small balls around 0 (balls are convex). -/
lemma CH_ballD {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} (hμ0 : 0 ≤ μ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : EthierKurtz.ComponentHolder D μ φ) {δ : ℝ}
    (hδ : 0 < δ) (hball : Metric.ball 0 δ ⊆ D) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), HB (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) μ φ := by
  obtain ⟨_, ρ₀, M, hρ₀, hM, hosc⟩ := hφ
  set r0 := min δ (ρ₀ / 4) with hr0
  have hr0p : 0 < r0 := lt_min hδ (by linarith)
  have hmain : HB (Metric.ball 0 r0) μ φ := by
    apply HB_of_hol hμ0 (K := M * 2 ^ μ) (Dm := 2 * r0) (by positivity)
    · intro y hy w hw
      rw [Metric.mem_ball, dist_zero_right] at hy hw
      calc ‖y - w‖ ≤ ‖y‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 * r0 := by linarith
    · intro y hy w hw
      rcases eq_or_ne y w with rfl | hne
      · simp only [sub_self, abs_zero, norm_zero]; positivity
      have hpos : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hy' := hy; have hw' := hw
      rw [Metric.mem_ball, dist_zero_right] at hy' hw'
      have hρle : 2 * ‖y - w‖ ≤ ρ₀ := by
        have : ‖y - w‖ ≤ ‖y‖ + ‖w‖ := norm_sub_le _ _
        have : r0 ≤ ρ₀ / 4 := min_le_right _ _
        linarith
      set W := Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ∩ Metric.ball y (2 * ‖y - w‖)
      have hWc : IsPreconnected W := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
      have hyW : y ∈ W :=
        ⟨Metric.ball_subset_ball (min_le_left _ _) hy, Metric.mem_ball_self (by positivity)⟩
      have hwW : w ∈ W := ⟨Metric.ball_subset_ball (min_le_left _ _) hw, by
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; linarith⟩
      have hWsub : W ⊆ D ∩ Metric.ball y (2 * ‖y - w‖) := fun p hp => ⟨hball hp.1, hp.2⟩
      have hcc := hWc.subset_connectedComponentIn hyW hWsub
      have := hosc (2 * ‖y - w‖) (by positivity) hρle y y (hWsub hyW) y (hcc hyW) w (hcc hwW)
      calc |φ y - φ w| ≤ M * (2 * ‖y - w‖) ^ μ := this
        _ = M * 2 ^ μ * ‖y - w‖ ^ μ := by
            rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring
  filter_upwards [Ioo_mem_nhdsGT hr0p] with r hr
  exact hmain.mono (Metric.ball_subset_ball hr.2.le)

/-- the derivative of a C² function is Lipschitz on a small ball around 0. -/
lemma fderiv_lip {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsOpen D)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u D) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) :
    ∃ L, 0 ≤ L ∧ ∃ r0 : ℝ, 0 < r0 ∧ ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r0,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r0,
        ‖fderiv ℝ u z - fderiv ℝ u z'‖ ≤ L * ‖z - z'‖ := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) D := hu.fderiv_of_isOpen hD (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := (h1.contDiffAt (hD.mem_nhds h0)).exists_lipschitzOnWith
  obtain ⟨r0, hr0, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨K, K.2, r0, hr0, fun z hz z' hz' => ?_⟩
  have := hK.dist_le_mul z (hsub hz) z' (hsub hz')
  rwa [dist_eq_norm, dist_eq_norm] at this

lemma clm_expand {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul]

lemma fderiv_apply_const {d : ℕ} {u : EuclideanSpace ℝ (Fin d) → ℝ} {z : EuclideanSpace ℝ (Fin d)}
    (h : DifferentiableAt ℝ (fun y => fderiv ℝ u y) z) (w : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun y => fderiv ℝ u y w) ((fderiv ℝ (fun y => fderiv ℝ u y) z).flip w) z := by
  have := h.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  simpa using this

lemma second_expand {d : ℕ} {u : EuclideanSpace ℝ (Fin d) → ℝ} {z : EuclideanSpace ℝ (Fin d)}
    (h : DifferentiableAt ℝ (fun y => fderiv ℝ u y) z) (a b : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => fderiv ℝ u y) z a b = ∑ k, ∑ l, a k * b l *
      fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single l 1)) z (EuclideanSpace.single k 1) := by
  set B := fderiv ℝ (fun y => fderiv ℝ u y) z
  have e1 : B a b = ∑ k, a k * B (EuclideanSpace.single k 1) b := by
    have := clm_expand (B.flip b) a; simpa using this
  rw [e1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [clm_expand (B (EuclideanSpace.single k 1)) b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(fderiv_apply_const h _).fderiv]
  simp only [ContinuousLinearMap.flip_apply]; ring

/-- all the chart data at one frontier point. -/
structure Chart {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) where
  x₀ : EuclideanSpace ℝ (Fin (n + 1))
  ν : EuclideanSpace ℝ (Fin (n + 1))
  U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))
  u : EuclideanSpace ℝ (Fin n) → ℝ
  α : ℝ
  δ1 : ℝ
  δ2 : ℝ
  hνn : ‖ν‖ = 1
  hα : α ^ 2 = 1
  hUν : U ν = α • EuclideanSpace.single (Fin.last n) (1 : ℝ)
  hδ1 : 0 < δ1
  hu0 : u 0 = 0
  hlip : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1,
    ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, |u z - u z'| ≤ ‖z - z'‖
  hδ12 : 2 * δ1 ≤ δ2
  hbox : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, ∀ t : ℝ, |t| < δ2 →
      (0 < t → Qm x₀ U u α z t ∈ Ω) ∧ (t < 0 → Qm x₀ U u α z t ∉ closure Ω) ∧
      (t = 0 → Qm x₀ U u α z t ∈ frontier Ω)

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}

/-- height above the boundary (positive inside Ω). -/
noncomputable def Ch.T (C : Chart Ω) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  C.α * (C.u (πc n (C.U (x - C.x₀))) - C.U (x - C.x₀) (Fin.last n))

lemma T_eq_Qm (C : Chart Ω) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x = Qm C.x₀ C.U C.u C.α (πc n (C.U (x - C.x₀))) (Ch.T C x) := by
  have h : C.u (πc n (C.U (x - C.x₀))) - C.α * Ch.T C x = C.U (x - C.x₀) (Fin.last n) := by
    unfold Ch.T; linear_combination (C.U (x - C.x₀) (Fin.last n) - C.u (πc n (C.U (x - C.x₀)))) * C.hα
  unfold Qm; rw [h, ← decomp]; simp

lemma T_shift (C : Chart Ω) (x : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    Ch.T C (x - s • C.ν) = Ch.T C x + s := by
  have h1 : C.U (x - s • C.ν - C.x₀) =
      C.U (x - C.x₀) - (s * C.α) • EuclideanSpace.single (Fin.last n) (1 : ℝ) := by
    rw [show x - s • C.ν - C.x₀ = (x - C.x₀) - s • C.ν by abel, map_sub, map_smul, C.hUν, smul_smul]
  have he : πc n (EuclideanSpace.single (Fin.last n) (1 : ℝ)) = 0 := by
    ext i; simp [πc_apply, (Fin.castSucc_lt_last i).ne]
  have h2 : πc n (C.U (x - s • C.ν - C.x₀)) = πc n (C.U (x - C.x₀)) := by
    rw [h1, map_sub, map_smul, he, smul_zero, sub_zero]
  have h3 : C.U (x - s • C.ν - C.x₀) (Fin.last n) = C.U (x - C.x₀) (Fin.last n) - s * C.α := by
    rw [h1]; simp
  unfold Ch.T; rw [h2, h3]; linear_combination s * C.hα

lemma T_lip (C : Chart Ω) {x y : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : ‖x - C.x₀‖ < C.δ1) (hy : ‖y - C.x₀‖ < C.δ1) :
    |Ch.T C x - Ch.T C y| ≤ 2 * ‖x - y‖ := by
  have hαa := abs_of_sq_one C.hα
  have hd : C.U (x - C.x₀) - C.U (y - C.x₀) = C.U (x - y) := by
    rw [← map_sub]; congr 1; abel
  have hpx := part_norms (C.U (x - C.x₀))
  have hpy := part_norms (C.U (y - C.x₀))
  have hpd := part_norms (C.U (x - y))
  rw [LinearIsometryEquiv.norm_map] at hpx hpy hpd
  have hzx : πc n (C.U (x - C.x₀)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 := by
    rw [mem_ball_zero_iff]; linarith [hpx.1]
  have hzy : πc n (C.U (y - C.x₀)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 := by
    rw [mem_ball_zero_iff]; linarith [hpy.1]
  have hl := C.hlip _ hzx _ hzy
  rw [← map_sub, hd] at hl
  have hl2 : |C.U (x - C.x₀) (Fin.last n) - C.U (y - C.x₀) (Fin.last n)| ≤ ‖x - y‖ := by
    have : C.U (x - C.x₀) (Fin.last n) - C.U (y - C.x₀) (Fin.last n) = C.U (x - y) (Fin.last n) := by
      rw [← hd]; simp
    rw [this]; exact hpd.2
  have hpd1 := hpd.1
  unfold Ch.T
  rw [← mul_sub, abs_mul, hαa, one_mul]
  calc |C.u (πc n (C.U (x - C.x₀))) - C.U (x - C.x₀) (Fin.last n) -
        (C.u (πc n (C.U (y - C.x₀))) - C.U (y - C.x₀) (Fin.last n))|
      = |(C.u (πc n (C.U (x - C.x₀))) - C.u (πc n (C.U (y - C.x₀)))) -
          (C.U (x - C.x₀) (Fin.last n) - C.U (y - C.x₀) (Fin.last n))| := by ring_nf
    _ ≤ |C.u (πc n (C.U (x - C.x₀))) - C.u (πc n (C.U (y - C.x₀)))| +
          |C.U (x - C.x₀) (Fin.last n) - C.U (y - C.x₀) (Fin.last n)| := abs_sub _ _
    _ ≤ 2 * ‖x - y‖ := by linarith

lemma T_x0 (C : Chart Ω) : Ch.T C C.x₀ = 0 := by
  simp [Ch.T, C.hu0]

/-- characterisation of Ω, closure and frontier near x₀ by the sign of T. -/
lemma char (C : Chart Ω) (hopen : IsOpen Ω) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : ‖x - C.x₀‖ < C.δ1) :
    (x ∈ Ω ↔ 0 < Ch.T C x) ∧ (x ∈ closure Ω ↔ 0 ≤ Ch.T C x) := by
  have hp := part_norms (C.U (x - C.x₀))
  rw [LinearIsometryEquiv.norm_map] at hp
  have hz : πc n (C.U (x - C.x₀)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 := by
    rw [mem_ball_zero_iff]; linarith [hp.1]
  have hT : |Ch.T C x| < C.δ2 := by
    have hαa := abs_of_sq_one C.hα
    have hl := C.hlip _ hz 0 (Metric.mem_ball_self C.hδ1)
    rw [C.hu0, sub_zero, sub_zero] at hl
    unfold Ch.T; rw [abs_mul, hαa, one_mul]
    have := abs_sub (C.u (πc n (C.U (x - C.x₀)))) (C.U (x - C.x₀) (Fin.last n))
    linarith [hp.1, hp.2, C.hδ12]
  have hb := C.hbox _ hz _ hT
  rw [← T_eq_Qm] at hb
  have hfr : frontier Ω ∩ Ω = ∅ := by
    rw [hopen.frontier_eq]; ext y; simp
  rcases lt_trichotomy (Ch.T C x) 0 with h | h | h
  · have h1 := hb.2.1 h
    exact ⟨⟨fun hx => absurd (subset_closure hx) h1, fun h' => by linarith⟩,
      ⟨fun hx => absurd hx h1, fun h' => by linarith⟩⟩
  · have h1 := hb.2.2 h
    refine ⟨⟨fun hx => ?_, fun h' => by linarith⟩, ⟨fun _ => h.ge, fun _ => frontier_subset_closure h1⟩⟩
    have : x ∈ frontier Ω ∩ Ω := ⟨h1, hx⟩
    rw [hfr] at this; exact this.elim
  · have h1 := hb.1 h
    exact ⟨⟨fun _ => h, fun _ => h1⟩, ⟨fun _ => h.le, fun _ => subset_closure h1⟩⟩

lemma norm_smul_nu (C : Chart Ω) (s : ℝ) (hs : 0 ≤ s) : ‖s • C.ν‖ = s := by
  rw [norm_smul, C.hνn, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]

/-- E: a short path inside Ω between nearby points of Ω (down along -ν, across, up). -/
lemma path (C : Chart Ω) (hopen : IsOpen Ω) {y w : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ Ω) (hw : w ∈ Ω) (hyb : ‖y - C.x₀‖ < C.δ1 / 16) (hwb : ‖w - C.x₀‖ < C.δ1 / 16) :
    ∃ P : Set (EuclideanSpace ℝ (Fin (n + 1))), IsPreconnected P ∧ y ∈ P ∧ w ∈ P ∧ P ⊆ Ω ∧
      ∀ p ∈ P, ‖p - y‖ ≤ 4 * ‖y - w‖ := by
  set d := ‖y - w‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdle : d < C.δ1 / 8 := by
    have : ‖y - w‖ ≤ ‖y - C.x₀‖ + ‖w - C.x₀‖ := by
      calc ‖y - w‖ = ‖(y - C.x₀) - (w - C.x₀)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hTy := ((char C hopen (by linarith [C.hδ1] : ‖y - C.x₀‖ < C.δ1)).1).1 hy
  have hTw := ((char C hopen (by linarith [C.hδ1] : ‖w - C.x₀‖ < C.δ1)).1).1 hw
  have hin : ∀ p, ‖p - C.x₀‖ < C.δ1 → 0 < Ch.T C p → p ∈ Ω :=
    fun p hp hT => ((char C hopen hp).1).2 hT
  set y' := y - (3 * d) • C.ν with hy'
  set w' := w - (3 * d) • C.ν with hw'
  have hn3 := norm_smul_nu C (3 * d) (by positivity)
  -- vertical segments
  have hvert : ∀ q, q ∈ Ω → ‖q - C.x₀‖ < C.δ1 / 16 → 0 < Ch.T C q →
      ∀ p ∈ segment ℝ q (q - (3 * d) • C.ν), p ∈ Ω ∧ ‖p - q‖ ≤ 3 * d := by
    intro q _ hqb hTq p hp
    rw [segment_eq_image'] at hp
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hp
    dsimp only
    have he : q + θ • (q - (3 * d) • C.ν - q) = q - (θ * (3 * d)) • C.ν := by
      rw [show q - (3 * d) • C.ν - q = -((3 * d) • C.ν) by abel, smul_neg, smul_smul]; abel
    rw [he]
    have hn := norm_smul_nu C (θ * (3 * d)) (by positivity)
    have hle : θ * (3 * d) ≤ 3 * d := by nlinarith
    refine ⟨hin _ ?_ ?_, ?_⟩
    · calc ‖q - (θ * (3 * d)) • C.ν - C.x₀‖ = ‖(q - C.x₀) - (θ * (3 * d)) • C.ν‖ := by congr 1; abel
        _ ≤ ‖q - C.x₀‖ + ‖(θ * (3 * d)) • C.ν‖ := norm_sub_le _ _
        _ < C.δ1 := by rw [hn]; linarith
    · rw [T_shift]; nlinarith
    · rw [show q - (θ * (3 * d)) • C.ν - q = -((θ * (3 * d)) • C.ν) by abel, norm_neg, hn]; exact hle
  refine ⟨segment ℝ y y' ∪ segment ℝ y' w' ∪ segment ℝ w' w, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsPreconnected.union w' ?_ (left_mem_segment ℝ w' w) ?_ (convex_segment _ _).isPreconnected
    · exact Or.inr (right_mem_segment ℝ y' w')
    · exact IsPreconnected.union y' (right_mem_segment ℝ y y') (left_mem_segment ℝ y' w')
        (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected
  · exact Or.inl (Or.inl (left_mem_segment ℝ y y'))
  · exact Or.inr (right_mem_segment ℝ w' w)
  · rintro p ((hp | hp) | hp)
    · exact (hvert y hy hyb hTy p hp).1
    · rw [segment_eq_image'] at hp
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hp
      dsimp only
      have hww : w' - y' = w - y := by rw [hy', hw']; abel
      rw [hww]
      have hn : ‖θ • (w - y)‖ ≤ d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0, norm_sub_rev]; nlinarith
      have hy'b : ‖y' - C.x₀‖ < C.δ1 / 2 := by
        calc ‖y' - C.x₀‖ = ‖(y - C.x₀) - (3 * d) • C.ν‖ := by rw [hy']; congr 1; abel
          _ ≤ ‖y - C.x₀‖ + ‖(3 * d) • C.ν‖ := norm_sub_le _ _
          _ < C.δ1 / 2 := by rw [hn3]; linarith
      have hpb : ‖y' + θ • (w - y) - C.x₀‖ < C.δ1 := by
        calc ‖y' + θ • (w - y) - C.x₀‖ = ‖(y' - C.x₀) + θ • (w - y)‖ := by congr 1; abel
          _ ≤ ‖y' - C.x₀‖ + ‖θ • (w - y)‖ := norm_add_le _ _
          _ < C.δ1 := by linarith
      refine hin _ hpb ?_
      have hl := T_lip C hpb (by linarith : ‖y' - C.x₀‖ < C.δ1)
      have hTy' : Ch.T C y' = Ch.T C y + 3 * d := by rw [hy', T_shift]
      rw [show y' + θ • (w - y) - y' = θ • (w - y) by abel] at hl
      have := (abs_le.1 hl).1
      nlinarith
    · rw [segment_symm] at hp
      exact (hvert w hw hwb hTw p hp).1
  · rintro p ((hp | hp) | hp)
    · have := (hvert y hy hyb hTy p hp).2; linarith
    · rw [segment_eq_image'] at hp
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hp
      dsimp only
      have hww : w' - y' = w - y := by rw [hy', hw']; abel
      rw [hww]
      have hn : ‖θ • (w - y)‖ ≤ d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0, norm_sub_rev]; nlinarith
      calc ‖y' + θ • (w - y) - y‖ = ‖θ • (w - y) - (3 * d) • C.ν‖ := by rw [hy']; congr 1; abel
        _ ≤ ‖θ • (w - y)‖ + ‖(3 * d) • C.ν‖ := norm_sub_le _ _
        _ ≤ 4 * d := by rw [hn3]; linarith
    · rw [segment_symm] at hp
      have := (hvert w hw hwb hTw p hp).2
      calc ‖p - y‖ = ‖(p - w) + (w - y)‖ := by congr 1; abel
        _ ≤ ‖p - w‖ + ‖w - y‖ := norm_add_le _ _
        _ ≤ 4 * d := by rw [norm_sub_rev w y]; linarith

/-- ComponentHolder gives a genuine Hölder bound near x₀. -/
lemma CH_apply (C : Chart Ω) (hopen : IsOpen Ω) {μ : ℝ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : ComponentHolder Ω μ φ) :
    ∃ ρ₀ M : ℝ, 0 < ρ₀ ∧ 0 ≤ M ∧ ∀ y ∈ Ω, ∀ w ∈ Ω, ‖y - C.x₀‖ < C.δ1 / 16 →
      ‖w - C.x₀‖ < C.δ1 / 16 → 0 < ‖y - w‖ → 5 * ‖y - w‖ ≤ ρ₀ →
      |φ y - φ w| ≤ M * (5 * ‖y - w‖) ^ μ := by
  obtain ⟨_, ρ₀, M, hρ₀, hM, hosc⟩ := hφ
  refine ⟨ρ₀, M, hρ₀, hM, fun y hy w hw hyb hwb hpos hle => ?_⟩
  obtain ⟨P, hP, hyP, hwP, hPΩ, hPd⟩ := path C hopen hy hw hyb hwb
  have hsub : P ⊆ Ω ∩ Metric.ball y (5 * ‖y - w‖) := by
    intro p hp
    refine ⟨hPΩ hp, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have := hPd p hp; linarith
  have hyB : y ∈ Ω ∩ Metric.ball y (5 * ‖y - w‖) := hsub hyP
  have hcc := hP.subset_connectedComponentIn hyP hsub
  exact hosc _ (by linarith) hle y y hyB y (hcc hyP) w (hcc hwP)

/-- (2) a Chart exists at every frontier point. -/
lemma exists_chart (hopen : IsOpen Ω) {μ : ℝ} (hboundary : BoundaryCTwiceHolder Ω μ)
    {x₀ ν : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ frontier Ω)
    (hν : IsOutwardUnitNormal Ω x₀ ν) :
    ∃ C : Chart Ω, C.x₀ = x₀ ∧ C.ν = ν ∧ ∃ D : Set (EuclideanSpace ℝ (Fin n)), IsOpen D ∧
      Metric.ball 0 C.δ1 ⊆ D ∧ CTwiceHolder D μ C.u := by
  obtain ⟨ρ, hρ, hch⟩ := hboundary
  obtain ⟨U, D, u, hD, h0, hu, hu0, hdu, _, himg⟩ := hch x₀ hx₀
  have hdiffD : DifferentiableOn ℝ u D := hu.1.differentiableOn two_ne_zero
  have hud : DifferentiableAt ℝ u 0 := hdiffD.differentiableAt (hD.mem_nhds h0)
  have hor := orient hopen hν hD h0 hud hu0 hdu himg
  set e : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) (1 : ℝ) with he
  set α := U ν (Fin.last n) with hαdef
  have hπ : πc n (U ν) = 0 := by ext i; rw [πc_apply, hor i]; rfl
  have hUν : U ν = α • e := by
    have := decomp (U ν); rw [hπ, map_zero, add_zero] at this; exact this
  have hα : α ^ 2 = 1 := by
    have h1 := comb_normsq α (0 : EuclideanSpace ℝ (Fin n))
    rw [map_zero, add_zero, ← hUν, U.norm_map, hν.2.1, norm_zero] at h1
    linarith
  -- small ball where ‖fderiv u‖ ≤ 1
  have hfc : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.1.continuousOn_fderiv_of_isOpen hD (by norm_num)).continuousAt (hD.mem_nhds h0)
  have hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), z ∈ D ∧ ‖fderiv ℝ u z‖ ≤ 1 := by
    have h1 : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ‖fderiv ℝ u z - fderiv ℝ u 0‖ < 1 := by
      have := hfc.tendsto
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [h1, hD.mem_nhds h0] with z hz hzD
    rw [hdu, sub_zero] at hz
    exact ⟨hzD, hz.le⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hev
  set δ1 := min ε (ρ / 4) with hδ1def
  have hδ1 : 0 < δ1 := lt_min hε (by linarith)
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1 ⊆ D :=
    fun z hz => (hεsub (Metric.ball_subset_ball (min_le_left _ _) hz)).1
  have hlip : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, |u z - u z'| ≤ ‖z - z'‖ := by
    intro z hz z' hz'
    have := (convex_ball (0 : EuclideanSpace ℝ (Fin n)) δ1).norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hdiffD.differentiableAt (hD.mem_nhds (hball hx)))
      (fun x hx => (hεsub (Metric.ball_subset_ball (min_le_left _ _) hx)).2) hz' hz
    rw [one_mul, Real.norm_eq_abs] at this
    exact this
  have hubd : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ1, |u z| ≤ ‖z‖ := by
    intro z hz
    have := hlip z hz 0 (Metric.mem_ball_self hδ1)
    rwa [hu0, sub_zero, sub_zero] at this
  have hsides := normal_sides hν
  have hIoo : Set.Ioo (0 : ℝ) (2 * δ1) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith)
  obtain ⟨t1, ht1, ht1'⟩ := (hsides.1.and (Filter.mem_of_superset hIoo fun _ h => h)).exists
  obtain ⟨t2, ht2, ht2'⟩ := (hsides.2.and (Filter.mem_of_superset hIoo fun _ h => h)).exists
  have hsize : 2 * δ1 + 2 * δ1 ≤ ρ := by
    have := min_le_right ε (ρ / 4); linarith
  have hbox := box hopen himg hu.1.continuousOn hα hUν hδ1 hball hubd hu0 hsize
    ⟨t1, ht1', ht1⟩ ⟨t2, ht2', ht2⟩
  exact ⟨⟨x₀, ν, U, u, α, δ1, 2 * δ1, hν.2.1, hα, hUν, hδ1, hu0, hlip, le_rfl, hbox⟩,
    rfl, rfl, D, hD, hball, hu⟩


/-! ## Session 2: chart derivatives, the test function F = χ·T² -/

noncomputable def Lz (C : Chart Ω) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (πc n).comp C.U.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def lastL (C : Chart Ω) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (Fin.last n)).comp C.U.toContinuousLinearEquiv.toContinuousLinearMap

lemma Lz_apply (C : Chart Ω) (v : EuclideanSpace ℝ (Fin (n + 1))) : Lz C v = πc n (C.U v) := rfl

lemma lastL_apply (C : Chart Ω) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    lastL C v = C.U v (Fin.last n) := rfl

lemma Lz_norm_le (C : Chart Ω) (v : EuclideanSpace ℝ (Fin (n + 1))) : ‖Lz C v‖ ≤ ‖v‖ := by
  rw [Lz_apply]; have := (part_norms (C.U v)).1; rwa [C.U.norm_map] at this

lemma T_fun (C : Chart Ω) :
    Ch.T C = fun y => C.α * (C.u (Lz C (y - C.x₀)) - lastL C (y - C.x₀)) := rfl

/-- p_j = ∂_j T. -/
noncomputable def pj (C : Chart Ω) (j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  C.α * (fderiv ℝ C.u (Lz C (y - C.x₀)) (Lz C (EuclideanSpace.single j 1)) -
    lastL C (EuclideanSpace.single j 1))

/-- q_ij = ∂_i p_j. -/
noncomputable def qij (C : Chart Ω) (i j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  C.α * (fderiv ℝ (fun z => fderiv ℝ C.u z) (Lz C (y - C.x₀)) (Lz C (EuclideanSpace.single i 1))
    (Lz C (EuclideanSpace.single j 1)))

lemma hasFDerivAt_zf (C : Chart Ω) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (fun y => Lz C (y - C.x₀)) (Lz C) y := by
  have h := ((Lz C).hasFDerivAt (x := y)).sub_const (Lz C C.x₀)
  have e : (fun y => Lz C (y - C.x₀)) = fun y => Lz C y - Lz C C.x₀ := by
    funext y; exact map_sub _ _ _
  rw [e]; exact h

lemma hasFDerivAt_T (C : Chart Ω) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : DifferentiableAt ℝ C.u (Lz C (y - C.x₀))) :
    HasFDerivAt (Ch.T C) (C.α • ((fderiv ℝ C.u (Lz C (y - C.x₀))).comp (Lz C) - lastL C)) y := by
  have h1 := hu.hasFDerivAt.comp y (hasFDerivAt_zf C y)
  have h2 : HasFDerivAt (fun y => lastL C (y - C.x₀)) (lastL C) y := by
    have h := ((lastL C).hasFDerivAt (x := y)).sub_const (lastL C C.x₀)
    have e : (fun y => lastL C (y - C.x₀)) = fun y => lastL C y - lastL C C.x₀ := by
      funext y; exact map_sub _ _ _
    rw [e]; exact h
  have := (h1.sub h2).const_mul C.α
  rw [T_fun]; exact this

lemma hasFDerivAt_pj (C : Chart Ω) (j : Fin (n + 1)) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : DifferentiableAt ℝ (fun z => fderiv ℝ C.u z) (Lz C (y - C.x₀))) :
    HasFDerivAt (pj C j) (C.α • (((fderiv ℝ (fun z => fderiv ℝ C.u z) (Lz C (y - C.x₀))).flip
      (Lz C (EuclideanSpace.single j 1))).comp (Lz C))) y := by
  have h1 := (fderiv_apply_const hu (Lz C (EuclideanSpace.single j 1))).comp y (hasFDerivAt_zf C y)
  have := (h1.sub_const (lastL C (EuclideanSpace.single j 1))).const_mul C.α
  exact this

lemma zf_mem (C : Chart Ω) {r : ℝ} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ Metric.ball C.x₀ r) : Lz C (y - C.x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact (Lz_norm_le C _).trans_lt hy

/-- the cut-off data. -/
structure Cut (C : Chart Ω) where
  χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ
  r : ℝ
  rIn : ℝ
  hr : 0 < r
  hrδ : r ≤ C.δ1
  hrIn : 0 < rIn
  hχ : ContDiff ℝ 3 χ
  hcs : HasCompactSupport χ
  hsupp : tsupport χ ⊆ Metric.ball C.x₀ (r / 2)
  hone : ∀ y ∈ Metric.ball C.x₀ rIn, χ y = 1
  hrInr : rIn ≤ r / 2
  hu2 : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1, ContDiffAt ℝ 2 C.u z

variable {C : Chart Ω}

noncomputable def Cut.F (K : Cut C) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  K.χ y * Ch.T C y ^ 2

noncomputable def Cut.cj (K : Cut C) (j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  fderiv ℝ K.χ y (EuclideanSpace.single j 1)

noncomputable def Cut.cij (K : Cut C) (i j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  fderiv ℝ (K.cj j) y (EuclideanSpace.single i 1)

noncomputable def Cut.Φ (K : Cut C) (j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  K.cj j y * Ch.T C y ^ 2 + 2 * K.χ y * Ch.T C y * pj C j y

noncomputable def Cut.Ψ (K : Cut C) (i j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  K.cij i j y * Ch.T C y ^ 2 + K.cj j y * (2 * Ch.T C y * pj C i y) +
    2 * (K.cj i y * Ch.T C y * pj C j y + K.χ y * pj C i y * pj C j y +
      K.χ y * Ch.T C y * qij C i j y)

lemma Cut.mem_ball_of_supp (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ tsupport K.χ) : Lz C (y - C.x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 := by
  have h1 := K.hsupp hy
  have h2 : y ∈ Metric.ball C.x₀ C.δ1 :=
    Metric.ball_subset_ball (by linarith [K.hr, K.hrδ]) h1
  exact zf_mem C h2

lemma Cut.du (K : Cut C) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Metric.ball 0 C.δ1) :
    DifferentiableAt ℝ C.u z := (K.hu2 z hz).differentiableAt (by norm_num)

lemma Cut.ddu (K : Cut C) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Metric.ball 0 C.δ1) :
    DifferentiableAt ℝ (fun z => fderiv ℝ C.u z) z :=
  ((K.hu2 z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

lemma Cut.off (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∉ tsupport K.χ) :
    ∀ᶠ y' in 𝓝 y, K.χ y' = 0 ∧ fderiv ℝ K.χ y' = 0 := by
  have hO : ∀ᶠ y' in 𝓝 y, y' ∉ tsupport K.χ :=
    (isClosed_tsupport K.χ).isOpen_compl.mem_nhds hy
  filter_upwards [hO] with y' hy'
  have hev : K.χ =ᶠ[𝓝 y'] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy'
  exact ⟨hev.eq_of_nhds, by rw [hev.fderiv_eq]; simp⟩

lemma Cut.inner (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ Metric.ball C.x₀ K.rIn) :
    ∀ᶠ y' in 𝓝 y, K.χ y' = 1 ∧ fderiv ℝ K.χ y' = 0 := by
  have hO : ∀ᶠ y' in 𝓝 y, y' ∈ Metric.ball C.x₀ K.rIn := Metric.isOpen_ball.mem_nhds hy
  filter_upwards [hO] with y' hy'
  have hev : K.χ =ᶠ[𝓝 y'] fun _ => 1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy'] with x hx; exact K.hone x hx
  exact ⟨hev.eq_of_nhds, by rw [hev.fderiv_eq]; simp⟩

lemma Cut.cj_contDiff (K : Cut C) (j : Fin (n + 1)) : ContDiff ℝ 2 (K.cj j) := by
  have := (K.hχ.fderiv_right (m := 2) (by norm_num)).clm_apply
    (contDiff_const (c := (EuclideanSpace.single j (1:ℝ) : EuclideanSpace ℝ (Fin (n + 1)))))
  exact this

lemma Cut.fderiv_F (K : Cut C) (j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ K.F y (EuclideanSpace.single j 1) = K.Φ j y := by
  by_cases hy : y ∈ tsupport K.χ
  · have hz := K.mem_ball_of_supp hy
    have hT := hasFDerivAt_T C (K.du hz)
    have hχd := (K.hχ.differentiable (by norm_num) y).hasFDerivAt
    have := hχd.mul (hT.pow 2)
    have hd : HasFDerivAt K.F _ y := this
    rw [hd.fderiv]
    simp [Cut.Φ, Cut.cj, pj, smul_eq_mul]
    ring
  · have hev := K.off hy
    have hF : K.F =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with y' hy'; simp [Cut.F, hy'.1]
    rw [hF.fderiv_eq]
    have h0 := hev.self_of_nhds
    simp [Cut.Φ, Cut.cj, h0.1, h0.2]

lemma Cut.fderiv_Φ (K : Cut C) (i j : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (K.Φ j) y (EuclideanSpace.single i 1) = K.Ψ i j y := by
  by_cases hy : y ∈ tsupport K.χ
  · have hz := K.mem_ball_of_supp hy
    have hT := hasFDerivAt_T C (K.du hz)
    have hp := hasFDerivAt_pj C j (K.ddu hz)
    have hχd := (K.hχ.differentiable (by norm_num) y).hasFDerivAt
    have hcj := ((K.cj_contDiff j).differentiable (by norm_num) y).hasFDerivAt
    have := (hcj.mul (hT.pow 2)).add (((hχd.const_mul 2).mul hT).mul hp)
    have hd : HasFDerivAt (K.Φ j) _ y := this
    rw [hd.fderiv]
    simp [Cut.Ψ, Cut.cj, Cut.cij, pj, qij, smul_eq_mul]
    ring
  · have hev := K.off hy
    have hΦ : K.Φ j =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with y' hy'; simp [Cut.Φ, Cut.cj, hy'.1, hy'.2]
    rw [hΦ.fderiv_eq]
    have h0 := hev.self_of_nhds
    have hcj : K.cj j =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with y' hy'; simp [Cut.cj, hy'.2]
    have hcij : K.cij i j y = 0 := by simp [Cut.cij, hcj.fderiv_eq]
    simp [Cut.Ψ, Cut.cj, hcij, h0.1, h0.2]

lemma Cut.contDiff_F (K : Cut C) : ContDiff ℝ 2 K.F := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport K.χ
  · have hz := K.mem_ball_of_supp hy
    have haff : ContDiffAt ℝ 2 (fun y => Lz C (y - C.x₀)) y :=
      ((Lz C).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hl : ContDiffAt ℝ 2 (fun y => lastL C (y - C.x₀)) y :=
      ((lastL C).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hT : ContDiffAt ℝ 2 (Ch.T C) y := by
      rw [T_fun]
      exact contDiffAt_const.mul (((K.hu2 _ hz).comp y haff).sub hl)
    exact (K.hχ.contDiffAt.of_le (by norm_num)).mul (hT.pow 2)
  · have hev := K.off hy
    have hF : K.F =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with y' hy'; simp [Cut.F, hy'.1]
    exact contDiffAt_const.congr_of_eventuallyEq hF


lemma HB_of_cs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : ℝ}
    (hμ : 0 ≤ μ ∧ μ ≤ 1) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) (c : E) {r : ℝ}
    (hr : 0 < r) : HB (Metric.ball c r) μ φ := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hφ one_ne_zero
  exact HB_of_lip hμ L.2 (Dm := 2 * r)
    (fun y hy w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hy hw
      calc ‖y - w‖ = ‖(y - c) - (w - c)‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖w - c‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith)
    (fun y _ w _ => by
      have := hL.dist_le_mul y w; rwa [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at this)
    (M := |φ c| + L * r)
    (fun y hy => by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have h1 := hL.dist_le_mul y c
      rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at h1
      have h2 : |φ y| ≤ |φ y - φ c| + |φ c| := by
        have := abs_add_le (φ y - φ c) (φ c); simpa using this
      have h3 : (L : ℝ) * ‖y - c‖ ≤ L * r := mul_le_mul_of_nonneg_left hy.le L.2
      linarith)
    (by positivity)

lemma Cut.vals_off (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∉ tsupport K.χ)
    (i j : Fin (n + 1)) : K.χ y = 0 ∧ K.cj j y = 0 ∧ K.cij i j y = 0 := by
  have hev := K.off hy
  have h0 := hev.self_of_nhds
  have hcj : K.cj j =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hev] with y' hy'; simp [Cut.cj, hy'.2]
  refine ⟨h0.1, by simp [Cut.cj, h0.2], by simp [Cut.cij, hcj.fderiv_eq]⟩

lemma Cut.Ψ_off (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∉ tsupport K.χ)
    (i j : Fin (n + 1)) : K.Ψ i j y = 0 := by
  obtain ⟨h1, h2, h3⟩ := K.vals_off hy i j
  obtain ⟨_, h4, _⟩ := K.vals_off hy j i
  simp [Cut.Ψ, h1, h2, h3, h4]

lemma Cut.Φ_off (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∉ tsupport K.χ)
    (j : Fin (n + 1)) : K.Φ j y = 0 := by
  obtain ⟨h1, h2, _⟩ := K.vals_off hy j j
  simp [Cut.Φ, h1, h2]

lemma Cut.HB_T (K : Cut C) {μ : ℝ} (hμ : 0 ≤ μ ∧ μ ≤ 1) :
    HB (Metric.ball C.x₀ K.r) μ (Ch.T C) := by
  have hb : ∀ y ∈ Metric.ball C.x₀ K.r, ‖y - C.x₀‖ < C.δ1 := fun y hy => by
    rw [Metric.mem_ball, dist_eq_norm] at hy; linarith [K.hrδ]
  refine HB_of_lip hμ (L := 2) (Dm := 2 * K.r) (M := 2 * K.r) (by norm_num) ?_ ?_ ?_ (by linarith [K.hr])
  · intro y hy w hw
    rw [Metric.mem_ball, dist_eq_norm] at hy hw
    calc ‖y - w‖ = ‖(y - C.x₀) - (w - C.x₀)‖ := by congr 1; abel
      _ ≤ ‖y - C.x₀‖ + ‖w - C.x₀‖ := norm_sub_le _ _
      _ ≤ 2 * K.r := by linarith
  · intro y hy w hw; exact T_lip C (hb y hy) (hb w hw)
  · intro y hy
    have := T_lip C (y := C.x₀) (hb y hy) (by simpa using C.hδ1)
    rw [T_x0, sub_zero] at this
    have hy' := hy; rw [Metric.mem_ball, dist_eq_norm] at hy'
    linarith

lemma Cut.HB_pj (K : Cut C) {μ : ℝ} (hμ : 0 ≤ μ ∧ μ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖) (j : Fin (n + 1)) :
    HB (Metric.ball C.x₀ K.r) μ (pj C j) := by
  have hαa := abs_of_sq_one C.hα
  have hlip : ∀ y ∈ Metric.ball C.x₀ K.r, ∀ w ∈ Metric.ball C.x₀ K.r,
      |pj C j y - pj C j w| ≤ L * ‖y - w‖ := by
    intro y hy w hw
    have h1 := hL _ (zf_mem C hy) _ (zf_mem C hw)
    have h2 : Lz C (y - C.x₀) - Lz C (w - C.x₀) = Lz C (y - w) := by
      rw [← map_sub]; congr 1; abel
    rw [h2] at h1
    have h3 := (Lz_norm_le C (y - w))
    have h4 : ‖Lz C (EuclideanSpace.single j (1:ℝ))‖ ≤ 1 := by
      have := Lz_norm_le C (EuclideanSpace.single j (1:ℝ)); simpa using this
    have h5 := (fderiv ℝ C.u (Lz C (y - C.x₀)) - fderiv ℝ C.u (Lz C (w - C.x₀))).le_opNorm
      (Lz C (EuclideanSpace.single j 1))
    unfold pj
    rw [← mul_sub, abs_mul, hαa, one_mul]
    have e : fderiv ℝ C.u (Lz C (y - C.x₀)) (Lz C (EuclideanSpace.single j 1)) -
        lastL C (EuclideanSpace.single j 1) -
        (fderiv ℝ C.u (Lz C (w - C.x₀)) (Lz C (EuclideanSpace.single j 1)) -
          lastL C (EuclideanSpace.single j 1)) =
        (fderiv ℝ C.u (Lz C (y - C.x₀)) - fderiv ℝ C.u (Lz C (w - C.x₀)))
          (Lz C (EuclideanSpace.single j 1)) := by
      simp
    rw [e, ← Real.norm_eq_abs]
    calc _ ≤ _ := h5
      _ ≤ (L * ‖Lz C (y - w)‖) * 1 := by
          apply mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
      _ ≤ L * ‖y - w‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h3 hL0
  have hx₀ : C.x₀ ∈ Metric.ball C.x₀ K.r := Metric.mem_ball_self K.hr
  refine HB_of_lip hμ hL0 (Dm := 2 * K.r) (M := |pj C j C.x₀| + L * K.r) ?_ hlip ?_
    (add_nonneg (abs_nonneg _) (mul_nonneg hL0 K.hr.le))
  · intro y hy w hw
    rw [Metric.mem_ball, dist_eq_norm] at hy hw
    calc ‖y - w‖ = ‖(y - C.x₀) - (w - C.x₀)‖ := by congr 1; abel
      _ ≤ ‖y - C.x₀‖ + ‖w - C.x₀‖ := norm_sub_le _ _
      _ ≤ 2 * K.r := by linarith
  · intro y hy
    have h1 := hlip y hy _ hx₀
    have h2 : |pj C j y| ≤ |pj C j y - pj C j C.x₀| + |pj C j C.x₀| := by
      have := abs_add_le (pj C j y - pj C j C.x₀) (pj C j C.x₀); simpa using this
    have hy' := hy; rw [Metric.mem_ball, dist_eq_norm] at hy'
    have h3 : L * ‖y - C.x₀‖ ≤ L * K.r := mul_le_mul_of_nonneg_left hy'.le hL0
    linarith

lemma Cut.HB_qij (K : Cut C) {μ : ℝ} (hμ : 0 ≤ μ ∧ μ ≤ 1)
    (hq : ∀ k l : Fin n, HB (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r) μ
      (fun z => fderiv ℝ (fun y => fderiv ℝ C.u y (EuclideanSpace.single l 1)) z
        (EuclideanSpace.single k 1))) (i j : Fin (n + 1)) :
    HB (Metric.ball C.x₀ K.r) μ (qij C i j) := by
  have hcomp : ∀ k l : Fin n, HB (Metric.ball C.x₀ K.r) μ (fun y =>
      fderiv ℝ (fun y => fderiv ℝ C.u y (EuclideanSpace.single l 1)) (Lz C (y - C.x₀))
        (EuclideanSpace.single k 1)) := by
    intro k l
    refine (hq k l).comp hμ.1 (fun y hy => zf_mem C hy) (fun y _ w _ => ?_)
    have h2 : Lz C (y - C.x₀) - Lz C (w - C.x₀) = Lz C (y - w) := by
      rw [← map_sub]; congr 1; abel
    rw [h2]; exact Lz_norm_le C _
  have hsum := (HB.sum (A := Metric.ball C.x₀ K.r) (μ := μ) Finset.univ (fun k _ =>
    HB.sum Finset.univ (fun l _ => ((hcomp k l).const_mul
      (Lz C (EuclideanSpace.single i 1) k * Lz C (EuclideanSpace.single j 1) l))))).const_mul C.α
  refine hsum.congr fun y hy => ?_
  have hz : Lz C (y - C.x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 :=
    Metric.ball_subset_ball K.hrδ (zf_mem C hy)
  unfold qij
  rw [second_expand (K.ddu hz)]

lemma Cut.HB_Ψ (K : Cut C) {μ : ℝ} (hμ : 0 ≤ μ ∧ μ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖)
    (hq : ∀ k l : Fin n, HB (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r) μ
      (fun z => fderiv ℝ (fun y => fderiv ℝ C.u y (EuclideanSpace.single l 1)) z
        (EuclideanSpace.single k 1))) (i j : Fin (n + 1)) :
    HB (Metric.ball C.x₀ K.r) μ (K.Ψ i j) := by
  have hcs1 : ∀ j, HasCompactSupport (K.cj j) := fun j => K.hcs.fderiv_apply (𝕜 := ℝ) _
  have hχ := HB_of_cs hμ (K.hχ.of_le (by norm_num)) K.hcs C.x₀ K.hr
  have hc : ∀ j, HB (Metric.ball C.x₀ K.r) μ (K.cj j) := fun j =>
    HB_of_cs hμ ((K.cj_contDiff j).of_le (by norm_num)) (hcs1 j) C.x₀ K.hr
  have hcc : HB (Metric.ball C.x₀ K.r) μ (K.cij i j) := by
    have h1 : ContDiff ℝ 1 (K.cij i j) :=
      ((K.cj_contDiff j).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact HB_of_cs hμ h1 ((hcs1 j).fderiv_apply (𝕜 := ℝ) _) C.x₀ K.hr
  have hT := K.HB_T hμ
  have hpi := K.HB_pj hμ hL0 hL i
  have hpj := K.HB_pj hμ hL0 hL j
  have hqq := K.HB_qij hμ hq i j
  have h1 := (hcc.mul (hT.mul hT)).add ((hc j).mul ((hT.const_mul 2).mul hpi))
  have h2 := ((((hc i).mul hT).mul hpj).add ((hχ.mul hpi).mul hpj)).add ((hχ.mul hT).mul hqq)
  have := h1.add (h2.const_mul 2)
  refine this.congr fun y _ => ?_
  simp only [Cut.Ψ]; ring

lemma Cut.glob_Ψ (K : Cut C) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖)
    (hq : ∀ k l : Fin n, HB (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r) μ
      (fun z => fderiv ℝ (fun y => fderiv ℝ C.u y (EuclideanSpace.single l 1)) z
        (EuclideanSpace.single k 1))) (i j : Fin (n + 1)) :
    ∃ Kc, 0 ≤ Kc ∧ ∀ y w : EuclideanSpace ℝ (Fin (n + 1)),
      |K.Ψ i j y - K.Ψ i j w| ≤ Kc * ‖y - w‖ ^ μ := by
  have h := (K.HB_Ψ ⟨hμ.1.le, hμ.2⟩ hL0 hL hq i j).mono (Set.inter_subset_right (s := Set.univ))
  obtain ⟨Kc, hKc, hb⟩ := HB.glob hμ.1 K.hr h (fun y _ hy => K.Ψ_off (fun hs => by
    have := K.hsupp hs; rw [Metric.mem_ball, dist_eq_norm] at this; linarith) i j)
  exact ⟨Kc, hKc, fun y w => hb y trivial w trivial⟩

lemma Cut.Φ_eq (K : Cut C) (j : Fin (n + 1)) :
    K.Φ j = fun y => fderiv ℝ K.F y (EuclideanSpace.single j 1) := by
  funext y; rw [K.fderiv_F]

lemma Cut.Ψ_eq (K : Cut C) (i j : Fin (n + 1)) :
    K.Ψ i j = fun y => fderiv ℝ (K.Φ j) y (EuclideanSpace.single i 1) := by
  funext y; rw [K.fderiv_Φ]

lemma Cut.contDiff_Φ (K : Cut C) (j : Fin (n + 1)) : ContDiff ℝ 1 (K.Φ j) := by
  rw [K.Φ_eq]
  exact (K.contDiff_F.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma Cut.continuous_Ψ (K : Cut C) (i j : Fin (n + 1)) : Continuous (K.Ψ i j) := by
  rw [K.Ψ_eq]
  exact ((K.contDiff_Φ j).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- R agrees with F on Ω: R's second partials are the Ψ's there. -/
lemma Cut.R_second (K : Cut C) (hopen : IsOpen Ω) {R : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hR : ∀ y ∈ Ω, R y = K.F y) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Ω) (i j : Fin (n + 1)) :
    fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      K.Ψ i j x ∧ fderiv ℝ R x = fderiv ℝ K.F x := by
  have hev : ∀ y ∈ Ω, fderiv ℝ R y = fderiv ℝ K.F y := fun y hy => by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hy] with z hz; exact hR z hz
  have h1 : (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x] K.Φ j := by
    filter_upwards [hopen.mem_nhds hx] with z hz; rw [hev z hz, K.fderiv_F]
  refine ⟨?_, hev x hx⟩
  rw [h1.fderiv_eq, K.fderiv_Φ]

lemma Cut.ctwice (K : Cut C) (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    {R : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hR : ∀ y ∈ Ω, R y = K.F y)
    (hglob : ∀ i j : Fin (n + 1), ∃ Kc, 0 ≤ Kc ∧ ∀ y w : EuclideanSpace ℝ (Fin (n + 1)),
      |K.Ψ i j y - K.Ψ i j w| ≤ Kc * ‖y - w‖ ^ μ) :
    CTwiceHolder Ω μ R := by
  refine ⟨K.contDiff_F.contDiffOn.congr (fun y hy => hR y hy), fun i j => ?_⟩
  obtain ⟨Kc, hKc, hb⟩ := hglob i j
  refine ⟨(K.continuous_Ψ i j).continuousOn.congr (fun x hx => (K.R_second hopen hR hx i j).1),
    1, Kc * 2 ^ μ, one_pos, by positivity, fun ρ hρ _ x z _ y hy w hw => ?_⟩
  have hy' := connectedComponentIn_subset _ _ hy
  have hw' := connectedComponentIn_subset _ _ hw
  beta_reduce
  rw [(K.R_second hopen hR hy'.1 i j).1, (K.R_second hopen hR hw'.1 i j).1]
  have hyw : ‖y - w‖ ≤ 2 * ρ := by
    have h1 := hy'.2; have h2 := hw'.2
    rw [Metric.mem_ball, dist_eq_norm] at h1 h2
    calc ‖y - w‖ = ‖(y - x) - (w - x)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖w - x‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith
  calc |K.Ψ i j y - K.Ψ i j w| ≤ Kc * ‖y - w‖ ^ μ := hb y w
    _ ≤ Kc * (2 * ρ) ^ μ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyw hμ.1.le) hKc
    _ = Kc * 2 ^ μ * ρ ^ μ := by rw [Real.mul_rpow (by norm_num) hρ.le]; ring


lemma CH_HB (C : Chart Ω) (hopen : IsOpen Ω) {μ : ℝ} (hμ0 : 0 ≤ μ)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : ComponentHolder Ω μ φ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), HB (Ω ∩ Metric.ball C.x₀ r) μ φ := by
  obtain ⟨ρ₀, M, hρ₀, hM, hb⟩ := CH_apply C hopen hφ
  set r0 := min (C.δ1 / 16) (ρ₀ / 10) with hr0def
  have hr0 : 0 < r0 := lt_min (by linarith [C.hδ1]) (by linarith)
  have hmain : HB (Ω ∩ Metric.ball C.x₀ r0) μ φ := by
    apply HB_of_hol hμ0 (K := M * 5 ^ μ) (Dm := 2 * r0) (by positivity)
    · intro y hy w hw
      have h1 := hy.2; have h2 := hw.2
      rw [Metric.mem_ball, dist_eq_norm] at h1 h2
      calc ‖y - w‖ = ‖(y - C.x₀) - (w - C.x₀)‖ := by congr 1; abel
        _ ≤ ‖y - C.x₀‖ + ‖w - C.x₀‖ := norm_sub_le _ _
        _ ≤ 2 * r0 := by linarith
    · intro y hy w hw
      rcases eq_or_ne y w with rfl | hne
      · simp only [sub_self, abs_zero, norm_zero]; positivity
      have hpos : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have h1 := hy.2; have h2 := hw.2
      rw [Metric.mem_ball, dist_eq_norm] at h1 h2
      have hyw : ‖y - w‖ ≤ ‖y - C.x₀‖ + ‖w - C.x₀‖ := by
        calc ‖y - w‖ = ‖(y - C.x₀) - (w - C.x₀)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have hr1 : r0 ≤ C.δ1 / 16 := min_le_left _ _
      have hr2 : r0 ≤ ρ₀ / 10 := min_le_right _ _
      have := hb y hy.1 w hw.1 (by linarith) (by linarith) hpos (by linarith)
      calc |φ y - φ w| ≤ M * (5 * ‖y - w‖) ^ μ := this
        _ = M * 5 ^ μ * ‖y - w‖ ^ μ := by
            rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring
  filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
  exact hmain.mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hr.2.le))

lemma Cut.HB_Φ (K : Cut C) {μ : ℝ} (hμ : 0 ≤ μ ∧ μ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖) (j : Fin (n + 1)) :
    HB (Metric.ball C.x₀ K.r) μ (K.Φ j) := by
  have hcs1 : HasCompactSupport (K.cj j) := K.hcs.fderiv_apply (𝕜 := ℝ) _
  have hχ := HB_of_cs hμ (K.hχ.of_le (by norm_num)) K.hcs C.x₀ K.hr
  have hc := HB_of_cs hμ ((K.cj_contDiff j).of_le (by norm_num)) hcs1 C.x₀ K.hr
  have hT := K.HB_T hμ
  have hpj := K.HB_pj hμ hL0 hL j
  have := (hc.mul (hT.mul hT)).add (((hχ.const_mul 2).mul hT).mul hpj)
  refine this.congr fun y _ => ?_
  simp only [Cut.Φ]; ring

noncomputable def Cut.gΩ (K : Cut C)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, a y i j * K.Ψ i j y) + ∑ i, b y i * K.Φ i y

lemma Cut.g_formula (K : Cut C) (hopen : IsOpen Ω)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {R : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hR : ∀ y ∈ Ω, R y = K.F y)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Ω) :
    (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      a x i j * fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ R x (b x) = K.gΩ a b x := by
  unfold Cut.gΩ
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(K.R_second hopen hR hx i j).1]
  · rw [(K.R_second hopen hR hx 0 0).2, clm_expand]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [K.fderiv_F]

lemma Cut.glob_g (K : Cut C) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖)
    (hq : ∀ k l : Fin n, HB (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r) μ
      (fun z => fderiv ℝ (fun y => fderiv ℝ C.u y (EuclideanSpace.single l 1)) z
        (EuclideanSpace.single k 1)))
    (ha : ∀ i j, HB (Ω ∩ Metric.ball C.x₀ K.r) μ (fun x => a x i j))
    (hb : ∀ i, HB (Ω ∩ Metric.ball C.x₀ K.r) μ (fun x => b x i)) :
    ∃ Kg, 0 ≤ Kg ∧ ∀ y ∈ Ω, ∀ w ∈ Ω, |K.gΩ a b y - K.gΩ a b w| ≤ Kg * ‖y - w‖ ^ μ := by
  have hμ' : 0 ≤ μ ∧ μ ≤ 1 := ⟨hμ.1.le, hμ.2⟩
  have h1 := (HB.sum Finset.univ (fun i _ => HB.sum Finset.univ (fun j _ =>
    (ha i j).mul ((K.HB_Ψ hμ' hL0 hL hq i j).mono Set.inter_subset_right)))).const_mul (1 / 2 : ℝ)
  have h2 := HB.sum Finset.univ (fun i _ =>
    (hb i).mul ((K.HB_Φ hμ' hL0 hL i).mono (Set.inter_subset_right (s := Ω))))
  have h3 := h1.add h2
  refine HB.glob hμ.1 K.hr (h3.congr fun y _ => rfl) (fun y _ hy => ?_)
  have hs : y ∉ tsupport K.χ := fun hs => by
    have := K.hsupp hs; rw [Metric.mem_ball, dist_eq_norm] at this; linarith
  simp [Cut.gΩ, K.Ψ_off hs, K.Φ_off hs]

lemma holderWith_of_le {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {K : NNReal} {μ : ℝ}
    (hμ : 0 ≤ μ) (h : ∀ x y, |f x - f y| ≤ K * dist x y ^ μ) : HolderWith K ⟨μ, hμ⟩ f := by
  intro x y
  rw [edist_dist, edist_dist, Real.dist_eq]
  change ENNReal.ofReal |f x - f y| ≤ ↑K * ENNReal.ofReal (dist x y) ^ μ
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hμ, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)]
  exact ENNReal.ofReal_le_ofReal (h x y)

lemma HolderWith.abs_le' {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {K r : NNReal}
    (h : HolderWith K r f) (x y : X) : |f x - f y| ≤ K * dist x y ^ (r : ℝ) := by
  have := h.edist_le x y
  rw [edist_dist, edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg r),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)] at this
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this

/-- Hölder functions on S extend to closure S with the same constant. -/
lemma holder_ext {E : Type*} [NormedAddCommGroup E] {S : Set E} {g : E → ℝ} {Kg μ : ℝ}
    (hμ : 0 < μ) (hK : 0 ≤ Kg) (hg : ∀ y ∈ S, ∀ w ∈ S, |g y - g w| ≤ Kg * ‖y - w‖ ^ μ) :
    (∀ x ∈ S, extendFrom S g x = g x) ∧
      ∀ p ∈ closure S, ∀ q ∈ closure S,
        |extendFrom S g p - extendFrom S g q| ≤ Kg * ‖p - q‖ ^ μ := by
  have hcont : ∀ x ∈ S, Tendsto g (𝓝[S] x) (𝓝 (g x)) := by
    intro x hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, Kg * δ ^ μ < ε := by
      have ht : Tendsto (fun δ : ℝ => Kg * δ ^ μ) (𝓝[>] 0) (𝓝 (Kg * 0 ^ μ)) :=
        ((continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hμ.le)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      rw [Real.zero_rpow hμ.ne', mul_zero] at ht
      exact ((ht.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists.imp
        fun δ h => ⟨h.2, h.1⟩
    filter_upwards [inter_mem_nhdsWithin S (Metric.ball_mem_nhds x hδ)] with y hy
    rw [Real.dist_eq]
    have hyx : ‖y - x‖ < δ := by have := hy.2; rwa [Metric.mem_ball, dist_eq_norm] at this
    calc |g y - g x| ≤ Kg * ‖y - x‖ ^ μ := hg y hy.1 x hx
      _ ≤ Kg * δ ^ μ := by gcongr
      _ < ε := hδε
  have hlim : ∀ x ∈ closure S, Tendsto g (𝓝[S] x) (𝓝 (extendFrom S g x)) := by
    intro x hx
    apply tendsto_extendFrom
    have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
    apply cauchy_map_iff_exists_tendsto.1
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, Kg * (2 * δ) ^ μ < ε := by
      have ht : Tendsto (fun δ : ℝ => Kg * (2 * δ) ^ μ) (𝓝[>] 0) (𝓝 (Kg * (2 * 0) ^ μ)) :=
        ((continuous_const.mul ((continuous_const.mul continuous_id).rpow_const
          fun _ => Or.inr hμ.le)).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [mul_zero, Real.zero_rpow hμ.ne', mul_zero] at ht
      exact ((ht.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists.imp
        fun δ h => ⟨h.2, h.1⟩
    refine ⟨g '' (S ∩ Metric.ball x δ), Filter.image_mem_map
      (inter_mem_nhdsWithin S (Metric.ball_mem_nhds x hδ)), ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [Real.dist_eq]
    have h1 := hy.2; have h2 := hw.2
    rw [Metric.mem_ball, dist_eq_norm] at h1 h2
    have hyw : ‖y - w‖ ≤ 2 * δ := by
      calc ‖y - w‖ = ‖(y - x) - (w - x)‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖w - x‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by linarith
    calc |g y - g w| ≤ Kg * ‖y - w‖ ^ μ := hg y hy.1 w hw.1
      _ ≤ Kg * (2 * δ) ^ μ := by gcongr
      _ < ε := hδε
  refine ⟨fun x hx => extendFrom_eq (subset_closure hx) (hcont x hx), fun p hp q hq => ?_⟩
  have : (𝓝[S] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hp
  have : (𝓝[S] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hq
  have t1 : Tendsto (fun yw : E × E => |g yw.1 - g yw.2|) (𝓝[S] p ×ˢ 𝓝[S] q)
      (𝓝 |extendFrom S g p - extendFrom S g q|) :=
    (((hlim p hp).comp tendsto_fst).sub ((hlim q hq).comp tendsto_snd)).abs
  have t2 : Tendsto (fun yw : E × E => Kg * ‖yw.1 - yw.2‖ ^ μ) (𝓝[S] p ×ˢ 𝓝[S] q)
      (𝓝 (Kg * ‖p - q‖ ^ μ)) := by
    have hc : Continuous (fun yw : E × E => Kg * ‖yw.1 - yw.2‖ ^ μ) :=
      continuous_const.mul ((continuous_fst.sub continuous_snd).norm.rpow_const
        fun _ => Or.inr hμ.le)
    refine (hc.tendsto (p, q)).mono_left ?_
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto t1 t2 ?_
  filter_upwards [prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin] with yw hyw
  exact hg _ hyw.1 _ hyw.2


lemma vanish_hasFDerivAt' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K G : E → ℝ} {y : E} (hKG : ∀ᶠ z in 𝓝 y, |K z| ≤ |G z|) (hG0 : G y = 0)
    (hG : HasFDerivAt G (0 : E →L[ℝ] ℝ) y) : HasFDerivAt K (0 : E →L[ℝ] ℝ) y := by
  have hK0 : K y = 0 := by
    have := hKG.self_of_nhds; rw [hG0, abs_zero] at this; exact abs_nonpos_iff.mp this
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hG ⊢
  have hKG' : ∀ᶠ h in 𝓝 (0:E), |K (y + h)| ≤ |G (y + h)| := by
    have : Tendsto (fun h => y + h) (𝓝 0) (𝓝 y) := by
      have := (continuous_const_add y).tendsto 0; simpa using this
    exact this.eventually hKG
  have h1 : (fun h => K (y + h) - K y - (0 : E →L[ℝ] ℝ) h) =O[𝓝 0]
      (fun h => G (y + h) - G y - (0 : E →L[ℝ] ℝ) h) :=
    Asymptotics.IsBigO.of_bound 1 (hKG'.mono fun h hh => by
      simp [hK0, hG0, Real.norm_eq_abs, hh])
  exact h1.trans_isLittleO hG

lemma Cut.pj_lip (K : Cut C) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖) (j : Fin (n + 1)) :
    ∀ y ∈ Metric.ball C.x₀ K.r, ∀ w ∈ Metric.ball C.x₀ K.r,
      |pj C j y - pj C j w| ≤ L * ‖y - w‖ := by
  have hαa := abs_of_sq_one C.hα
  intro y hy w hw
  have h1 := hL _ (zf_mem C hy) _ (zf_mem C hw)
  have h2 : Lz C (y - C.x₀) - Lz C (w - C.x₀) = Lz C (y - w) := by
    rw [← map_sub]; congr 1; abel
  rw [h2] at h1
  have h3 := (Lz_norm_le C (y - w))
  have h4 : ‖Lz C (EuclideanSpace.single j (1:ℝ))‖ ≤ 1 := by
    have := Lz_norm_le C (EuclideanSpace.single j (1:ℝ)); simpa using this
  have h5 := (fderiv ℝ C.u (Lz C (y - C.x₀)) - fderiv ℝ C.u (Lz C (w - C.x₀))).le_opNorm
    (Lz C (EuclideanSpace.single j 1))
  unfold pj
  rw [← mul_sub, abs_mul, hαa, one_mul]
  have e : fderiv ℝ C.u (Lz C (y - C.x₀)) (Lz C (EuclideanSpace.single j 1)) -
      lastL C (EuclideanSpace.single j 1) -
      (fderiv ℝ C.u (Lz C (w - C.x₀)) (Lz C (EuclideanSpace.single j 1)) -
        lastL C (EuclideanSpace.single j 1)) =
      (fderiv ℝ C.u (Lz C (y - C.x₀)) - fderiv ℝ C.u (Lz C (w - C.x₀)))
        (Lz C (EuclideanSpace.single j 1)) := by
    simp
  rw [e, ← Real.norm_eq_abs]
  calc _ ≤ _ := h5
    _ ≤ (L * ‖Lz C (y - w)‖) * 1 := by
        apply mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
    _ ≤ L * ‖y - w‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h3 hL0

lemma Cut.F_frontier (K : Cut C) (hopen : IsOpen Ω) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ frontier Ω) :
    K.F y = 0 ∧ HasFDerivAt K.F (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) y := by
  by_cases hs : y ∈ tsupport K.χ
  · have hz := K.mem_ball_of_supp hs
    have hyb : ‖y - C.x₀‖ < C.δ1 := by
      have := K.hsupp hs; rw [Metric.mem_ball, dist_eq_norm] at this; linarith [K.hrδ, K.hr]
    have hc := char C hopen hyb
    rw [hopen.frontier_eq] at hy
    have hT0 : Ch.T C y = 0 := le_antisymm (not_lt.1 fun h => hy.2 (hc.1.2 h)) (hc.2.1 hy.1)
    have hT := hasFDerivAt_T C (K.du hz)
    have hχd := (K.hχ.differentiable (by norm_num) y).hasFDerivAt
    have := hχd.mul (hT.pow 2)
    have hd : HasFDerivAt K.F _ y := this
    refine ⟨by simp [Cut.F, hT0], ?_⟩
    simpa [hT0] using hd
  · have hev := K.off hs
    have hF : K.F =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with y' hy'; simp [Cut.F, hy'.1]
    exact ⟨hF.self_of_nhds, (hasFDerivAt_const (0:ℝ) y).congr_of_eventuallyEq hF⟩

lemma Cut.vals_in (K : Cut C) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ Metric.ball C.x₀ K.rIn)
    (i j : Fin (n + 1)) : K.χ y = 1 ∧ K.cj j y = 0 ∧ K.cij i j y = 0 := by
  have hev := K.inner hy
  have h0 := hev.self_of_nhds
  have hcj : K.cj j =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hev] with y' hy'; simp [Cut.cj, hy'.2]
  refine ⟨h0.1, by simp [Cut.cj, h0.2], by simp [Cut.cij, hcj.fderiv_eq]⟩

lemma Cut.line_T (K : Cut C) (t : ℝ) : Ch.T C (C.x₀ + t • C.ν) = -t := by
  have := T_shift C C.x₀ (-t)
  rw [neg_smul, sub_neg_eq_add, T_x0, zero_add] at this
  exact this

lemma Cut.line_norm (C : Chart Ω) (t : ℝ) : ‖(C.x₀ + t • C.ν) - C.x₀‖ = |t| := by
  rw [add_sub_cancel_left, norm_smul, C.hνn, mul_one, Real.norm_eq_abs]

/-- the second-order term of S vanishes at x₀. -/
lemma Cut.phi_zero (K : Cut C) (hopen : IsOpen Ω) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖) (j : Fin (n + 1))
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφΩ : ∀ y ∈ Ω, φ y = K.Φ j y)
    (hφ0 : ∀ y ∉ Ω, φ y = 0) : fderiv ℝ φ C.x₀ = 0 := by
  have hrIn := K.hrIn
  have hrr : K.rIn < C.δ1 := by linarith [K.hrInr, K.hrδ, K.hr]
  have hx₀Ω : C.x₀ ∉ Ω := fun h => by
    have := (char C hopen (by simpa using C.hδ1)).1.1 h; rw [T_x0] at this; exact lt_irrefl _ this
  have hφx₀ : φ C.x₀ = 0 := hφ0 _ hx₀Ω
  -- φ = 2 T p on Ω near x₀
  have hnear : ∀ y ∈ Metric.ball C.x₀ K.rIn, y ∈ Ω → φ y = 2 * Ch.T C y * pj C j y := by
    intro y hy hyΩ
    obtain ⟨h1, h2, _⟩ := K.vals_in hy j j
    rw [hφΩ y hyΩ]; simp [Cut.Φ, h1, h2]
  have hball : ∀ y ∈ Metric.ball C.x₀ K.rIn, y ∈ Metric.ball C.x₀ K.r := fun y hy =>
    Metric.ball_subset_ball (by linarith [K.hrInr, K.hr]) hy
  by_cases hd : DifferentiableAt ℝ φ C.x₀
  · have hp0 : pj C j C.x₀ = 0 := by
      set Lφ := fderiv ℝ φ C.x₀
      have h1 : HasDerivAt (fun t : ℝ => C.x₀ + t • C.ν) C.ν 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const C.ν).const_add C.x₀
      have hline : HasDerivAt (fun t : ℝ => φ (C.x₀ + t • C.ν)) (Lφ C.ν) 0 :=
        hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (by simp)
      have hR := hline.tendsto_slope_zero_right
      have hLt := hline.tendsto_slope_zero_left
      simp only [zero_add, zero_smul, add_zero, hφx₀, sub_zero, smul_eq_mul] at hR hLt
      have hR' : Tendsto (fun t : ℝ => t⁻¹ * φ (C.x₀ + t • C.ν)) (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hrIn] with t ht
        have hnc : C.x₀ + t • C.ν ∉ closure Ω := by
          intro hc
          have := (char C hopen (by rw [Cut.line_norm, abs_of_pos ht.1]; linarith [ht.2])).2.1 hc
          rw [K.line_T] at this; linarith [ht.1]
        rw [hφ0 _ (fun h => hnc (subset_closure h)), mul_zero]
      have hpc : ContinuousAt (pj C j) C.x₀ := by
        have hz : Lz C (C.x₀ - C.x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 :=
          zf_mem C (Metric.mem_ball_self C.hδ1)
        exact (hasFDerivAt_pj C j (K.ddu hz)).continuousAt
      have hlc : Tendsto (fun t : ℝ => C.x₀ + t • C.ν) (𝓝[<] 0) (𝓝 C.x₀) := by
        have : Continuous (fun t : ℝ => C.x₀ + t • C.ν) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have hL' : Tendsto (fun t : ℝ => t⁻¹ * φ (C.x₀ + t • C.ν)) (𝓝[<] 0)
          (𝓝 (-2 * pj C j C.x₀)) := by
        have := ((hpc.tendsto.comp hlc).const_mul (-2))
        refine this.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT (show -K.rIn < 0 by linarith)] with t ht
        have hyb : C.x₀ + t • C.ν ∈ Metric.ball C.x₀ K.rIn := by
          rw [Metric.mem_ball, dist_eq_norm, Cut.line_norm, abs_of_neg ht.2]; linarith [ht.1]
        have hyΩ : C.x₀ + t • C.ν ∈ Ω := by
          apply (char C hopen (by rw [Cut.line_norm, abs_of_neg ht.2]; linarith [ht.1])).1.2
          rw [K.line_T]; linarith [ht.2]
        rw [hnear _ hyb hyΩ, K.line_T]
        simp only [Function.comp]
        field_simp [ht.2.ne]
      have e1 := tendsto_nhds_unique hR hR'
      have e2 := tendsto_nhds_unique hLt hL'
      linarith
    have hdom : ∀ᶠ y in 𝓝 C.x₀, |φ y| ≤ |4 * L * ‖y - C.x₀‖ ^ 2| := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrIn)] with y hy
      have hnn : 0 ≤ 4 * L * ‖y - C.x₀‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hL0) (sq_nonneg _)
      rw [abs_of_nonneg hnn]
      by_cases hyΩ : y ∈ Ω
      · rw [hnear y hy hyΩ]
        have hyb : ‖y - C.x₀‖ < C.δ1 := by
          rw [Metric.mem_ball, dist_eq_norm] at hy; linarith
        have hT := T_lip C (y := C.x₀) hyb (by simpa using C.hδ1)
        rw [T_x0, sub_zero] at hT
        have hp := K.pj_lip hL0 hL j y (hball y hy) C.x₀ (Metric.mem_ball_self K.hr)
        rw [hp0, sub_zero] at hp
        rw [abs_mul, abs_mul, abs_two]
        have := mul_le_mul hT hp (abs_nonneg _) (by positivity)
        nlinarith [norm_nonneg (y - C.x₀)]
      · rw [hφ0 y hyΩ, abs_zero]; exact hnn
    have hG : HasFDerivAt (fun y => 4 * L * ‖y - C.x₀‖ ^ 2)
        (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) C.x₀ := by
      have := (((hasFDerivAt_id C.x₀).sub_const C.x₀).norm_sq).const_mul (4 * L)
      simpa using this
    exact (vanish_hasFDerivAt' hdom (by simp) hG).fderiv
  · exact fderiv_zero_of_not_differentiableAt hd

lemma Cut.R_facts (K : Cut C) (hopen : IsOpen Ω) (f : closure Ω →ᵇ ℝ)
    (hf : ∀ y : closure Ω, f y = K.F y) :
    (∀ y ∈ closure Ω, closedRegionRestriction f y = K.F y) ∧
    (∀ y ∉ closure Ω, closedRegionRestriction f y = 0) ∧
    (∀ y ∉ Ω, HasFDerivAt (closedRegionRestriction f)
      (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) y) := by
  have h1 : ∀ y ∈ closure Ω, closedRegionRestriction f y = K.F y := fun y hy => by
    simp only [closedRegionRestriction, dif_pos hy]; exact hf ⟨y, hy⟩
  have h2 : ∀ y ∉ closure Ω, closedRegionRestriction f y = 0 := fun y hy => by
    simp only [closedRegionRestriction, dif_neg hy]
  refine ⟨h1, h2, fun y hy => ?_⟩
  by_cases hc : y ∈ closure Ω
  · have hfr : y ∈ frontier Ω := by rw [hopen.frontier_eq]; exact ⟨hc, hy⟩
    obtain ⟨hF0, hFd⟩ := K.F_frontier hopen hfr
    refine vanish_hasFDerivAt (fun z => ?_) hF0 hFd
    by_cases hz : z ∈ closure Ω
    · rw [h1 z hz]
    · rw [h2 z hz, abs_zero]; exact abs_nonneg _
  · have hev : closedRegionRestriction f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with z hz; exact h2 z hz
    exact (hasFDerivAt_const (0:ℝ) y).congr_of_eventuallyEq hev

/-- the contradiction: S cannot be Hölder (it jumps at x₀). -/
lemma Cut.contra (K : Cut C) (hopen : IsOpen Ω) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ C.u z - fderiv ℝ C.u z'‖ ≤ L * ‖z - z'‖)
    (f : closure Ω →ᵇ ℝ) (hf : ∀ y : closure Ω, f y = K.F y) {Kh r : NNReal} (hr : 0 < (r : ℝ))
    (S : closure Ω → ℝ)
    (hSdef : ∀ x : closure Ω, S x = ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖)
    (hS : HolderWith Kh r S) : False := by
  obtain ⟨hR1, hR2, hR3⟩ := K.R_facts hopen f hf
  set R := closedRegionRestriction f with hRdef
  have hx0b : ‖C.x₀ - C.x₀‖ < C.δ1 := by simpa using C.hδ1
  have hx₀Ω : C.x₀ ∉ Ω := fun h => by
    have := (char C hopen hx0b).1.1 h; rw [T_x0] at this; exact lt_irrefl _ this
  have hx₀c : C.x₀ ∈ closure Ω := (char C hopen hx0b).2.2 (T_x0 C).ge
  have hfr : C.x₀ ∈ frontier Ω := by rw [hopen.frontier_eq]; exact ⟨hx₀c, hx₀Ω⟩
  have hRΩ : ∀ y ∈ Ω, R y = K.F y := fun y hy => hR1 y (subset_closure hy)
  have hφ : ∀ j, fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) C.x₀ = 0 := by
    intro j
    refine K.phi_zero hopen hL0 hL j (fun y hy => ?_) (fun y hy => ?_)
    · rw [(K.R_second hopen hRΩ hy j j).2, K.fderiv_F]
    · rw [(hR3 y hy).fderiv]; simp
  have hS0 : S ⟨C.x₀, hx₀c⟩ = 0 := by
    rw [hSdef]
    have e1 : f ⟨C.x₀, hx₀c⟩ = 0 := by rw [hf]; exact (K.F_frontier hopen hfr).1
    have e2 : fderiv ℝ R C.x₀ = 0 := (hR3 _ hx₀Ω).fderiv
    simp [e1, e2, hφ]
  have hz0 : Lz C (C.x₀ - C.x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) C.δ1 :=
    zf_mem C (Metric.mem_ball_self C.hδ1)
  obtain ⟨j₀, hj₀⟩ : ∃ j, pj C j C.x₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hT := hasFDerivAt_T C (K.du hz0)
    set DT := C.α • ((fderiv ℝ C.u (Lz C (C.x₀ - C.x₀))).comp (Lz C) - lastL C) with hDT
    have hDTj : ∀ j, DT (EuclideanSpace.single j 1) = pj C j C.x₀ := fun j => by
      simp [hDT, pj]
    have hDν : DT C.ν = 0 := by
      rw [clm_expand]; simp [hDTj, hall]
    have h1 : HasDerivAt (fun t : ℝ => C.x₀ + t • C.ν) C.ν 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const C.ν).const_add C.x₀
    have h2 : HasDerivAt (fun t : ℝ => Ch.T C (C.x₀ + t • C.ν)) (DT C.ν) 0 :=
      hT.comp_hasDerivAt_of_eq 0 h1 (by simp)
    have e : (fun t : ℝ => Ch.T C (C.x₀ + t • C.ν)) = fun t => -t := funext K.line_T
    rw [e] at h2
    have := h2.unique (hasDerivAt_neg 0)
    rw [hDν] at this; norm_num at this
  have hΨ0 : K.Ψ j₀ j₀ C.x₀ ≠ 0 := by
    obtain ⟨h1, h2, h3⟩ := K.vals_in (Metric.mem_ball_self K.hrIn) j₀ j₀
    simp [Cut.Ψ, h1, h2, h3, T_x0, hj₀]
  have hmem : ∀ t ∈ Set.Ioo (0:ℝ) K.rIn, C.x₀ + (-t) • C.ν ∈ Ω := by
    intro t ht
    have hrr : K.rIn < C.δ1 := by linarith [K.hrInr, K.hrδ, K.hr]
    apply (char C hopen (by rw [Cut.line_norm, abs_neg, abs_of_pos ht.1]; linarith [ht.2])).1.2
    rw [K.line_T]; linarith [ht.1]
  have hlow : ∀ x : closure Ω, ‖fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j₀ 1)) ↑x
      (EuclideanSpace.single j₀ 1)‖ ≤ S x := by
    intro x
    rw [hSdef]
    have h1 : ‖fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j₀ 1)) ↑x
        (EuclideanSpace.single j₀ 1)‖ ≤ ∑ j : Fin (n + 1),
        ‖fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) ↑x
          (EuclideanSpace.single j₀ 1)‖ :=
      Finset.single_le_sum (f := fun j => ‖fderiv ℝ (fun y => fderiv ℝ R y
        (EuclideanSpace.single j 1)) ↑x (EuclideanSpace.single j₀ 1)‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ j₀)
    have h2 : ∑ j : Fin (n + 1), ‖fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) ↑x
          (EuclideanSpace.single j₀ 1)‖ ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        ‖fderiv ℝ (fun y => fderiv ℝ R y (EuclideanSpace.single j 1)) ↑x
          (EuclideanSpace.single i 1)‖ :=
      Finset.single_le_sum (f := fun i => ∑ j : Fin (n + 1), ‖fderiv ℝ (fun y => fderiv ℝ R y
        (EuclideanSpace.single j 1)) ↑x (EuclideanSpace.single i 1)‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ j₀)
    have h3 : 0 ≤ ∑ i : Fin (n + 1), ‖fderiv ℝ R ↑x (EuclideanSpace.single i 1)‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have h4 := norm_nonneg (f x)
    linarith
  have hbound : ∀ t ∈ Set.Ioo (0:ℝ) K.rIn,
      |K.Ψ j₀ j₀ (C.x₀ + (-t) • C.ν)| ≤ Kh * t ^ (r:ℝ) := by
    intro t ht
    have hy := hmem t ht
    obtain ⟨x, hxdef⟩ : ∃ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) =
        C.x₀ + (-t) • C.ν := ⟨⟨_, subset_closure hy⟩, rfl⟩
    have h1 := hlow x
    rw [hxdef, (K.R_second hopen hRΩ hy j₀ j₀).1, Real.norm_eq_abs] at h1
    have h2 := HolderWith.abs_le' (f := S) hS x ⟨C.x₀, hx₀c⟩
    have hd : dist x ⟨C.x₀, hx₀c⟩ = t := by
      rw [Subtype.dist_eq, dist_eq_norm, hxdef]
      change ‖(C.x₀ + (-t) • C.ν) - C.x₀‖ = t
      rw [Cut.line_norm, abs_neg, abs_of_pos ht.1]
    rw [hS0, hd, sub_zero] at h2
    exact h1.trans ((le_abs_self _).trans h2)
  have hc : Continuous (fun t : ℝ => C.x₀ + (-t) • C.ν) := by fun_prop
  have t1 : Tendsto (fun t : ℝ => |K.Ψ j₀ j₀ (C.x₀ + (-t) • C.ν)|) (𝓝[>] 0)
      (𝓝 |K.Ψ j₀ j₀ C.x₀|) := by
    have := (((K.continuous_Ψ j₀ j₀).comp hc).tendsto 0).abs
    simpa using this.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun t : ℝ => (Kh:ℝ) * t ^ (r:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => (Kh:ℝ) * t ^ (r:ℝ)) (𝓝 0) (𝓝 ((Kh:ℝ) * 0 ^ (r:ℝ))) :=
      (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hr.le)).tendsto 0
    rw [Real.zero_rpow hr.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto t1 t2 (by
    filter_upwards [Ioo_mem_nhdsGT K.hrIn] with t ht; exact hbound t ht)
  exact hΨ0 (abs_nonpos_iff.1 hle)

end P211c1a39

open P211c1a39

open scoped Topology BoundedContinuousFunction in open EthierKurtz in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (hBase : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h)
    (hEst : ∃ lamstar : ℝ, 0 < lamstar ∧ ∃ C₀ : NNReal,
      ∀ (f h : (closure Ω) →ᵇ ℝ) (Ch : NNReal) (lam : ℝ),
        lamstar ≤ lam →
        HolderWith Ch ⟨μ, hμ.1.le⟩ ⇑h →
        (∃ g : (closure Ω) →ᵇ ℝ,
          (f, g) ∈ obliqueDiffusionGraph Ω μ a b c ∧ lam • f - g = h) →
        (∀ x : closure Ω,
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖ ≤
            ↑(C₀ * (Ch + 1))) ∧
        HolderWith (C₀ * (Ch + 1)) ⟨μ, hμ.1.le⟩ (fun x : closure Ω =>
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖)) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c,
          lam₀ • fg.1 - fg.2 = h := by
  exfalso
  obtain ⟨lamstar, hls, C₀, hE⟩ := hEst
  have hμ' : 0 ≤ μ ∧ μ ≤ 1 := ⟨hμ.1.le, hμ.2⟩
  obtain ⟨x₀, hx₀⟩ := frontier_nonempty hbounded hconnected.nonempty
  obtain ⟨Cc, -, -, D, hD, hballD, hCu⟩ := exists_chart hopen hboundary hx₀ (hnormal x₀ hx₀)
  have h0D : (0 : EuclideanSpace ℝ (Fin n)) ∈ D := hballD (Metric.mem_ball_self Cc.hδ1)
  obtain ⟨L, hL0, r0, hr0, hLr0⟩ := fderiv_lip hD hCu.1 h0D
  have hq_ev : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ k l : Fin n,
      HB (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) μ
        (fun z => fderiv ℝ (fun y => fderiv ℝ Cc.u y (EuclideanSpace.single l 1)) z
          (EuclideanSpace.single k 1)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      CH_ballD hμ'.1 (hCu.2 k l) Cc.hδ1 hballD
  have ha_ev : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i j : Fin (n + 1),
      HB (Ω ∩ Metric.ball Cc.x₀ r) μ (fun x => a x i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      CH_HB Cc hopen hμ'.1 (haHolder i j)
  have hb_ev : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : Fin (n + 1),
      HB (Ω ∩ Metric.ball Cc.x₀ r) μ (fun x => b x i) :=
    Filter.eventually_all.2 fun i => CH_HB Cc hopen hμ'.1 (hbHolder i)
  have hIoo : Set.Ioo (0:ℝ) (min Cc.δ1 r0) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (lt_min Cc.hδ1 hr0)
  obtain ⟨r, ⟨⟨hq, ha'⟩, hb'⟩, hr⟩ :=
    (((hq_ev.and ha_ev).and hb_ev).and (Filter.mem_of_superset hIoo fun _ h => h)).exists
  have hrpos : 0 < r := hr.1
  have hrδ : r ≤ Cc.δ1 := hr.2.le.trans (min_le_left _ _)
  have hrr0 : r ≤ r0 := hr.2.le.trans (min_le_right _ _)
  have hu2 : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Cc.δ1, ContDiffAt ℝ 2 Cc.u z :=
    fun z hz => hCu.1.contDiffAt (hD.mem_nhds (hballD hz))
  obtain ⟨K, hKr⟩ : ∃ K : Cut Cc, K.r = r := by
    let β : ContDiffBump Cc.x₀ := ⟨r / 8, r / 4, by positivity, by linarith⟩
    refine ⟨{
      χ := ⇑β
      r := r
      rIn := r / 8
      hr := hrpos
      hrδ := hrδ
      hrIn := (by positivity)
      hχ := β.contDiff
      hcs := β.hasCompactSupport
      hsupp := (by
        rw [β.tsupport_eq]; exact Metric.closedBall_subset_ball (show r / 4 < r / 2 by linarith))
      hone := fun y hy => β.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
      hrInr := (by linarith)
      hu2 := hu2 }, rfl⟩
  have hrK : K.r ≤ r0 := by rw [hKr]; exact hrr0
  have hL : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) K.r,
        ‖fderiv ℝ Cc.u z - fderiv ℝ Cc.u z'‖ ≤ L * ‖z - z'‖ := fun z hz z' hz' =>
    hLr0 z (Metric.ball_subset_ball hrK hz) z' (Metric.ball_subset_ball hrK hz')
  rw [← hKr] at hq ha' hb'
  haveI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hbounded.isCompact_closure
  obtain ⟨f, hf⟩ : ∃ f : closure Ω →ᵇ ℝ, ∀ y : closure Ω, f y = K.F y :=
    ⟨BoundedContinuousFunction.mkOfCompact
      ⟨fun x => K.F x, K.contDiff_F.continuous.comp continuous_subtype_val⟩, fun y => rfl⟩
  obtain ⟨hR1, -, -⟩ := K.R_facts hopen f hf
  have hRΩ : ∀ y ∈ Ω, closedRegionRestriction f y = K.F y := fun y hy => hR1 y (subset_closure hy)
  obtain ⟨Kg, hKg, hgΩ⟩ := K.glob_g hμ a b hL0 hL hq ha' hb'
  obtain ⟨hext1, hext2⟩ := holder_ext hμ.1 hKg hgΩ
  have hgH : HolderWith ⟨Kg, hKg⟩ ⟨μ, hμ.1.le⟩
      (fun x : closure Ω => extendFrom Ω (K.gΩ a b) x) :=
    holderWith_of_le hμ.1.le fun x y => by
      rw [Subtype.dist_eq, dist_eq_norm]; exact hext2 x x.2 y y.2
  obtain ⟨g, hg⟩ : ∃ g : closure Ω →ᵇ ℝ, ∀ y : closure Ω, g y = extendFrom Ω (K.gΩ a b) y :=
    ⟨BoundedContinuousFunction.mkOfCompact ⟨_, hgH.continuous (NNReal.coe_pos.mp hμ.1)⟩,
      fun y => rfl⟩
  have hFcs : HasCompactSupport K.F := by
    have := K.hcs.mul_right (f' := fun y => Ch.T Cc y ^ 2); exact this
  obtain ⟨Kf, hKf, hFH⟩ := HB.glob (S := Set.univ) hμ.1 K.hr
    ((HB_of_cs hμ' (K.contDiff_F.of_le (by norm_num)) hFcs Cc.x₀ K.hr).mono
      Set.inter_subset_right)
    (fun y _ hy => by
      have hs : y ∉ tsupport K.χ := fun hs => by
        have := K.hsupp hs; rw [Metric.mem_ball, dist_eq_norm] at this; linarith
      simp [Cut.F, (K.off hs).self_of_nhds.1])
  obtain ⟨Ch, hCh⟩ : ∃ Ch : NNReal, (Ch : ℝ) = |lamstar| * Kf + Kg :=
    ⟨⟨|lamstar| * Kf + Kg, by positivity⟩, rfl⟩
  have hhx : ∀ z : closure Ω, (lamstar • f - g) z =
      lamstar * K.F z - extendFrom Ω (K.gΩ a b) z := fun z => by simp [hf, hg]
  have hhH : HolderWith Ch ⟨μ, hμ.1.le⟩ ⇑(lamstar • f - g) := by
    refine holderWith_of_le hμ.1.le fun x y => ?_
    rw [hhx, hhx, Subtype.dist_eq, dist_eq_norm, hCh]
    have e1 := hFH x (Set.mem_univ _) y (Set.mem_univ _)
    have e2 := hext2 x x.2 y y.2
    have e3 : |lamstar * K.F x - extendFrom Ω (K.gΩ a b) x -
        (lamstar * K.F y - extendFrom Ω (K.gΩ a b) y)| ≤
        |lamstar| * |K.F x - K.F y| +
          |extendFrom Ω (K.gΩ a b) x - extendFrom Ω (K.gΩ a b) y| := by
      rw [show lamstar * K.F x - extendFrom Ω (K.gΩ a b) x -
          (lamstar * K.F y - extendFrom Ω (K.gΩ a b) y) = lamstar * (K.F x - K.F y) -
          (extendFrom Ω (K.gΩ a b) x - extendFrom Ω (K.gΩ a b) y) by ring, ← abs_mul]
      exact abs_sub _ _
    have e4 : |lamstar| * |K.F x - K.F y| ≤
        |lamstar| * (Kf * ‖(x : EuclideanSpace ℝ (Fin (n + 1))) - y‖ ^ μ) :=
      mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    linarith
  have hgraph : (f, g) ∈ obliqueDiffusionGraph Ω μ a b c := by
    simp only [obliqueDiffusionGraph, Set.mem_setOf_eq]
    refine ⟨K.ctwice hopen hμ hRΩ (fun i j => K.glob_Ψ hμ hL0 hL hq i j), fun x hx => ?_,
      fun x => fderiv ℝ K.F x,
      (K.contDiff_F.continuous_fderiv (by norm_num)).comp continuous_subtype_val,
      fun x hx => (K.R_second hopen hRΩ hx 0 0).2.symm, fun x hx => ?_⟩
    · rw [K.g_formula hopen a b hRΩ hx]
      simp only [closedRegionRestriction, dif_pos (subset_closure hx)]
      rw [hg]; exact hext1 x hx
    · show fderiv ℝ K.F x (c x) = 0
      rw [(K.F_frontier hopen hx).2.fderiv]; simp
  have hmain := (hE f (lamstar • f - g) Ch lamstar le_rfl hhH ⟨g, hgraph, rfl⟩).2
  exact K.contra (r := ⟨μ, hμ.1.le⟩) (Kh := C₀ * (Ch + 1)) hopen hL0 hL f hf hμ.1 _
    (fun x => rfl) hmain
