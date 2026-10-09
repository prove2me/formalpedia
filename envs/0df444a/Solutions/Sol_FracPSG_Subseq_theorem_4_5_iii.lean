-- Prove2me | solution 1 for FracPSG.Subseq.theorem_4_5_iii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T22:37:25.343141+00:00
-- url     : https://prove2.me/submissions/b6eca921-ef97-4ea9-8bbf-7dc081b0a960
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Subseq_EPSG
import Theorems.Thm_FracPSG_Subseq_theorem_4_5_i
import Theorems.Thm_FracPSG_Subseq_theorem_4_5_ii
import Theorems.Thm_FracPSG_Subseq_limit_inequality

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

namespace P6afa

open NonconvexSplitting.Shared FracPSG.Subseq

/-- A regular subgradient of a function that is `K`-Lipschitz near `z` has norm at most `K`. -/
theorem regSubgrad_norm_le {N : ℕ} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {z v : EuclideanSpace ℝ (Fin N)} {K : NNReal} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : U ∈ 𝓝 z) (hK : LipschitzOnWith K g U)
    (hv : IsRegularSubgrad (fun y => (g y : EReal)) z v) : ‖v‖ ≤ K := by
  by_contra hcon
  push Not at hcon
  have hKnn : (0 : ℝ) ≤ K := K.2
  have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hKnn hcon
  set ε : ℝ := (‖v‖ - K) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hline : Tendsto (fun s : ℝ => z + s • v) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • v) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hline.eventually (hv.2 ε hε)
  have h2 := hline.eventually hU
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  have hs0 : 0 < s := hs3
  simp only [add_sub_cancel_left] at hs1
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hs1
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, real_inner_self_eq_norm_sq]
    at hs1
  have hlip : dist (g (z + s • v)) (g z) ≤ K * dist (z + s • v) z :=
    hK.dist_le_mul _ hs2 _ (mem_of_mem_nhds hU)
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hs0] at hlip
  have hup : g (z + s • v) - g z ≤ K * (s * ‖v‖) := (le_abs_self _).trans hlip
  -- s‖v‖² - ε s‖v‖ ≤ K s ‖v‖
  have h3 : s * ‖v‖ ^ 2 - ε * (s * ‖v‖) ≤ K * (s * ‖v‖) := by linarith
  have h4 : 0 < s * ‖v‖ := mul_pos hs0 hvpos
  have h5 : ‖v‖ - ε ≤ K := by
    have : (‖v‖ - ε) * (s * ‖v‖) ≤ K * (s * ‖v‖) := by nlinarith
    exact le_of_mul_le_mul_right this h4
  rw [hεdef] at h5
  linarith

/-- A limiting subgradient of a function that is `K`-Lipschitz near `z` has norm at most `K`. -/
theorem limSubgrad_norm_le {N : ℕ} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {z v : EuclideanSpace ℝ (Fin N)} {K : NNReal} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : U ∈ 𝓝 z) (hK : LipschitzOnWith K g U)
    (hv : v ∈ LimitingSubdiff (fun y => (g y : EReal)) z) : ‖v‖ ≤ K := by
  obtain ⟨-, xs, vs, hxs, -, hvs, hreg⟩ := hv
  have hev : ∀ᶠ y in 𝓝 z, U ∈ 𝓝 y := Filter.Eventually.eventually_nhds (p := fun y => y ∈ U) hU
  have hev2 : ∀ᶠ t in atTop, ‖vs t‖ ≤ K := by
    filter_upwards [hxs.eventually hev] with t ht
    exact regSubgrad_norm_le ht hK (hreg t)
  exact le_of_tendsto hvs.norm hev2

theorem fn_real {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : Assumption1 S fs fn ℓ)
    {y : EuclideanSpace ℝ (Fin N)} (hy : objF fs fn y ≠ ⊤) :
    ∃ r : ℝ, fn y = r ∧ objF fs fn y = ((fs y + r : ℝ) : EReal) ∧
      (objF fs fn y).toReal = fs y + r := by
  have h1 : fn y ≠ ⊥ := hA1.fn_proper.1 y
  have h2 : fn y ≠ ⊤ := by
    intro h; apply hy; simp [objF, h]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, fn y = r := ⟨_, (EReal.coe_toReal h2 h1).symm⟩
  have h3 : objF fs fn y = ((fs y + r : ℝ) : EReal) := by
    unfold objF; rw [hr, EReal.coe_add]
  exact ⟨r, hr, h3, by rw [h3, EReal.toReal_coe]⟩

/-- The Step-2 optimality of `x (n+1)` tested against `y = xbar`, in real form. -/
theorem step_upper {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) (n : ℕ)
    {xbar : EuclideanSpace ℝ (Fin N)} (hxbS : xbar ∈ S)
    (hxbf : objF fs fn xbar ≠ ⊤)
    (hyf : objF fs fn (x (n + 1)) ≠ ⊤) :
    (objF fs fn (x (n + 1))).toReal ≤ (objF fs fn xbar).toReal
      + (fs (x (n + 1)) - fs xbar)
      + ⟪gradient fs (extrap x κ n), xbar - x (n + 1)⟫_ℝ
      + 1 / (2 * τ n) *
          (‖xbar - extrap x μ n - (τ n * ratio (objF fs fn) g (x n)) • gs n‖ ^ 2
            - ‖x (n + 1) - extrap x μ n - (τ n * ratio (objF fs fn) g (x n)) • gs n‖ ^ 2)
      + ℓ / 2 * (‖xbar - extrap x κ n‖ ^ 2 - ‖x (n + 1) - extrap x κ n‖ ^ 2) := by
  have h := hrun.next_argmin n xbar hxbS
  obtain ⟨r1, hr1, -, ha⟩ := fn_real hA1 hyf
  obtain ⟨r2, hr2, -, hb⟩ := fn_real hA1 hxbf
  unfold subObj at h
  rw [hr1, hr2, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [ha, hb]
  have e : ⟪gradient fs (extrap x κ n), xbar - x (n + 1)⟫_ℝ =
      ⟪gradient fs (extrap x κ n), xbar - extrap x κ n⟫_ℝ -
      ⟪gradient fs (extrap x κ n), x (n + 1) - extrap x κ n⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  rw [e]
  have e2 : ∀ (a b : ℝ), 1 / (2 * τ n) * (a - b) = 1 / (2 * τ n) * a - 1 / (2 * τ n) * b := by
    intro a b; ring
  rw [e2]
  linarith

theorem T2_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (xb y v gr : E)
    (τ θ T0 δ Θ Γ : ℝ) (hT0 : 0 < T0) (hτ0 : T0 ≤ τ) (hτδ : τ ≤ 1 / δ) (hδ : 0 < δ)
    (hθ : |θ| ≤ Θ) (hgr : ‖gr‖ ≤ Γ) (h1 : ‖xb - v‖ ≤ 1) (h2 : ‖y - v‖ ≤ 1) :
    |1 / (2 * τ) * (‖xb - v - (τ * θ) • gr‖ ^ 2 - ‖y - v - (τ * θ) • gr‖ ^ 2)| ≤
      1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) * ‖xb - y‖ := by
  have hτ : 0 < τ := lt_of_lt_of_le hT0 hτ0
  set c := (τ * θ) • gr with hcdef
  have hΘ : 0 ≤ Θ := le_trans (abs_nonneg _) hθ
  have hΓ : 0 ≤ Γ := le_trans (norm_nonneg _) hgr
  have hc : ‖c‖ ≤ 1 / δ * Θ * Γ := by
    rw [hcdef, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hτ]
    have := mul_le_mul hτδ hθ (abs_nonneg _) (by positivity)
    exact mul_le_mul this hgr (norm_nonneg _) (by positivity)
  set K := 1 / δ * Θ * Γ
  have ha : ‖xb - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h1 hc)
  have hb : ‖y - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h2 hc)
  have hab : |‖xb - v - c‖ - ‖y - v - c‖| ≤ ‖xb - y‖ := by
    have := abs_norm_sub_norm_le (xb - v - c) (y - v - c)
    have e : xb - v - c - (y - v - c) = xb - y := by abel
    rwa [e] at this
  have hsq : |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2| ≤ ‖xb - y‖ * (2 + 2 * K) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖xb - v - c‖ + ‖y - v - c‖),
      mul_comm]
    exact mul_le_mul hab (by linarith) (by positivity) (norm_nonneg _)
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * τ))]
  have hinv : 1 / (2 * τ) ≤ 1 / (2 * T0) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc 1 / (2 * τ) * |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2|
      ≤ 1 / (2 * T0) * (‖xb - y‖ * (2 + 2 * K)) :=
        mul_le_mul hinv hsq (abs_nonneg _) (by positivity)
    _ = 1 / (2 * T0) * (2 + 2 * K) * ‖xb - y‖ := by ring

theorem objF_lsc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : Assumption1 S fs fn ℓ) :
    LowerSemicontinuous (objF fs fn) := by
  have h1 : LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hA1.fs_contDiff.continuous).lowerSemicontinuous
  show LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal) + fn y)
  exact LowerSemicontinuous.add' h1 hA1.fn_lsc (fun y =>
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

/-- The limit of the ratios equals the ratio at any cluster point. -/
theorem ratio_limit_eq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hμbar : 0 ≤ μbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hgLip : ∀ y ∈ S, ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K g U)
    {τbar : ℝ} (hτbar : 0 < τbar) (hτ : ∀ᶠ n in atTop, τbar ≤ τ n)
    (hxn : ∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤)
    {L : ℝ} (hL : Tendsto (fun n => ratio (objF fs fn) g (x n)) atTop (𝓝 L))
    (hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    {xbar : EuclideanSpace ℝ (Fin N)} (hcl : MapClusterPt xbar atTop x) (hxbS : xbar ∈ S)
    (hxbf : objF fs fn xbar ≠ ⊤) :
    L = ratio (objF fs fn) g xbar := by
  have hlsc := objF_lsc hA1
  set f := objF fs fn with hf
  obtain ⟨O, hO, hSO, hgO⟩ := hA2.continuous_near
  have hgcont : ContinuousAt g xbar := hgO.continuousAt (hO.mem_nhds (hSO hxbS))
  have hgpos : 0 < g xbar := hA2.pos xbar hxbS
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  obtain ⟨K, U, hU, hKU⟩ := hgLip xbar hxbS
  -- subsequence
  obtain ⟨ψ, hψm, hψt⟩ := hcl.tendsto_subseq
  obtain ⟨nn, hnn1, hnnk⟩ : ∃ nn : ℕ → ℕ, (∀ k, nn k + 1 = ψ (k + 1)) ∧ ∀ k, k ≤ nn k := by
    refine ⟨fun k => ψ (k + 1) - 1, fun k => ?_, fun k => ?_⟩
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show ψ (k + 1) - 1 + 1 = ψ (k + 1)
      omega
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show k ≤ ψ (k + 1) - 1
      omega
  have hnnt : Tendsto nn atTop atTop := tendsto_atTop_mono hnnk tendsto_id
  have hnnt1 : Tendsto (fun k => nn k + 1) atTop atTop := tendsto_add_atTop_nat 1 |>.comp hnnt
  have hy : Tendsto (fun k => x (nn k + 1)) atTop (𝓝 xbar) := by
    have := hψt.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun k => ?_)
    simp [Function.comp, hnn1]
  have hsteps : Tendsto (fun k => x (nn k + 1) - x (nn k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; exact hstep.comp hnnt
  have hx0 : Tendsto (fun k => x (nn k)) atTop (𝓝 xbar) := by
    have := hy.sub hsteps; simpa using this
  have hprevd : Tendsto (fun n => x n - xPrev x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := hstep.comp (tendsto_sub_atTop_nat 1)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp, xPrev, if_neg (by omega : n ≠ 0),
      Nat.sub_add_cancel hn]
  have hprevk := hprevd.comp hnnt
  have hu : Tendsto (fun k => extrap x κ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => κ (nn k) • (x (nn k) - xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => κbar * ‖x (nn k) - xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.kappa_mem (nn k)).1]
        exact mul_le_mul_of_nonneg_right (hrun.kappa_mem (nn k)).2 (norm_nonneg _)
      · simpa using (hprevk.norm).const_mul κbar
    have := hx0.add hz
    simpa [extrap] using this
  have hv : Tendsto (fun k => extrap x μ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => μ (nn k) • (x (nn k) - xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun k => (μbar * (1 / δ)) * ‖x (nn k) - xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.mu_mem (nn k)).1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hrun.mu_mem (nn k)).2.trans
          (mul_le_mul_of_nonneg_left (hτle _) hμbar)
      · simpa using (hprevk.norm).const_mul (μbar * (1 / δ))
    have := hx0.add hz
    simpa [extrap] using this
  -- a_k
  set a : ℕ → ℝ := fun k => (f (x (nn k + 1))).toReal with ha
  have ha_eq : ∀ k, a k = ratio f g (x (nn k + 1)) * g (x (nn k + 1)) := by
    intro k
    have hp : 0 < g (x (nn k + 1)) := hA2.pos _ (hxn _).1
    simp only [ha, ratio]
    field_simp
  have hA : Tendsto a atTop (𝓝 (L * g xbar)) := by
    have := (hL.comp hnnt1).mul (hgcont.tendsto.comp hy)
    refine this.congr (fun k => ?_)
    rw [ha_eq k]; rfl
  obtain ⟨F0, -, hF0, hF⟩ := fn_real hA1 hxbf
  set F := (f xbar).toReal with hFdef
  -- lower bound by lower semicontinuity
  have hlow : F ≤ L * g xbar := by
    have hfin : ∀ k, f (x (nn k + 1)) = ((a k : ℝ) : EReal) := by
      intro k
      obtain ⟨r, -, h1, h2⟩ := fn_real hA1 (hxn (nn k + 1)).2
      simp only [ha]; rw [← hf] at h1 h2; rw [h2, h1]
    have hfx : f xbar = ((F : ℝ) : EReal) := by
      rw [hFdef, ← hf] at *; rw [hF0, EReal.toReal_coe]
    by_contra hcon
    push Not at hcon
    have hlt : (((L * g xbar : ℝ)) : EReal) < f xbar := by
      rw [hfx]; exact EReal.coe_lt_coe_iff.2 hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hev : ∀ᶠ k in atTop, c < ((a k : ℝ) : EReal) := by
      have := hy.eventually (hlsc xbar c hc2)
      filter_upwards [this] with k hk
      rwa [hfin k] at hk
    have hAE : Tendsto (fun k => ((a k : ℝ) : EReal)) atTop (𝓝 ((L * g xbar : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hA
    have : c ≤ ((L * g xbar : ℝ) : EReal) := ge_of_tendsto hAE (hev.mono fun k hk => hk.le)
    exact absurd hc1 (not_lt.2 this)
  -- upper bound
  set E : ℕ → ℝ := fun k =>
      (fs (x (nn k + 1)) - fs xbar)
      + ⟪gradient fs (extrap x κ (nn k)), xbar - x (nn k + 1)⟫_ℝ
      + 1 / (2 * τ (nn k)) *
          (‖xbar - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) • gs (nn k)‖ ^ 2
            - ‖x (nn k + 1) - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) •
              gs (nn k)‖ ^ 2)
      + ℓ / 2 * (‖xbar - extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - extrap x κ (nn k)‖ ^ 2) with hE
  have hupk : ∀ k, a k ≤ F + E k := by
    intro k
    have := step_upper hA1 hrun (nn k) hxbS hxbf (hxn (nn k + 1)).2
    simp only [ha, hE, hFdef]
    linarith
  have hfsc : Continuous fs := hA1.fs_contDiff.continuous
  have hgfs : Continuous (fun z => gradient fs z) := by
    have h1 := hA1.fs_contDiff.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous.comp h1
  have hdy : Tendsto (fun k => xbar - x (nn k + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := xbar)).sub hy; simpa using this
  have hE1 : Tendsto (fun k => fs (x (nn k + 1)) - fs xbar) atTop (𝓝 0) := by
    have := ((hfsc.tendsto xbar).comp hy).sub (tendsto_const_nhds (x := fs xbar))
    simpa using this
  have hE2 : Tendsto (fun k => ⟪gradient fs (extrap x κ (nn k)),
      xbar - x (nn k + 1)⟫_ℝ) atTop (𝓝 0) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) ((hgfs.tendsto xbar).comp hu) hdy
    simpa using this
  have hE4 : Tendsto (fun k => ℓ / 2 * (‖xbar - extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - extrap x κ (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => xbar - extrap x κ (nn k)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := xbar)).sub hu; simpa using this
    have h2 : Tendsto (fun k => x (nn k + 1) - extrap x κ (nn k)) atTop (𝓝 0) := by
      have := hy.sub hu; simpa using this
    have := ((h1.norm.pow 2).sub (h2.norm.pow 2)).const_mul (ℓ / 2)
    simpa using this
  -- the quadratic term, by a squeeze
  set T0 := τbar with hT0
  have hT0pos : 0 < T0 := hτbar
  set Θ := |L| + 1
  set Γ : ℝ := (K : ℝ)
  have ev1 : ∀ᶠ k in atTop, T0 ≤ τ (nn k) := hnnt.eventually hτ
  have ev2 : ∀ᶠ k in atTop, |ratio f g (x (nn k))| ≤ Θ := by
    have := (hL.comp hnnt).eventually (Metric.ball_mem_nhds L one_pos)
    filter_upwards [this] with k hk
    have hk' : |ratio f g (x (nn k)) - L| < 1 := by
      simpa [Real.dist_eq] using hk
    have := abs_sub_abs_le_abs_sub (ratio f g (x (nn k))) L
    linarith
  have ev3 : ∀ᶠ k in atTop, ‖gs (nn k)‖ ≤ Γ := by
    have hev : ∀ᶠ y in 𝓝 xbar, U ∈ 𝓝 y :=
      Filter.Eventually.eventually_nhds (p := fun y => y ∈ U) hU
    filter_upwards [hx0.eventually hev] with k hk
    exact limSubgrad_norm_le hk hKU (hrun.subgrad (nn k))
  have ev4 : ∀ᶠ k in atTop, ‖xbar - extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖xbar - extrap x μ (nn k)‖) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := xbar)).sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have ev5 : ∀ᶠ k in atTop, ‖x (nn k + 1) - extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖x (nn k + 1) - extrap x μ (nn k)‖) atTop
        (𝓝 0) := by
      have := (hy.sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have hE3 : Tendsto (fun k => 1 / (2 * τ (nn k)) *
          (‖xbar - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) • gs (nn k)‖ ^ 2
            - ‖x (nn k + 1) - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) •
              gs (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => 1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) *
        ‖xbar - x (nn k + 1)‖) atTop (𝓝 0) := by
      have := (hdy.norm).const_mul (1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ev1, ev2, ev3, ev4, ev5] with k h1 h2 h3 h4 h5
    rw [Real.norm_eq_abs]
    exact T2_bound _ _ _ _ _ _ T0 δ Θ Γ hT0pos h1 (hτle _) hδ h2 h3 h4 h5
  have hEt : Tendsto E atTop (𝓝 0) := by
    have := ((hE1.add hE2).add hE3).add hE4
    simpa [hE] using this
  have hup : L * g xbar ≤ F := by
    have := le_of_tendsto_of_tendsto hA ((tendsto_const_nhds (x := F)).add hEt)
      (Eventually.of_forall hupk)
    simpa using this
  have heq : L * g xbar = F := le_antisymm hup hlow
  simp only [ratio]
  rw [← hFdef, ← heq]
  field_simp

/-- Lifted stationarity from the limit inequality. -/
theorem lifted_of_ineq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ : ℝ}
    {τbar : ℝ} (hτbar : 0 < τbar) (hℓ : 0 ≤ ℓ)
    {xbar gbar : EuclideanSpace ℝ (Fin N)} (hxbS : xbar ∈ S)
    (hxbf : objF fs fn xbar ≠ ⊤) (hgpos : 0 < g xbar)
    (hgbar : gbar ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar)
    (hineq : ∀ y ∈ S, objF fs fn xbar +
          ((-(1 / (2 * τbar)) * ‖y - xbar‖ ^ 2
            - ratio (objF fs fn) g xbar * ⟪gbar, xbar - y⟫_ℝ
            - ℓ / 2 * ‖y - xbar‖ ^ 2 : ℝ) : EReal) ≤ objF fs fn y) :
    IsLiftedStationary (objF fs fn) g S xbar := by
  set θ := ratio (objF fs fn) g xbar with hθ
  have hc : 0 < 1 / (2 * τbar) + ℓ / 2 := by
    have : 0 < 1 / (2 * τbar) := by positivity
    linarith
  have hreg : IsRegularSubgrad (addInd (objF fs fn) S) xbar (θ • gbar) := by
    refine ⟨?_, fun ε hε => ?_⟩
    · simp only [addInd, if_pos hxbS]; exact hxbf
    · filter_upwards [Metric.ball_mem_nhds xbar (div_pos hε hc)] with z hz
      by_cases hzS : z ∈ S
      · simp only [addInd, if_pos hxbS, if_pos hzS]
        have hd : ‖z - xbar‖ * (1 / (2 * τbar) + ℓ / 2) < ε := by
          have : ‖z - xbar‖ < ε / (1 / (2 * τbar) + ℓ / 2) := by
            have hz' : dist z xbar < ε / (1 / (2 * τbar) + ℓ / 2) := hz
            rwa [dist_eq_norm] at hz'
          rwa [lt_div_iff₀ hc] at this
        have hd0 : 0 ≤ ‖z - xbar‖ := norm_nonneg _
        have e1 : ⟪gbar, xbar - z⟫_ℝ = -⟪gbar, z - xbar⟫_ℝ := by
          rw [← inner_neg_right]; congr 1; abel
        have key : ⟪θ • gbar, z - xbar⟫_ℝ - ε * ‖z - xbar‖ ≤
            -(1 / (2 * τbar)) * ‖z - xbar‖ ^ 2 - θ * ⟪gbar, xbar - z⟫_ℝ
              - ℓ / 2 * ‖z - xbar‖ ^ 2 := by
          rw [inner_smul_left, e1]
          simp only [conj_trivial]
          nlinarith [mul_le_mul_of_nonneg_left hd.le hd0]
        exact (add_le_add le_rfl (EReal.coe_le_coe_iff.2 key)).trans (hineq z hzS)
      · simp [addInd, hzS]
  refine ⟨hxbS, θ • gbar, ⟨?_, fun _ => xbar, fun _ => θ • gbar, tendsto_const_nhds,
    tendsto_const_nhds, tendsto_const_nhds, fun _ => hreg⟩, gbar, hgbar, ?_⟩
  · simp only [addInd, if_pos hxbS]; exact hxbf
  · have : g xbar * θ = (objF fs fn xbar).toReal := by
      rw [hθ]; unfold ratio; field_simp
    rw [smul_smul, this, sub_self]

end P6afa

open FracPSG.Subseq NonconvexSplitting.Shared in
theorem solution
    {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ) {m M : ℝ}
    (hpar : ParamsBC S (objF fs fn) g ℓ β δ ζ μbar κbar m M ∨ ParamsNoBC μbar κbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0)))
    (hgLip : ∀ y ∈ S, ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K g U)
    (hτ : ∃ τbar : ℝ, 0 < τbar ∧ ∀ᶠ n in atTop, τbar ≤ τ n) :
    ∀ xbar : EuclideanSpace ℝ (Fin N), MapClusterPt xbar atTop x →
      xbar ∈ S ∧ objF fs fn xbar ≠ ⊤ ∧
      Tendsto (fun n => ratio (objF fs fn) g (x n)) atTop
        (𝓝 (ratio (objF fs fn) g xbar)) ∧
      IsLiftedStationary (objF fs fn) g S xbar := by
  intro xbar hcl
  obtain ⟨τbar, hτbar, hτev⟩ := hτ
  obtain ⟨hxn, -, -, L, hL⟩ := FracPSG.Subseq.theorem_4_5_i hS hSconv hA1 hA2 hδ hζ hβζ hpar
    hrun hS0
  obtain ⟨-, hstep, -⟩ := FracPSG.Subseq.theorem_4_5_ii hS hSconv hA1 hA2 hδ hζ hβζ hpar
    hrun hS0
  have hτ' : ∀ ε > 0, ∀ᶠ n in atTop, τbar - ε ≤ τ n := fun ε hε =>
    hτev.mono fun n hn => by linarith
  obtain ⟨gbar, hgbar, hineq⟩ := FracPSG.Subseq.limit_inequality hS hSconv hA1 hA2 hδ hζ hβζ
    hpar hrun hS0 hgLip τbar hτbar hτ' xbar hcl
  have hxbS : xbar ∈ S := by
    obtain ⟨ψ, -, hψt⟩ := hcl.tendsto_subseq
    exact hS.mem_of_tendsto hψt (Eventually.of_forall fun k => (hxn _).1)
  have hxbf : objF fs fn xbar ≠ ⊤ := by
    intro h
    have h0 := hineq (x 0) (hxn 0).1
    rw [h, EReal.top_add_coe] at h0
    exact (hxn 0).2 (top_le_iff.1 h0)
  have hμbar : 0 ≤ μbar := by
    rcases hpar with h | h
    · exact h.2.1
    · exact le_of_eq h.1.symm
  have hLeq := P6afa.ratio_limit_eq hA1 hA2 hδ hμbar hrun hgLip hτbar hτev hxn hL hstep hcl hxbS
    hxbf
  exact ⟨hxbS, hxbf, hLeq ▸ hL,
    P6afa.lifted_of_ineq hτbar hA1.ell_nonneg hxbS hxbf (hA2.pos xbar hxbS) hgbar hineq⟩
