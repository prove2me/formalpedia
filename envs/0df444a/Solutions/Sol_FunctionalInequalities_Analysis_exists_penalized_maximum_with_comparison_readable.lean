-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:15.478793+00:00
-- url     : https://prove2.me/submissions/06329d7a-309f-4b31-ab38-74127f679f12

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_det_hessianMatrix_le_of_lower_touch_readable
import Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT17BMaximumWithComparison
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
private lemma FunctionalInequalities.Analysis.n9_average_continuous {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (h : EuclideanSpace ℝ (Fin n)) :
    Continuous (FunctionalInequalities.Analysis.n9_average g h) :=
  continuous_const.mul
    ((hg.comp (continuous_id.add continuous_const)).add
      (hg.comp (continuous_id.sub continuous_const)))
private lemma FunctionalInequalities.Analysis.n9_average_smooth {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g)
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 2 (FunctionalInequalities.Analysis.n9_average g h) :=
  contDiff_const.mul
    ((hg.comp (contDiff_id.add contDiff_const)).add
      (hg.comp (contDiff_id.sub contDiff_const)))
private lemma FunctionalInequalities.Analysis.n9_hessian_add {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f y + g y) x =
      hessianMatrix f x + hessianMatrix g x := by
  ext i j
  simp only [Matrix.add_apply, hessianMatrix,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => f y + g y) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  rfl
private lemma FunctionalInequalities.Analysis.n9_hessian_mul {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => c * f y) x = c • hessianMatrix f x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, hessianMatrix,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => c * f y) = c • f from rfl,
    iteratedFDeriv_const_smul_apply hf.contDiffAt]
  rfl
private lemma FunctionalInequalities.Analysis.n9_hessian_sub_const {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f y - c) x = hessianMatrix f x := by
  ext i j
  simp only [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => f y - c) = f - (fun _ => c) from rfl,
    iteratedFDeriv_sub_apply hf.contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
private lemma FunctionalInequalities.Analysis.n9_hessian_translate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f (y + h)) x = hessianMatrix f (x + h) := by
  ext i j
  simp only [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    iteratedFDeriv_comp_add_right]
private lemma FunctionalInequalities.Analysis.n9_hessian_sub_translate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f (y - h)) x = hessianMatrix f (x - h) := by
  simpa only [sub_eq_add_neg] using n9_hessian_translate f (-h) x
private lemma FunctionalInequalities.Analysis.n9_hessian_average {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (FunctionalInequalities.Analysis.n9_average g h) x =
      (1 / 2 : ℝ) • (hessianMatrix g (x + h) + hessianMatrix g (x - h)) := by
  have hp : ContDiff ℝ 2 (fun y => g (y + h)) :=
    hg.comp (contDiff_id.add contDiff_const)
  have hm : ContDiff ℝ 2 (fun y => g (y - h)) :=
    hg.comp (contDiff_id.sub contDiff_const)
  unfold FunctionalInequalities.Analysis.n9_average
  rw [n9_hessian_mul (hp.add hm), n9_hessian_add hp hm,
    n9_hessian_translate, n9_hessian_sub_translate]
private lemma FunctionalInequalities.Analysis.n9_midpoint_det {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : a ≤ Real.log A.det) (hb : b ≤ Real.log B.det) :
    Real.exp ((a + b) / 2) ≤ ((1 / 2 : ℝ) • (A + B)).det := by
  have hM := (hA.add hB).smul (by norm_num : (0 : ℝ) < 1 / 2)
  apply ((forall_posDef_add_log_det_le_trace_iff_readable hM.posSemidef
    ((a + b) / 2)).mp ?_).2
  intro J hJ
  have h1 := ((forall_posDef_add_log_det_le_trace_iff_readable hA.posSemidef
    (Real.log A.det)).mpr ⟨hA, by rw [Real.exp_log hA.det_pos]⟩) J hJ
  have h2 := ((forall_posDef_add_log_det_le_trace_iff_readable hB.posSemidef
    (Real.log B.det)).mpr ⟨hB, by rw [Real.exp_log hB.det_pos]⟩) J hJ
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul]
  linarith
private lemma FunctionalInequalities.Analysis.n9_scaled_det_comparison {n : ℕ}
    {α b f : ℝ} {M : Matrix (Fin n) (Fin n) ℝ}
    (ha : 0 < α) (hM : M.PosDef)
    (hl : Real.exp b ≤ M.det) (hu : (α⁻¹ • M).det ≤ Real.exp f) :
    b - n * Real.log α ≤ f := by
  have hl' := Real.log_le_log (Real.exp_pos b) hl
  have hu' := Real.log_le_log ((hM.smul (inv_pos.mpr ha)).det_pos) hu
  rw [Real.log_exp] at hl'
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero _ (inv_ne_zero ha.ne')) hM.det_pos.ne',
    Real.log_pow, Real.log_inv, Real.log_exp] at hu'
  linarith
private lemma FunctionalInequalities.Analysis.n9_maximizers {E : Type} [TopologicalSpace E] [Zero E]
    {u A : E → ℝ} {V : ℕ → E → ℝ}
    (hu : Continuous u) (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R})
    (hV : ∀ k, Continuous (V k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ k x, |V k x - A x| ≤ δ k)
    {C : ℝ} (hC : ∀ x, A x ≤ u x + C)
    {α : ℝ} (hα : 1 < α) :
    ∃ R : ℝ, ∃ x : ℕ → E,
      (∀ k, u (x k) ≤ R) ∧
      ∀ k y, V k y - α * u y ≤ V k (x k) - α * u (x k) := by
  obtain ⟨D, hD⟩ := hδ.bddAbove_range
  let B := A 0 - α * u 0 - D
  let R := max (u 0) ((C + D - B) / (α - 1))
  have hzero : u 0 ≤ R := le_max_left _ _
  have hbound : ∀ k y,
      V k 0 - α * u 0 ≤ V k y - α * u y → u y ≤ R := by
    intro k y hy
    have hd : δ k ≤ D := hD (mem_range_self k)
    have h1 := (abs_le.mp (hc k 0)).1
    have h2 := (abs_le.mp (hc k y)).2
    have h3 := hC y
    have hb : B ≤ V k 0 - α * u 0 := by
      dsimp [B]
      linarith
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ (by linarith : 0 < α - 1)).2
    nlinarith
  have hex : ∀ k, ∃ x, u x ≤ R ∧
      ∀ y, V k y - α * u y ≤ V k x - α * u x := by
    intro k
    obtain ⟨x, hx, hm⟩ := (hcoer R).exists_isMaxOn ⟨0, hzero⟩
      (((hV k).sub (hu.const_mul α)).continuousOn)
    refine ⟨x, hx, ?_⟩
    intro y
    by_cases hy : V k 0 - α * u 0 ≤ V k y - α * u y
    · exact hm (hbound k y hy)
    · exact (le_of_not_ge hy).trans (hm hzero)
  choose x hx hm using hex
  exact ⟨R, x, hx, hm⟩
private lemma FunctionalInequalities.Analysis.n9_limit {E : Type} [TopologicalSpace E]
    {u : E → ℝ} {V : ℕ → E → ℝ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ k x, |V k x - u x| ≤ δ k) (hu : Continuous u)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {g : ℕ → E} {x : E} (hg : Tendsto g atTop (𝓝 x)) :
    Tendsto (fun j => V (s j) (g j)) atTop (𝓝 (u x)) := by
  have hd := hδ.comp hs
  have hv := hu.continuousAt.tendsto.comp hg
  have hlo : Tendsto (fun j => u (g j) - δ (s j)) atTop (𝓝 (u x)) := by
    simpa only [sub_zero, Function.comp_def] using hv.sub hd
  have hhi : Tendsto (fun j => u (g j) + δ (s j)) atTop (𝓝 (u x)) := by
    simpa only [add_zero, Function.comp_def] using hv.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun j => by
      have hh := (abs_le.mp (hc (s j) (g j))).1
      linarith)
    (fun j => by
      have hh := (abs_le.mp (hc (s j) (g j))).2
      linarith)
private lemma FunctionalInequalities.Analysis.n9_lipschitz_translate {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hl : LipschitzWith L u) (y h : EuclideanSpace ℝ (Fin n)) :
    u (y + h) ≤ u y + (L : ℝ) * ‖h‖ := by
  have H : |u (y + h) - u y| ≤ (L : ℝ) * ‖h‖ := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left] using
      hl.norm_sub_le (y + h) y
  linarith [(abs_le.mp H).2]
private lemma FunctionalInequalities.Analysis.n9_touch_comparison {n : ℕ}
    {u F g B : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)))
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ y, (hessianMatrix g y).PosDef)
    (hlog : ∀ y, B y ≤ Real.log (hessianMatrix g y).det)
    (h x : EuclideanSpace ℝ (Fin n)) {α : ℝ} (ha : 0 < α)
    (hm : ∀ y, FunctionalInequalities.Analysis.n9_average g h y - α * u y ≤
      FunctionalInequalities.Analysis.n9_average g h x - α * u x) :
    (B (x + h) + B (x - h)) / 2 - n * Real.log α ≤ F x := by
  let V := FunctionalInequalities.Analysis.n9_average g h
  let M := (1 / 2 : ℝ) • (hessianMatrix g (x + h) + hessianMatrix g (x - h))
  let ψ := fun y => α⁻¹ * (V y - (V x - α * u x))
  have hV : ContDiff ℝ 2 V := n9_average_smooth hg h
  have hM : M.PosDef :=
    ((hpos (x + h)).add (hpos (x - h))).smul (by norm_num)
  have hψ : ContDiff ℝ 2 ψ := contDiff_const.mul (hV.sub contDiff_const)
  have hH : hessianMatrix ψ x = α⁻¹ • M := by
    dsimp [ψ]
    rw [n9_hessian_mul (hV.sub contDiff_const),
      n9_hessian_sub_const hV]
    exact congrArg (fun Q => α⁻¹ • Q) (n9_hessian_average hg h x)
  have hcontact : u x = ψ x := by
    dsimp [ψ]
    field_simp
    ring
  have htouch : ∀ᶠ y in 𝓝 x, ψ y ≤ u y := by
    apply Filter.Eventually.of_forall
    intro y
    apply (inv_mul_le_iff₀ ha).2
    have hy := hm y
    change V y - α * u y ≤ V x - α * u x at hy
    linarith
  have hdet : (α⁻¹ • M).det ≤ Real.exp (F x) := by
    rw [← hH]
    exact det_hessianMatrix_le_of_lower_touch_readable hconv isOpen_univ
      (fun G hG _ => hMA G hG) (mem_univ x)
      (Real.continuous_exp.comp hF).continuousAt (Real.exp_pos _).le
      hψ.contDiffAt (hH ▸ (hM.smul (inv_pos.mpr ha)).posSemidef)
      hcontact htouch
  exact n9_scaled_det_comparison ha hM
    (n9_midpoint_det (hpos (x + h)) (hpos (x - h))
      (hlog (x + h)) (hlog (x - h))) hdet
set_option maxHeartbeats 800000 in
/-- **A penalised maximum with the log-density comparison** (weak Letwin route; KLS500
`exists_weak_moment_maximum_with_target_comparison`): let the convex, Lipschitz, coercive `u` be an Alexandrov
solution `vol ∂u(G) = ∫_G e^F` with continuous `F`, and let `uₖ` be `C²` approximations, uniformly close to `u`,
with positive definite Hessians satisfying `Fₖ ≤ log det ∇²uₖ` for `Fₖ → F` locally uniformly. Then for
every `η > 0`, `Δ²ₕu − η u` has a maximiser `x₀` with `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. -/
theorem solution {n : ℕ} {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {L : NNReal} (hLip : LipschitzWith L u)
    (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R}) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (FunctionalInequalities.Analysis.subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {uk Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (huk : ∀ k, ContDiff ℝ 2 (uk k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k x, |uk k x - u x| ≤ δ k)
    (hFk : TendstoLocallyUniformly Fk F atTop)
    (hpos : ∀ k x, (FunctionalInequalities.Probability.Stein.hessianMatrix (uk k) x).PosDef)
    (hlog : ∀ k x, Fk k x ≤ Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix (uk k) x).det)
    (h : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : EuclideanSpace ℝ (Fin n),
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      F (x₀ + h) + F (x₀ - h) - 2 * F x₀ ≤ η * n := by
  classical
  let α : ℝ := 1 + η / 2
  have hα : 1 < α := by dsimp [α]; linarith
  have hα0 : 0 < α := by linarith
  let A := FunctionalInequalities.Analysis.n9_average u h
  let V := fun k => FunctionalInequalities.Analysis.n9_average (uk k) h
  have hu : Continuous u := hLip.continuous
  have hA : Continuous A := FunctionalInequalities.Analysis.n9_average_continuous hu h
  have hV : ∀ k, ContDiff ℝ 2 (V k) := fun k => FunctionalInequalities.Analysis.n9_average_smooth (huk k) h
  have hc : ∀ k y, |V k y - A y| ≤ δ k := by
    intro k y
    have hp := abs_le.mp (hclose k (y + h))
    have hm := abs_le.mp (hclose k (y - h))
    dsimp [V, A, FunctionalInequalities.Analysis.n9_average]
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  have hbound : ∀ y, A y ≤ u y + (L : ℝ) * ‖h‖ := by
    intro y
    have hp := FunctionalInequalities.Analysis.n9_lipschitz_translate hLip y h
    have hm : u (y - h) ≤ u y + (L : ℝ) * ‖h‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        FunctionalInequalities.Analysis.n9_lipschitz_translate hLip y (-h)
    dsimp [A, FunctionalInequalities.Analysis.n9_average]
    linarith
  obtain ⟨R, x, hx, hmax⟩ :=
    FunctionalInequalities.Analysis.n9_maximizers hu hcoer (fun k => (hV k).continuous) hδ hc hbound hα
  obtain ⟨x₀, _, s, hs, hxs⟩ := (hcoer R).tendsto_subseq hx
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hux : Tendsto (fun j => u (x (s j))) atTop (𝓝 (u x₀)) :=
    hu.continuousAt.tendsto.comp hxs
  have hAx : Tendsto (fun j => V (s j) (x (s j))) atTop (𝓝 (A x₀)) :=
    FunctionalInequalities.Analysis.n9_limit hδ hc hA hsTop hxs
  have hmax₀ : ∀ y, A y - α * u y ≤ A x₀ - α * u x₀ := by
    intro y
    have hAy : Tendsto (fun j => V (s j) y) atTop (𝓝 (A y)) :=
      FunctionalInequalities.Analysis.n9_limit hδ hc hA hsTop tendsto_const_nhds
    exact le_of_tendsto_of_tendsto (hAy.sub_const (α * u y))
      (hAx.sub (hux.const_mul α))
      (Filter.Eventually.of_forall (fun j => hmax (s j) y))
  have hcomp : ∀ k,
      (Fk k (x k + h) + Fk k (x k - h)) / 2 -
        n * Real.log α ≤ F (x k) := by
    intro k
    exact FunctionalInequalities.Analysis.n9_touch_comparison hconv hF hMA (huk k) (hpos k) (hlog k)
      h (x k) hα0 (hmax k)
  have hFks : TendstoLocallyUniformly (fun j => Fk (s j)) F atTop := by
    intro U hU z
    obtain ⟨t, ht, he⟩ := hFk U hU z
    exact ⟨t, ht, hsTop.eventually he⟩
  have hp : Tendsto (fun j => Fk (s j) (x (s j) + h))
      atTop (𝓝 (F (x₀ + h))) :=
    hFks.tendsto_comp hF.continuousAt (hxs.add_const h)
  have hm : Tendsto (fun j => Fk (s j) (x (s j) - h))
      atTop (𝓝 (F (x₀ - h))) :=
    hFks.tendsto_comp hF.continuousAt (hxs.sub_const h)
  have hFx : Tendsto (fun j => F (x (s j))) atTop (𝓝 (F x₀)) :=
    hF.continuousAt.tendsto.comp hxs
  have hlim : (F (x₀ + h) + F (x₀ - h)) / 2 -
      n * Real.log α ≤ F x₀ :=
    le_of_tendsto_of_tendsto (((hp.add hm).div_const 2).sub_const
      (n * Real.log α)) hFx
      (Filter.Eventually.of_forall (fun j => hcomp (s j)))
  refine ⟨x₀, ?_, ?_⟩
  · intro y
    have hy := hmax₀ y
    dsimp [A, FunctionalInequalities.Analysis.n9_average, α] at hy
    linarith
  · have hlogα : Real.log α ≤ η / 2 := by
      have hh := Real.log_le_sub_one_of_pos hα0
      dsimp [α] at hh ⊢
      linarith
    have hn := mul_le_mul_of_nonneg_left hlogα (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
