-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.theorem_7_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:34:54.649327+00:00
-- url     : https://prove2.me/submissions/c068bd59-f82a-4ef2-bfbb-57fcf0e42750
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Alg76
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_2
import Theorems.Thm_GenNewtonSubgrad_Composite_remark_7_7
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_4_i
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_5
import Theorems.Thm_GenNewtonSubgrad_Composite_theorem_5_7_local

open Filter Topology
open scoped InnerProductSpace

namespace GNCAux
open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma quadF_expand (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x h : E) :
    quadF A b α (x + h) = quadF A b α x + ⟪A x + b, h⟫_ℝ + (1/2) * ⟪A h, h⟫_ℝ := by
  have hs : ⟪A h, x⟫_ℝ = ⟪h, A x⟫_ℝ := by
    have := hA.isSymmetric h x
    simpa using this
  simp only [quadF, map_add, inner_add_left, inner_add_right]
  rw [hs, real_inner_comm h (A x)]
  ring

lemma hasGradientAt_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    HasGradientAt (quadF A b α) (A x + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : ∀ h : E, quadF A b α (x + h) - quadF A b α x - (InnerProductSpace.toDual ℝ E (A x + b)) h
      = (1/2) * ⟪A h, h⟫_ℝ := by
    intro h
    rw [quadF_expand A hA b α x h, InnerProductSpace.toDual_apply_apply]
    ring
  simp_rw [key]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : E => ‖h‖ ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound (‖A‖ / 2) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_pow, norm_norm]
    have h1 : |⟪A h, h⟫_ℝ| ≤ ‖A‖ * ‖h‖ ^ 2 := by
      calc |⟪A h, h⟫_ℝ| ≤ ‖A h‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖h‖ * ‖h‖ := by gcongr; exact A.le_opNorm h
        _ = ‖A‖ * ‖h‖ ^ 2 := by ring
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    nlinarith
  · exact Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2)

lemma gradient_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    gradient (quadF A b α) x = A x + b :=
  (hasGradientAt_quadF A hA b α x).gradient

lemma contDiff_quadF (A : E →L[ℝ] E) (b : E) (α : ℝ) : ContDiff ℝ 2 (quadF A b α) := by
  unfold quadF
  have h1 : ContDiff ℝ 2 (fun x : E => ⟪A x, x⟫_ℝ) := (A.contDiff).inner ℝ contDiff_id
  have h2 : ContDiff ℝ 2 (fun x : E => ⟪b, x⟫_ℝ) := contDiff_const.inner ℝ contDiff_id
  exact ((contDiff_const.mul h1).add h2).add contDiff_const


lemma ereal_shift_iff (a b : EReal) (r s : ℝ) :
    a + (r : EReal) ≤ b + (s : EReal) ↔ a + ((r - s : ℝ) : EReal) ≤ b := by
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    simp [← EReal.coe_add, EReal.coe_le_coe_iff, -EReal.coe_sub]
  constructor <;> intro <;> linarith

lemma ereal_neg_add_cancel (c : ℝ) (a : EReal) : ((-c : ℝ) : EReal) + ((c : EReal) + a) = a := by
  induction a using EReal.rec
  · simp
  · rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
  · simp

lemma ereal_le_of_add_le {a b : EReal} {r s : ℝ} (hrs : r ≤ s) (h : a + (s : EReal) ≤ b) :
    a + (r : EReal) ≤ b :=
  le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 hrs) a) h


lemma ereal_rearr (a b : EReal) (c d r : ℝ) :
    ((c : EReal) + a) + (r : EReal) ≤ (d : EReal) + b ↔ a + ((c + r - d : ℝ) : EReal) ≤ b := by
  have e1 : ((c : EReal) + a) + (r : EReal) = a + ((c + r : ℝ) : EReal) := by
    rw [EReal.coe_add, add_comm (c : EReal) a, add_assoc]
  rw [e1, add_comm (d : EReal) b, ereal_shift_iff]

lemma quad_small (A : E →L[ℝ] E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 x, |(1/2) * ⟪A (z - x), z - x⟫_ℝ| ≤ ε * ‖z - x‖ := by
  have hpos : 0 < ε / (‖A‖ + 1) := div_pos hε (by positivity)
  filter_upwards [Metric.ball_mem_nhds x hpos] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  set h := z - x
  have h1 : |⟪A h, h⟫_ℝ| ≤ ‖A‖ * ‖h‖ * ‖h‖ := by
    calc |⟪A h, h⟫_ℝ| ≤ ‖A h‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖h‖ * ‖h‖ := by gcongr; exact A.le_opNorm h
  have h2 : ‖A‖ * ‖h‖ ≤ ε := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < ‖A‖ + 1)).1 hz
    nlinarith [norm_nonneg h, norm_nonneg A]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  have := norm_nonneg h
  nlinarith [mul_le_mul_of_nonneg_right h2 this]

lemma regSubgrad_sum_iff (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ)
    (g : E → EReal) (x v : E) :
    IsRegularSubgrad (sumFn (quadF A b α) g) x v ↔ IsRegularSubgrad g x (v - (A x + b)) := by
  have hexp : ∀ z : E, quadF A b α z = quadF A b α x + ⟪A x + b, z - x⟫_ℝ +
      (1/2) * ⟪A (z - x), z - x⟫_ℝ := by
    intro z; have := quadF_expand A hA b α x (z - x); simpa using this
  have hfin : sumFn (quadF A b α) g x ≠ ⊤ ↔ g x ≠ ⊤ := by
    unfold sumFn
    constructor
    · intro h hg; apply h; rw [hg]; simp
    · intro h; exact EReal.add_ne_top (EReal.coe_ne_top _) h
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨hfin.1 h0, fun ε hε => ?_⟩
    filter_upwards [h (ε/2) (by linarith), quad_small A x (by linarith : 0 < ε/2)] with z hz hq
    unfold sumFn at hz
    rw [ereal_rearr] at hz
    refine ereal_le_of_add_le ?_ hz
    rw [hexp z, inner_sub_left]
    have := (abs_le.1 hq).2
    linarith
  · rintro ⟨h0, h⟩
    refine ⟨hfin.2 h0, fun ε hε => ?_⟩
    filter_upwards [h (ε/2) (by linarith), quad_small A x (by linarith : 0 < ε/2)] with z hz' hq
    unfold sumFn
    rw [ereal_rearr]
    refine ereal_le_of_add_le ?_ hz'
    rw [hexp z, inner_sub_left]
    have := (abs_le.1 hq).1
    linarith


lemma tendsto_coe_add {u : ℕ → ℝ} {c : ℝ} {a : ℕ → EReal} {l : EReal}
    (hu : Tendsto u atTop (𝓝 c)) (ha : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun t => (u t : EReal) + a t) atTop (𝓝 ((c : EReal) + l)) :=
  ((EReal.continuousAt_add (p := ((c : EReal), l)) (Or.inl (EReal.coe_ne_top c))
    (Or.inl (EReal.coe_ne_bot c))).tendsto).comp
    (((continuous_coe_real_ereal.tendsto c).comp hu).prodMk_nhds ha)

lemma limSubdiff_sum_iff (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ)
    (g : E → EReal) (x v : E) :
    v ∈ LimitingSubdiff (sumFn (quadF A b α) g) x ↔ v - (A x + b) ∈ LimitingSubdiff g x := by
  have hcont : Continuous (quadF A b α) := (contDiff_quadF A b α).continuous
  have hfin : sumFn (quadF A b α) g x ≠ ⊤ ↔ g x ≠ ⊤ := by
    unfold sumFn
    constructor
    · intro h hg; apply h; rw [hg]; simp
    · intro h; exact EReal.add_ne_top (EReal.coe_ne_top _) h
  have hAc : ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun t => A (xs t) + b) atTop (𝓝 (A x + b)) := fun xs hx =>
    ((A.continuous.tendsto x).comp hx).add_const b
  constructor
  · rintro ⟨h0, xs, vs, hx, hφ, hv, hreg⟩
    refine ⟨hfin.1 h0, xs, fun t => vs t - (A (xs t) + b), hx, ?_, hv.sub (hAc xs hx),
      fun t => (regSubgrad_sum_iff A hA b α g (xs t) (vs t)).1 (hreg t)⟩
    have key : ∀ y, g y = ((-(quadF A b α y) : ℝ) : EReal) + sumFn (quadF A b α) g y := by
      intro y; unfold sumFn; rw [ereal_neg_add_cancel]
    simp_rw [key]
    exact tendsto_coe_add ((hcont.tendsto x).comp hx).neg hφ
  · rintro ⟨h0, xs, ws, hx, hg, hw, hreg⟩
    refine ⟨hfin.2 h0, xs, fun t => ws t + (A (xs t) + b), hx, ?_, ?_, fun t => ?_⟩
    · unfold sumFn
      exact tendsto_coe_add ((hcont.tendsto x).comp hx) hg
    · have := hw.add (hAc xs hx)
      simpa using this
    · rw [regSubgrad_sum_iff A hA b α g]
      simpa using hreg t


/-- graph shift `(x, w) ↦ (x, w + A x + c)` -/
def Tsh (A : E →L[ℝ] E) (c : E) (p : E × E) : E × E := (p.1, p.2 + A p.1 + c)
/-- its linear part -/
def Lsh (A : E →L[ℝ] E) (p : E × E) : E × E := (p.1, p.2 + A p.1)
/-- adjoint of the linear part (A self-adjoint) -/
def adj (A : E →L[ℝ] E) (a : E × E) : E × E := (a.1 + A a.2, a.2)

lemma continuous_Tsh (A : E →L[ℝ] E) (c : E) : Continuous (Tsh A c) := by
  unfold Tsh; fun_prop

lemma continuous_Lsh (A : E →L[ℝ] E) : Continuous (Lsh A) := by
  unfold Lsh; fun_prop

lemma continuous_adj (A : E →L[ℝ] E) : Continuous (adj A) := by
  unfold adj; fun_prop

lemma Tsh_sub (A : E →L[ℝ] E) (c : E) (w z : E × E) :
    Tsh A c w - Tsh A c z = Lsh A (w - z) := by
  simp only [Tsh, Lsh, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, map_sub]
  congr 1; abel

lemma Tsh_inv (A : E →L[ℝ] E) (c : E) (w : E × E) : Tsh A c (Tsh (-A) (-c) w) = w := by
  simp only [Tsh, ContinuousLinearMap.neg_apply]
  refine Prod.ext rfl ?_
  simp only; abel

lemma Tsh_inv' (A : E →L[ℝ] E) (c : E) (w : E × E) : Tsh (-A) (-c) (Tsh A c w) = w := by
  simp only [Tsh, ContinuousLinearMap.neg_apply]
  refine Prod.ext rfl ?_
  simp only; abel

lemma Lsh_inv (A : E →L[ℝ] E) (w : E × E) : Lsh (-A) (Lsh A w) = w := by
  simp only [Lsh, ContinuousLinearMap.neg_apply]
  refine Prod.ext rfl ?_
  simp only; abel

lemma Tsh_add_smul (A : E →L[ℝ] E) (c z ds : E × E) (t : ℝ) :
    Tsh A c.1 z + t • ds = Tsh A c.1 (z + t • Lsh (-A) ds) := by
  simp only [Tsh, Lsh, ContinuousLinearMap.neg_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_add, smul_neg, Prod.mk_add_mk]
  ext <;> simp <;> abel

lemma pair_adj (A : E →L[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (a h : E × E) :
    pairInner (adj A a) h = pairInner a (Lsh A h) := by
  simp only [pairInner, adj, Lsh, inner_add_left, inner_add_right]
  rw [hA a.2 h.1]; ring

lemma symm_of_sa (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ :=
  fun x y => by simpa using hA.isSymmetric x y

lemma norm_Lsh_le (A : E →L[ℝ] E) (h : E × E) : ‖Lsh A h‖ ≤ (1 + ‖A‖) * ‖h‖ := by
  have h1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have h2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have hA0 := norm_nonneg A
  rw [show Lsh A h = (h.1, h.2 + A h.1) from rfl, Prod.norm_mk]
  apply max_le
  · nlinarith [norm_nonneg h]
  · calc ‖h.2 + A h.1‖ ≤ ‖h.2‖ + ‖A h.1‖ := norm_add_le _ _
      _ ≤ ‖h.2‖ + ‖A‖ * ‖h.1‖ := by gcongr; exact A.le_opNorm _
      _ ≤ (1 + ‖A‖) * ‖h‖ := by nlinarith

lemma regN_transfer (A : E →L[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (c : E) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Tsh A c w ∈ S') {z a : E × E} (hz : z ∈ S)
    (ha : a ∈ regNormal S' (Tsh A c z)) : adj A a ∈ regNormal S z := by
  refine ⟨hz, fun ε hε => ?_⟩
  have hK : 0 < 1 + ‖A‖ := by positivity
  have h1 := ha.2 (ε / (1 + ‖A‖)) (div_pos hε hK)
  have h2 := ((continuous_Tsh A c).tendsto z).eventually h1
  filter_upwards [h2] with w hw hwS
  have := hw (hS w hwS)
  rw [pair_adj A hA, ← Tsh_sub]
  refine this.trans ?_
  rw [Tsh_sub]
  calc ε / (1 + ‖A‖) * ‖Lsh A (w - z)‖ ≤ ε / (1 + ‖A‖) * ((1 + ‖A‖) * ‖w - z‖) := by
        gcongr; exact norm_Lsh_le A _
    _ = ε * ‖w - z‖ := by field_simp

lemma limN_transfer (A : E →L[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (c : E) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Tsh A c w ∈ S') (hS' : ∀ w ∈ S', Tsh (-A) (-c) w ∈ S) {z a : E × E}
    (hz : z ∈ S) (ha : a ∈ limNormal S' (Tsh A c z)) : adj A a ∈ limNormal S z := by
  obtain ⟨-, zs, as, hzs, hzl, hal, hreg⟩ := ha
  refine ⟨hz, fun k => Tsh (-A) (-c) (zs k), fun k => adj A (as k), fun k => hS' _ (hzs k),
    ?_, ((continuous_adj A).tendsto a).comp hal, fun k => ?_⟩
  · have := ((continuous_Tsh (-A) (-c)).tendsto _).comp hzl
    rwa [Tsh_inv'] at this
  · apply regN_transfer A hA c hS (hS' _ (hzs k))
    rw [Tsh_inv]; exact hreg k

lemma dirLimN_transfer (A : E →L[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (c : E) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Tsh A c w ∈ S') (hS' : ∀ w ∈ S', Tsh (-A) (-c) w ∈ S) {z a d : E × E}
    (hz : z ∈ S) (ha : a ∈ dirLimNormal S' (Tsh A c z) (Lsh A d)) :
    adj A a ∈ dirLimNormal S z d := by
  obtain ⟨-, ts, ds, as, hts, htl, hdl, hal, hreg⟩ := ha
  refine ⟨hz, ts, fun k => Lsh (-A) (ds k), fun k => adj A (as k), hts, htl, ?_,
    ((continuous_adj A).tendsto a).comp hal, fun k => ?_⟩
  · have := ((continuous_Lsh (-A)).tendsto _).comp hdl
    rwa [Lsh_inv] at this
  · have hk := hreg k
    have e := Tsh_add_smul A (c, c) z (ds k) (ts k)
    simp only at e
    rw [e] at hk
    have hmem : z + ts k • Lsh (-A) (ds k) ∈ S := by
      have := hS' _ hk.1
      rwa [Tsh_inv'] at this
    exact regN_transfer A hA c hS hmem hk


lemma gph_fwd (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (g : E → EReal) :
    ∀ w ∈ gph (LimitingSubdiff g), Tsh A b w ∈ gph (LimitingSubdiff (sumFn (quadF A b α) g)) := by
  intro w hw
  show w.2 + A w.1 + b ∈ LimitingSubdiff (sumFn (quadF A b α) g) w.1
  rw [limSubdiff_sum_iff A hA b α g]
  have : w.2 + A w.1 + b - (A w.1 + b) = w.2 := by abel
  rw [this]; exact hw

lemma gph_bwd (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (g : E → EReal) :
    ∀ w ∈ gph (LimitingSubdiff (sumFn (quadF A b α) g)), Tsh (-A) (-b) w ∈ gph (LimitingSubdiff g) := by
  intro w hw
  show w.2 + (-A) w.1 + -b ∈ LimitingSubdiff g w.1
  have hw' : w.2 ∈ LimitingSubdiff (sumFn (quadF A b α) g) w.1 := hw
  rw [limSubdiff_sum_iff A hA b α g] at hw'
  have : w.2 + (-A) w.1 + -b = w.2 - (A w.1 + b) := by simp; abel
  rw [this]; exact hw'

lemma semismooth_transfer (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ)
    (g : E → EReal) (xbar : E)
    (h : IsSemismoothStar (LimitingSubdiff (sumFn (quadF A b α) g)) xbar 0) :
    IsSemismoothStar (LimitingSubdiff g) xbar (-(A xbar + b)) := by
  refine ⟨?_, fun u v w u' hu' => ?_⟩
  · have := (limSubdiff_sum_iff A hA b α g xbar 0).1 h.1
    simpa using this
  · have hnA : ∀ x y : E, ⟪(-A) x, y⟫_ℝ = ⟪x, (-A) y⟫_ℝ := by
      intro x y; simp [symm_of_sa A hA x y]
    have e1 : ((xbar, -(A xbar + b)) : E × E) = Tsh (-A) (-b) (xbar, 0) := by
      simp only [Tsh, neg_apply]; refine Prod.ext rfl ?_; simp only; abel
    have e2 : ((u, v) : E × E) = Lsh (-A) (u, v + A u) := by
      simp only [Lsh, neg_apply]; refine Prod.ext rfl ?_; simp only; abel
    have hu'' : ((u', -w) : E × E) ∈ dirLimNormal (gph (LimitingSubdiff g))
        (Tsh (-A) (-b) (xbar, 0)) (Lsh (-A) (u, v + A u)) := by
      rw [← e1, ← e2]; exact hu'
    have hS' : ∀ w ∈ gph (LimitingSubdiff g),
        Tsh (-(-A)) (-(-b)) w ∈ gph (LimitingSubdiff (sumFn (quadF A b α) g)) := by
      simp only [neg_neg]; exact gph_fwd A hA b α g
    have hz : ((xbar, 0) : E × E) ∈ gph (LimitingSubdiff (sumFn (quadF A b α) g)) := h.1
    have key := dirLimN_transfer (-A) hnA (-b) (gph_bwd A hA b α g) hS' hz hu''
    have e3 : adj (-A) ((u', -w) : E × E) = (u' + A w, -w) := by
      simp only [adj, neg_apply, map_neg, neg_neg]
    rw [e3] at key
    have hss := h.2 u (v + A u) w (u' + A w) key
    have hsym : ⟪A w, u⟫_ℝ = ⟪w, A u⟫_ℝ := by simpa using hA.isSymmetric w u
    rw [inner_add_left, inner_add_right, hsym] at hss
    linarith

lemma secondSubdiff_transfer (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ)
    (g : E → EReal) (p v' d' z : E)
    (h : z ∈ secondSubdiff (sumFn (quadF A b α) g) p v' d') :
    z - A d' ∈ secondSubdiff g p (v' - (A p + b)) d' := by
  have h' : ((z, -d') : E × E) ∈ limNormal (gph (LimitingSubdiff (sumFn (quadF A b α) g))) (p, v') := h
  have hmem : v' ∈ LimitingSubdiff (sumFn (quadF A b α) g) p := h'.1
  have hz : ((p, v' - (A p + b)) : E × E) ∈ gph (LimitingSubdiff g) :=
    (limSubdiff_sum_iff A hA b α g p v').1 hmem
  have e1 : ((p, v') : E × E) = Tsh A b (p, v' - (A p + b)) := by
    simp only [Tsh]; refine Prod.ext rfl ?_; simp only; abel
  rw [e1] at h'
  have hS' : ∀ w ∈ gph (LimitingSubdiff (sumFn (quadF A b α) g)),
      Tsh (-A) (-b) w ∈ gph (LimitingSubdiff g) := gph_bwd A hA b α g
  have key := limN_transfer A (symm_of_sa A hA) b (gph_fwd A hA b α g) hS' hz h'
  have e3 : adj A ((z, -d') : E × E) = (z - A d', -d') := by
    simp only [adj, map_neg]; refine Prod.ext ?_ rfl; simp only; abel
  rw [e3] at key
  exact key

lemma prox_fermat (g : E → EReal) (hg : IsProperFn g) {γ : ℝ} (hγ : 0 < γ) (u v : E)
    (hv : v ∈ prox g γ u) : γ⁻¹ • (u - v) ∈ LimitingSubdiff g v := by
  have hfin : g v ≠ ⊤ := by
    obtain ⟨y0, hy0⟩ := hg.2
    intro htop
    have := hv y0
    rw [htop, EReal.top_add_coe] at this
    exact (EReal.add_ne_top hy0 (EReal.coe_ne_top _)) (top_le_iff.1 this)
  have hreg : IsRegularSubgrad g v (γ⁻¹ • (u - v)) := by
    refine ⟨hfin, fun ε hε => ?_⟩
    filter_upwards [Metric.ball_mem_nhds v (by positivity : (0:ℝ) < 2 * γ * ε)] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := hv z
    rw [ereal_shift_iff] at h1
    refine ereal_le_of_add_le ?_ h1
    have hexp : ‖z - u‖ ^ 2 = ‖z - v‖ ^ 2 + 2 * ⟪z - v, v - u⟫_ℝ + ‖v - u‖ ^ 2 := by
      have : z - u = (z - v) + (v - u) := by abel
      rw [this, norm_add_sq_real]
    rw [hexp, real_inner_smul_left]
    have hin : ⟪u - v, z - v⟫_ℝ = -⟪z - v, v - u⟫_ℝ := by
      rw [real_inner_comm, ← inner_neg_right, neg_sub]
    rw [hin]
    have hn := norm_nonneg (z - v)
    have hsq : ‖z - v‖ ^ 2 / (2 * γ) ≤ ε * ‖z - v‖ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have : γ⁻¹ * -⟪z - v, v - u⟫_ℝ = -(2 * ⟪z - v, v - u⟫_ℝ) / (2 * γ) := by
      field_simp
    rw [this]
    have e : ‖v - u‖ ^ 2 / (2 * γ) - (‖z - v‖ ^ 2 + 2 * ⟪z - v, v - u⟫_ℝ + ‖v - u‖ ^ 2) / (2 * γ)
        = -(2 * ⟪z - v, v - u⟫_ℝ) / (2 * γ) - ‖z - v‖ ^ 2 / (2 * γ) := by ring
    rw [e]; linarith
  exact ⟨hfin, fun _ => v, fun _ => γ⁻¹ • (u - v), tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => hreg⟩

end GNCAux

open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNCAux in
theorem solution {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g)) xbar 0) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      ∃ U ∈ 𝓝 xbar, Alg76WellDefinedOn A b α g γ U ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsAlg76Run A b α g γ x → x 0 ∈ U →
          GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by
  classical
  have hgrad : ∀ x, gradient (quadF A b α) x = A x + b := gradient_quadF A hA b α
  obtain ⟨γ2, hγ2, hγ2r, h72⟩ := proposition_7_2 (quadF A b α) g xbar r ε
    ⟨Set.univ, Filter.univ_mem, (contDiff_quadF A b α).contDiffOn⟩ hstat hg hpb
    (by rw [hgrad]; exact hpr)
  obtain ⟨γ7, hγ7, -, h77⟩ := remark_7_7 A hA b α g xbar r ε hg hpb hpr hstat
  obtain ⟨γ4, hγ4, -, h74⟩ := proposition_7_4_i A hA b α g xbar r ε hg hpb hpr hstat
  obtain ⟨γ5, hγ5, -, h75⟩ := proposition_7_5 A hA b α g xbar r ε hg hpb hpr hstat
  refine ⟨min (min γ2 γ7) (min γ4 γ5), lt_min (lt_min hγ2 hγ7) (lt_min hγ4 hγ5),
    (min_le_left _ _).trans ((min_le_left _ _).trans hγ2r), fun γ hγ hγlt hB => ?_⟩
  have lt2 : γ < γ2 := lt_of_lt_of_le hγlt ((min_le_left _ _).trans (min_le_left _ _))
  have lt7 : γ < γ7 := lt_of_lt_of_le hγlt ((min_le_left _ _).trans (min_le_right _ _))
  have lt4 : γ < γ4 := lt_of_lt_of_le hγlt ((min_le_right _ _).trans (min_le_left _ _))
  have lt5 : γ < γ5 := lt_of_lt_of_le hγlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨U2, hU2, P, hP, ⟨L, hL⟩, -⟩ := h72 γ hγ lt2
  obtain ⟨U7, hU7, h7⟩ := h77 γ hγ lt7 hB
  obtain ⟨-, hMR⟩ := h74 γ hγ lt4 hB
  have hSS := (h75 γ hγ lt5 hB (semismooth_transfer A hA b α g xbar hH.2.2.2)).2
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (fbe (quadF A b α) g γ y).toReal with hψdef
  -- basic facts on W0 = U2 ∩ U7
  have hPmem : ∀ x ∈ U2, P x ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) := by
    intro x hx
    have := hP x hx
    rw [hgrad] at this
    rw [this]; exact Set.mem_singleton _
  have hgψ : ∀ x ∈ U2 ∩ U7, gradient ψ x = γ⁻¹ • shiftOp A γ (x - P x) := fun x hx =>
    ((h7 x hx.2).2.2.2.2 (P x) (hPmem x hx.1)).1
  have hψ0 : gradient ψ xbar = 0 := ((h7 xbar (mem_of_mem_nhds hU7)).2.2.1).1 hstat
  have hW0 : U2 ∩ U7 ∈ 𝓝 xbar := Filter.inter_mem hU2 hU7
  have hxbarW0 : xbar ∈ U2 ∩ U7 := mem_of_mem_nhds hW0
  have hPx : P xbar = xbar := by
    have h1 := hgψ xbar hxbarW0
    rw [hψ0, eq_comm, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (inv_ne_zero hγ.ne')
    · have : xbar - P xbar = 0 := hB.1 (by rw [h1, map_zero])
      exact (sub_eq_zero.1 this).symm
  -- the explicit gradient map F and its Lipschitz property
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => (γ⁻¹ • shiftOp A γ) (x - P x) with hFdef
  have hFL : LipschitzOnWith (‖γ⁻¹ • shiftOp A γ‖₊ * (1 + L)) F (U2 ∩ U7) := by
    have h1 : LipschitzOnWith (1 + L) (fun x => x - P x) (U2 ∩ U7) :=
      (LipschitzWith.id.lipschitzOnWith).sub (hL.mono Set.inter_subset_left)
    exact (γ⁻¹ • shiftOp A γ).lipschitz.comp_lipschitzOnWith h1
  have hFeq : Set.EqOn F (gradient ψ) (U2 ∩ U7) := by
    intro x hx
    rw [hgψ x hx]; rfl
  have hgL : LipschitzOnWith (‖γ⁻¹ • shiftOp A γ‖₊ * (1 + L)) (gradient ψ) (U2 ∩ U7) := by
    intro x hx y hy
    rw [← hFeq hx, ← hFeq hy]; exact hFL hx hy
  have hC : IsC11Around ψ xbar :=
    ⟨U2 ∩ U7, hW0, fun x hx => (h7 x hx.2).1.2.2, _, hgL⟩
  -- continuity at xbar
  have hPc : ContinuousAt P xbar := (hL.continuousOn).continuousAt hU2
  have hgc : ContinuousAt (gradient ψ) xbar :=
    (hgL.continuousOn).continuousAt hW0
  -- (H1) for the gradient of the envelope
  obtain ⟨U1, hU1, V1, hV1, hH1⟩ := hH.2.1
  have hH1ψ : H1 (sv (gradient ψ)) xbar 0 := by
    refine ⟨U2 ∩ U7 ∩ (P ⁻¹' U1 ∩ gradient ψ ⁻¹' V1), Filter.inter_mem hW0
      (Filter.inter_mem (hPc.preimage_mem_nhds (by rw [hPx]; exact hU1))
        (hgc.preimage_mem_nhds (by rw [hψ0]; exact hV1))), Set.univ, Filter.univ_mem,
      fun x hx v _ hv => ?_⟩
    have hv' : v = gradient ψ x := hv
    subst hv'
    obtain ⟨hxW, hxU1, hxV1⟩ := hx
    set p := P x with hp
    have hpm := hPmem x hxW.1
    have hfer := prox_fermat g hg hγ _ p hpm
    have hveq : gradient ψ x = γ⁻¹ • (x - p) - A (x - p) := by
      rw [hgψ x hxW]
      have hs : shiftOp A γ (x - p) = (x - p) - γ • A (x - p) := by
        simp [shiftOp]
      rw [hs, smul_sub (γ⁻¹) (x - p) (γ • A (x - p)), smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
    have hshift : gradient ψ x - (A p + b) = γ⁻¹ • ((x - γ • (A x + b)) - p) := by
      rw [hveq]
      have e : (x - γ • (A x + b)) - p = (x - p) - γ • (A x + b) := by abel
      rw [e, smul_sub (γ⁻¹) (x - p) (γ • (A x + b)), smul_smul, inv_mul_cancel₀ hγ.ne', one_smul,
        map_sub]
      abel
    have hmem : gradient ψ x ∈ LimitingSubdiff (sumFn (quadF A b α) g) p := by
      rw [limSubdiff_sum_iff A hA b α g, hshift]; exact hfer
    obtain ⟨d', hd'⟩ := hH1 p hxU1 (gradient ψ x) hxV1 hmem
    have ht := secondSubdiff_transfer A hA b α g p (gradient ψ x) d' _ hd'
    rw [hshift] at ht
    refine ⟨d' - (x - p), ?_⟩
    apply (((h7 x hxW.2).2.2.2.2 p hpm).2.1 (d' - (x - p))).1
    have e1 : x - p + (d' - (x - p)) = d' := by abel
    have e2 : -(γ⁻¹ • (x - p)) - A (d' - (x - p)) = -gradient ψ x - A d' := by
      rw [hveq, map_sub]; abel
    rw [e1, e2]; exact ht
  have hSH : StandingH (sv (gradient ψ)) xbar 0 := by
    refine ⟨?_, hH1ψ, ?_, ?_⟩
    · show (0 : EuclideanSpace ℝ (Fin n)) ∈ ({gradient ψ xbar} : Set _)
      rw [hψ0]; exact Set.mem_singleton _
    · have := hMR.1 hH.2.2.1
      rwa [hψ0] at this
    · rwa [hψ0] at hSS
  obtain ⟨W, hW, hWdef, hWconv⟩ := theorem_5_7_local ψ xbar hC hψ0 hSH U7 hU7
  have hstep : ∀ y ∈ U7, ∀ y', alg76Step A b α g γ y y' ↔ alg53Step ψ y y' :=
    fun y hy => (h7 y hy).2.2.2.1
  have key : ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 ∈ W → ∀ N : ℕ,
      (∀ k < N, alg76Step A b α g γ (x k) (x (k + 1))) →
        ∀ k < N, alg53Step ψ (x k) (x (k + 1)) := by
    intro x h0 N
    induction N with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
      intro hs k hk
      have ih' := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact ih' k hk
      · subst hk
        exact (hstep _ (hWdef k x h0 ih').1 _).1 (hs k (Nat.lt_succ_self k))
  refine ⟨W, hW, fun N x h0 hs => ?_, fun x hrun h0 => ?_⟩
  · obtain ⟨hxN, x', hx'⟩ := hWdef N x h0 (key x h0 N hs)
    exact ⟨x', (hstep _ hxN x').2 hx'⟩
  · exact hWconv x (fun k => key x h0 (k + 1) (fun j _ => hrun j) k (Nat.lt_succ_self k)) h0
