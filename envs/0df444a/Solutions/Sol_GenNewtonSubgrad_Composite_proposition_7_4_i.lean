-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.proposition_7_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:19:27.313159+00:00
-- url     : https://prove2.me/submissions/75f10a7d-c385-4bec-8780-7dfacb95074a

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_2
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii

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

namespace GNC73
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regN_gen (Φ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') {z a : E × E} (hz : z ∈ S) (ha : a ∈ regNormal S' (Φ z)) :
    adjm a ∈ regNormal S z := by
  refine ⟨hz, fun ε hε => ?_⟩
  have hΦc : Continuous Φ := by
    have : Φ = fun w => Φ 0 + Λ w := by
      funext w; have := hΦ w 0; rw [sub_zero] at this; rw [← this]; abel
    rw [this]; exact continuous_const.add Λ.continuous
  have hK : 0 < ‖Λ‖ + 1 := by positivity
  have h1 := ha.2 (ε / (‖Λ‖ + 1)) (div_pos hε hK)
  have h2 := (hΦc.tendsto z).eventually h1
  filter_upwards [h2] with w hw hwS
  have := hw (hS w hwS)
  rw [hadj, ← hΦ]
  refine this.trans ?_
  rw [hΦ]
  calc ε / (‖Λ‖ + 1) * ‖Λ (w - z)‖ ≤ ε / (‖Λ‖ + 1) * ((‖Λ‖ + 1) * ‖w - z‖) := by
        gcongr
        calc ‖Λ (w - z)‖ ≤ ‖Λ‖ * ‖w - z‖ := Λ.le_opNorm _
          _ ≤ (‖Λ‖ + 1) * ‖w - z‖ := by nlinarith [norm_nonneg (w - z)]
    _ = ε * ‖w - z‖ := by field_simp

lemma limN_gen (Φ Ψ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨc : Continuous Ψ) (hΦΨ : ∀ w, Φ (Ψ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z a : E × E} (hz : z ∈ S)
    (hΨΦ : Ψ (Φ z) = z) (ha : a ∈ limNormal S' (Φ z)) : adjm a ∈ limNormal S z := by
  obtain ⟨-, zs, as, hzs, hzl, hal, hreg⟩ := ha
  refine ⟨hz, fun k => Ψ (zs k), fun k => adjm (as k), fun k => hS' _ (hzs k), ?_,
    (hadjc.tendsto a).comp hal, fun k => ?_⟩
  · have := (hΨc.tendsto _).comp hzl
    rwa [hΨΦ] at this
  · apply regN_gen Φ Λ hΦ adjm hadj hS (hS' _ (hzs k))
    rw [hΦΨ]; exact hreg k

lemma regNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ regNormal S z → a ∈ regNormal S' z := by
  rintro ⟨hz, h⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  refine ⟨hz', fun ε hε => ?_⟩
  filter_upwards [h ε hε, hN.mem_nhds hzN] with w hw hwN hwS'
  have : w ∈ S' ∩ N := ⟨hwS', hwN⟩
  rw [← hSS] at this
  exact hw this.1

lemma limNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ limNormal S z → a ∈ limNormal S' z := by
  rintro ⟨hz, zs, as, hzs, hzl, hal, hreg⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hzl.eventually (hN.mem_nhds hzN))
  have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
  refine ⟨hz', fun k => zs (k + K), fun k => as (k + K), fun k => ?_, hzl.comp hsh, hal.comp hsh,
    fun k => regNormal_local hN hSS (hK _ (Nat.le_add_left K k)) _ (hreg _)⟩
  have : zs (k + K) ∈ S ∩ N := ⟨hzs _, hK _ (Nat.le_add_left K k)⟩
  rw [hSS] at this; exact this.1

lemma coderiv_congr (F G : E → E) {U : Set E} (hU : IsOpen U) (hFG : ∀ y ∈ U, F y = G y)
    {x : E} (hx : x ∈ U) (w : E) :
    coderiv (sv F) x (F x) w = coderiv (sv G) x (G x) w := by
  have hN : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  have hSS : gph (sv F) ∩ U ×ˢ Set.univ = gph (sv G) ∩ U ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({G p.1} : Set E)
      have : p.2 ∈ ({F p.1} : Set E) := h1
      rwa [hFG p.1 h2] at this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({F p.1} : Set E)
      have : p.2 ∈ ({G p.1} : Set E) := h1
      rwa [← hFG p.1 h2] at this
  have hzN : ((x, F x) : E × E) ∈ U ×ˢ (Set.univ : Set E) := ⟨hx, Set.mem_univ _⟩
  ext u
  show (u, -w) ∈ limNormal (gph (sv F)) (x, F x) ↔ (u, -w) ∈ limNormal (gph (sv G)) (x, G x)
  rw [← hFG x hx]
  exact ⟨limNormal_local hN hSS hzN _, limNormal_local hN hSS.symm hzN _⟩

end GNC73

namespace GNC75
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- the graph form of semismoothness* -/
def SSet (S : Set (E × E)) (z : E × E) : Prop :=
  ∀ d a : E × E, a ∈ dirLimNormal S z d → pairInner a d = 0

lemma semismooth_iff_SSet (G : E → Set E) (x y : E) :
    IsSemismoothStar G x y ↔ y ∈ G x ∧ SSet (gph G) (x, y) := by
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun d a ha => ?_⟩
    have h1 := h d.1 d.2 (-a.2) a.1 (by
      show (a.1, -(-a.2)) ∈ dirLimNormal (gph G) (x, y) (d.1, d.2)
      simpa using ha)
    simp only [pairInner]
    rw [inner_neg_left] at h1
    linarith
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun u v w u' hu' => ?_⟩
    have := h (u, v) (u', -w) hu'
    simp only [pairInner, inner_neg_left] at this
    linarith

lemma dirLimN_gen (Φ Ψ : E × E → E × E) (Λ Λi : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (hΛΛi : ∀ w, Λ (Λi w) = w)
    (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨΦ : ∀ w, Ψ (Φ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z a d : E × E} (hz : z ∈ S)
    (ha : a ∈ dirLimNormal S' (Φ z) (Λ d)) : adjm a ∈ dirLimNormal S z d := by
  obtain ⟨-, ts, ds, as, hts, htl, hdl, hal, hreg⟩ := ha
  refine ⟨hz, ts, fun k => Λi (ds k), fun k => adjm (as k), hts, htl, ?_,
    (hadjc.tendsto a).comp hal, fun k => ?_⟩
  · have hΛd : Λi (Λ d) = d := by
      have h1 : Λ (Λi (Λ d)) = Λ d := hΛΛi _
      -- Λ injective from Φ/Ψ
      have hinj : Function.Injective Λ := by
        intro p q hpq
        have e1 : Φ p - Φ 0 = Φ q - Φ 0 := by rw [hΦ, hΦ, sub_zero, sub_zero, hpq]
        have e2 : Φ p = Φ q := by simpa using e1
        have := congrArg Ψ e2
        rwa [hΨΦ, hΨΦ] at this
      exact hinj h1
    have := ((Λi.continuous).tendsto _).comp hdl
    rwa [hΛd] at this
  · have hk := hreg k
    have e : Φ z + ts k • ds k = Φ (z + ts k • Λi (ds k)) := by
      have := hΦ (z + ts k • Λi (ds k)) z
      rw [add_sub_cancel_left, map_smul, hΛΛi] at this
      rw [← this]; abel
    rw [e] at hk
    have hmem : z + ts k • Λi (ds k) ∈ S := by
      have := hS' _ hk.1
      rwa [hΨΦ] at this
    exact regN_gen Φ Λ hΦ adjm hadj hS hmem hk

lemma SSet_transfer (Φ Ψ : E × E → E × E) (Λ Λi : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (hΛΛi : ∀ w, Λ (Λi w) = w)
    (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨΦ : ∀ w, Ψ (Φ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z : E × E} (hz : z ∈ S)
    (h : SSet S z) : SSet S' (Φ z) := by
  intro d' a ha
  have ha' : a ∈ dirLimNormal S' (Φ z) (Λ (Λi d')) := by rw [hΛΛi]; exact ha
  have := h _ _ (dirLimN_gen Φ Ψ Λ Λi hΦ hΛΛi adjm hadj hadjc hΨΦ hS hS' hz ha')
  rw [hadj, hΛΛi] at this
  exact this

lemma dirLimNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N)
    {z : E × E} (hzN : z ∈ N) (d a : E × E) :
    a ∈ dirLimNormal S z d → a ∈ dirLimNormal S' z d := by
  rintro ⟨hz, ts, ds, as, hts, htl, hdl, hal, hreg⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  have hpts : Tendsto (fun k => z + ts k • ds k) atTop (𝓝 z) := by
    have := tendsto_const_nhds (x := z) |>.add (htl.smul hdl)
    simpa using this
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hpts.eventually (hN.mem_nhds hzN))
  have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
  exact ⟨hz', fun k => ts (k + K), fun k => ds (k + K), fun k => as (k + K), fun k => hts _,
    htl.comp hsh, hdl.comp hsh, hal.comp hsh,
    fun k => regNormal_local hN hSS (hK _ (Nat.le_add_left K k)) _ (hreg _)⟩

lemma SSet_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N)
    {z : E × E} (hzN : z ∈ N) (h : SSet S z) : SSet S' z := fun d a ha =>
  h d a (dirLimNormal_local hN hSS.symm hzN d a ha)

end GNC75

namespace GNC74
open GenNewtonSubgrad.ProxReg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma MR_transfer (G1 G2 : E → Set E) (xbar : E) (c : E →L[ℝ] E) {N : Set (E × E)}
    (hN : N ∈ 𝓝 ((xbar, 0) : E × E))
    (hloc : ∀ q ∈ N, q ∈ gph G2 ↔ ((q.1 - c q.2, q.2) : E × E) ∈ gph G1)
    (h : MetricRegularAround G1 xbar 0) : MetricRegularAround G2 xbar 0 := by
  obtain ⟨μ, h0, hμ, U1, hU1, V1, hV1, hreg⟩ := h
  obtain ⟨δN, hδN, hballN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨δU, hδU, hballU⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨δV, hδV, hballV⟩ := Metric.mem_nhds_iff.1 hV1
  set δ := min δN (min δU δV) with hδdef
  have hδ : 0 < δ := lt_min hδN (lt_min hδU hδV)
  have hinN : ∀ x v : E, ‖x - xbar‖ < δ → ‖v‖ < δ → ((x, v) : E × E) ∈ N := by
    intro x v hx hv
    apply hballN
    rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
    exact max_lt (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hv (min_le_left _ _))
  have hinU : ∀ x : E, ‖x - xbar‖ < δ → x ∈ U1 := by
    intro x hx; apply hballU
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have hinV : ∀ v : E, ‖v‖ < δ → v ∈ V1 := by
    intro v hv; apply hballV
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_right _ _))
  set κ := ‖c‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  set M := 2 * μ + κ + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  set δ' := δ / (2 * M + 2) with hδ'
  have hδ'pos : 0 < δ' := div_pos hδ (by linarith)
  set ρ := δ' / (2 * (M + 2)) with hρ
  have hρpos : 0 < ρ := div_pos hδ'pos (by linarith)
  have hδ'δ : (2 * M + 2) * δ' = δ := by rw [hδ']; field_simp
  have hMρ : (M + 2) * ρ * 2 = δ' := by rw [hρ]; field_simp
  have hρδ' : ρ ≤ δ' / 2 := by nlinarith
  have hρδ : ρ < δ := by nlinarith
  have hδ'lt : δ' < δ := by nlinarith
  have hcb : ∀ v : E, ‖c v‖ ≤ κ * ‖v‖ := fun v => c.le_opNorm v
  -- membership of xbar
  have h0' : (0 : E) ∈ G2 xbar := by
    have hq := hloc (xbar, 0) (hinN xbar 0 (by simpa using hδ) (by simpa using hδ))
    have : ((xbar - c 0, 0) : E × E) ∈ gph G1 := by
      show (0 : E) ∈ G1 (xbar - c 0); simpa using h0
    exact hq.2 this
  -- points of G2⁻¹ y from points of G1⁻¹ y
  have hlift : ∀ y p' : E, y ∈ G1 p' → ‖p' + c y - xbar‖ < δ → ‖y‖ < δ → y ∈ G2 (p' + c y) := by
    intro y p' hp' h1 h2
    have hq := hloc (p' + c y, y) (hinN _ _ h1 h2)
    exact hq.2 (by show y ∈ G1 (p' + c y - c y); simpa using hp')
  have hnear : ∀ y : E, ‖y‖ < ρ → ∃ x'' : E, y ∈ G2 x'' ∧ ‖x'' - xbar‖ < (μ + κ) * ρ := by
    intro y hy
    obtain ⟨hne, hd⟩ := hreg xbar (mem_of_mem_nhds hU1) y (hinV y (by linarith)) 0 h0
    have hlt : Metric.infDist xbar {x' | y ∈ G1 x'} < μ * ρ := by
      calc _ ≤ μ * ‖y - 0‖ := hd
        _ < μ * ρ := by rw [sub_zero]; exact mul_lt_mul_of_pos_left hy hμ
    obtain ⟨p', hp', hdp⟩ := (Metric.infDist_lt_iff hne).1 hlt
    rw [dist_comm, dist_eq_norm] at hdp
    have hx'' : ‖p' + c y - xbar‖ < (μ + κ) * ρ := by
      calc ‖p' + c y - xbar‖ ≤ ‖p' - xbar‖ + ‖c y‖ := by
            rw [show p' + c y - xbar = (p' - xbar) + c y by abel]; exact norm_add_le _ _
        _ < μ * ρ + κ * ρ := by
            have := hcb y
            have : κ * ‖y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hy.le hκ0
            linarith
        _ = (μ + κ) * ρ := by ring
    refine ⟨p' + c y, hlift y p' hp' ?_ (by linarith), hx''⟩
    have : (μ + κ) * ρ ≤ δ := by nlinarith
    linarith
  refine ⟨M, h0', by linarith, Metric.ball xbar ρ, Metric.ball_mem_nhds _ hρpos,
    Metric.ball 0 ρ, Metric.ball_mem_nhds _ hρpos, fun x hx y hy w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
  obtain ⟨x'', hx''G, hx''n⟩ := hnear y hy
  refine ⟨⟨x'', hx''G⟩, ?_⟩
  by_cases hwδ : ‖w‖ < δ'
  · -- case A
    have hpG : w ∈ G1 (x - c w) := by
      have hq := hloc (x, w) (hinN x w (by linarith) (by linarith))
      exact hq.1 hw
    have hpU : x - c w ∈ U1 := hinU _ (by
      calc ‖x - c w - xbar‖ ≤ ‖x - xbar‖ + ‖c w‖ := by
            rw [show x - c w - xbar = (x - xbar) - c w by abel]; exact norm_sub_le _ _
        _ < δ := by
            have := hcb w
            have : κ * ‖w‖ ≤ κ * δ' := mul_le_mul_of_nonneg_left hwδ.le hκ0
            nlinarith)
    obtain ⟨hne1, hd1⟩ := hreg (x - c w) hpU y (hinV y (by linarith)) w hpG
    by_cases hyw : y = w
    · subst hyw
      have : Metric.infDist x {x' | y ∈ G2 x'} ≤ 0 := by
        have := Metric.infDist_le_dist_of_mem (x := x) (show x ∈ {x' | y ∈ G2 x'} from hw)
        simpa using this
      have : 0 ≤ M * ‖y - y‖ := by simp
      linarith
    · have hpos : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
      have hlt : Metric.infDist (x - c w) {x' | y ∈ G1 x'} < 2 * μ * ‖y - w‖ := by
        nlinarith
      obtain ⟨p', hp', hdp⟩ := (Metric.infDist_lt_iff hne1).1 hlt
      rw [dist_eq_norm] at hdp
      have hyw' : ‖y - w‖ < ρ + δ' := by
        calc ‖y - w‖ ≤ ‖y‖ + ‖w‖ := norm_sub_le _ _
          _ < ρ + δ' := by linarith
      have hx'n : ‖p' + c y - xbar‖ < δ := by
        have e : p' + c y - xbar = -((x - c w) - p') + (x - xbar) - c w + c y := by abel
        calc ‖p' + c y - xbar‖ ≤ ‖(x - c w) - p'‖ + ‖x - xbar‖ + ‖c w‖ + ‖c y‖ := by
              rw [e]
              calc ‖-((x - c w) - p') + (x - xbar) - c w + c y‖
                  ≤ ‖-((x - c w) - p') + (x - xbar) - c w‖ + ‖c y‖ := norm_add_le _ _
                _ ≤ ‖-((x - c w) - p') + (x - xbar)‖ + ‖c w‖ + ‖c y‖ := by
                    gcongr; exact norm_sub_le _ _
                _ ≤ ‖(x - c w) - p'‖ + ‖x - xbar‖ + ‖c w‖ + ‖c y‖ := by
                    gcongr; calc ‖-((x - c w) - p') + (x - xbar)‖
                        ≤ ‖-((x - c w) - p')‖ + ‖x - xbar‖ := norm_add_le _ _
                      _ = _ := by rw [norm_neg]
          _ < δ := by
              have h1 := hcb w
              have h2 := hcb y
              have h3 : κ * ‖w‖ ≤ κ * δ' := mul_le_mul_of_nonneg_left hwδ.le hκ0
              have h4 : κ * ‖y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hy.le hκ0
              have h5 : 2 * μ * ‖y - w‖ ≤ 2 * μ * (ρ + δ') :=
                mul_le_mul_of_nonneg_left hyw'.le (by linarith)
              nlinarith
      have hx'G : y ∈ G2 (p' + c y) := hlift y p' hp' hx'n (by linarith)
      calc Metric.infDist x {x' | y ∈ G2 x'} ≤ dist x (p' + c y) :=
            Metric.infDist_le_dist_of_mem hx'G
        _ = ‖((x - c w) - p') + c (w - y)‖ := by
            rw [dist_eq_norm, map_sub]; congr 1; abel
        _ ≤ ‖(x - c w) - p'‖ + ‖c (w - y)‖ := norm_add_le _ _
        _ ≤ 2 * μ * ‖y - w‖ + κ * ‖y - w‖ := by
            have := hcb (w - y)
            rw [norm_sub_rev w y] at this
            linarith
        _ ≤ M * ‖y - w‖ := by nlinarith
  · -- case B
    push_neg at hwδ
    have hyw : δ' / 2 ≤ ‖y - w‖ := by
      have : ‖w‖ - ‖y‖ ≤ ‖y - w‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le w y
      linarith
    calc Metric.infDist x {x' | y ∈ G2 x'} ≤ dist x x'' := Metric.infDist_le_dist_of_mem hx''G
      _ ≤ ‖x - xbar‖ + ‖x'' - xbar‖ := by
          rw [dist_eq_norm, show x - x'' = (x - xbar) - (x'' - xbar) by abel]; exact norm_sub_le _ _
      _ ≤ δ' / 2 := by nlinarith
      _ ≤ ‖y - w‖ := hyw
      _ ≤ M * ‖y - w‖ := by nlinarith [norm_nonneg (y - w)]

end GNC74

open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNCAux GNC73 GNC75 GNC74 in
theorem solution {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      (∃ U ∈ 𝓝 xbar, ∀ x ∈ U, fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
        DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
      (GenNewtonSubgrad.ProxReg.MetricRegularAround (NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g))
          xbar 0 ↔
        GenNewtonSubgrad.ProxReg.MetricRegularAround (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) xbar
          (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) xbar)) := by
  classical
  have hgrad : ∀ x, gradient (quadF A b α) x = A x + b := gradient_quadF A hA b α
  have hfd : ∀ x, fderiv ℝ (gradient (quadF A b α)) x = A := by
    intro x
    have : gradient (quadF A b α) = fun y => A y + b := funext hgrad
    rw [this]; exact (A.hasFDerivAt.add_const b).fderiv
  have hAs : ∀ h k, ⟪A h, k⟫_ℝ = ⟪h, A k⟫_ℝ := fun h k => by simpa using hA.isSymmetric h k
  set vbar := -(A xbar + b) with hvbar
  obtain ⟨γ2, hγ2, hγ2r, h72⟩ := proposition_7_2 (quadF A b α) g xbar r ε
    ⟨Set.univ, Filter.univ_mem, (contDiff_quadF A b α).contDiffOn⟩ hstat hg hpb
    (by rw [hgrad]; exact hpr)
  obtain ⟨l3, hl3, -, H3⟩ := lemma_6_3_iii g xbar vbar r ε hg hpb hpr
  refine ⟨min γ2 l3, lt_min hγ2 hl3, (min_le_left _ _).trans hγ2r, fun γ hγ hlt hB => ?_⟩
  have lt2 : γ < γ2 := lt_of_lt_of_le hlt (min_le_left _ _)
  have lt3 : γ < l3 := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨U2, hU2, P, hP, -, hfin2, hdiff2, -, hform, h75⟩ := h72 γ hγ lt2
  obtain ⟨W3, hW3, V3, hV3, hgr3, hres3⟩ := H3 γ hγ lt3
  refine ⟨⟨U2, hU2, fun x hx => ⟨(hfin2 x hx).1, (hfin2 x hx).2, hdiff2 x hx⟩⟩, ?_⟩
  -- the operator B and its inverse
  set B := shiftOp A γ with hBdef
  have hBapp : ∀ y, B y = y - γ • A y := by intro y; simp [hBdef, shiftOp]
  set Be := ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 hB.1)
    (LinearMap.range_eq_top.2 hB.2) with hBe
  set Binv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Be.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) with hBinv
  have hBBi : ∀ y, B (Binv y) = y := fun y =>
    ContinuousLinearEquiv.ofBijective_apply_symm_apply B _ _ y
  have hBiB : ∀ y, Binv (B y) = y := fun y =>
    ContinuousLinearEquiv.ofBijective_symm_apply_apply B _ _ y
  have hBs : ∀ h k, ⟪B h, k⟫_ℝ = ⟪h, B k⟫_ℝ := by
    intro h k
    rw [hBapp, hBapp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hAs]
    simp
  have hBis : ∀ h k, ⟪Binv h, k⟫_ℝ = ⟪h, Binv k⟫_ℝ := by
    intro h k
    conv_lhs => rw [← hBBi k]
    rw [← hBs, hBBi]
  -- envelope data
  set e : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (moreauEnv g γ z).toReal with hedef
  set ge := gradient e with hgedef
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => x - γ • (A x + b)
    with hTdef
  have hTx : T xbar = xbar + γ • vbar := by
    simp only [hTdef, hvbar, smul_neg, sub_eq_add_neg]
  have hTc : Continuous T := by simp only [hTdef]; fun_prop
  set U := interior (U2 ∩ T ⁻¹' W3) with hUdef
  have hUnhds : U ∈ 𝓝 xbar := by
    rw [hUdef, interior_mem_nhds]
    refine Filter.inter_mem hU2 (hTc.continuousAt.preimage_mem_nhds ?_)
    rw [hTx]; exact hW3
  have hUopen : IsOpen U := isOpen_interior
  have mU2 : ∀ y ∈ U, y ∈ U2 := fun y hy => (interior_subset hy).1
  have mW3 : ∀ y ∈ U, T y ∈ W3 := fun y hy => (interior_subset hy).2
  have hP' : ∀ y ∈ U2, prox g γ (y - γ • (A y + b)) = {P y} := by
    intro y hy; have := hP y hy; rwa [hgrad] at this
  have hPmem : ∀ y ∈ U2, P y ∈ prox g γ (T y) := by
    intro y hy; rw [hP' y hy]; exact Set.mem_singleton _
  have hge : ∀ y ∈ U, ge (T y) = γ⁻¹ • (T y - P y) := fun y hy =>
    ((hgr3 (T y) (mW3 y hy)).2 (P y) (hPmem y (mU2 y hy))).gradient
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (fbe (quadF A b α) g γ y).toReal with hψdef
  have hgψ : ∀ y ∈ U2, gradient ψ y = γ⁻¹ • B (y - P y) := by
    intro y hy
    rw [hform y hy, hfd, hBapp]
  have hψ0 : gradient ψ xbar = 0 :=
    (h75 xbar (mem_of_mem_nhds hU2) (by rw [hfd]; exact hB)).2 hstat
  -- the shear
  set Linv : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun q => (q.1 - γ • Binv q.2, q.2) with hLinvdef
  set S1 := gph (LimitingSubdiff (sumFn (quadF A b α) g)) with hS1
  set S2' := {q | Linv q ∈ S1} with hS2'
  set S2 := gph (sv (gradient ψ)) with hS2
  set Fm : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun q => (q.1, q.2 - (A (q.1 - γ • Binv q.2) + b)) with hFmdef
  have hFmc : Continuous Fm := by simp only [hFmdef]; fun_prop
  set N := interior (Fm ⁻¹' (U ×ˢ V3)) with hNdef
  have hNopen : IsOpen N := isOpen_interior
  have hzN : ((xbar, 0) : _ × _) ∈ N := by
    rw [hNdef, mem_interior_iff_mem_nhds]
    apply hFmc.continuousAt.preimage_mem_nhds
    have : Fm (xbar, 0) = (xbar, vbar) := by
      simp only [hFmdef, map_zero, smul_zero, sub_zero, hvbar, zero_sub]
    rw [this]
    exact prod_mem_nhds hUnhds hV3
  have hNmem : ∀ q ∈ N, q.1 ∈ U ∧ q.2 - (A (q.1 - γ • Binv q.2) + b) ∈ V3 := by
    intro q hq
    have h := interior_subset (s := Fm ⁻¹' (U ×ˢ V3)) hq
    exact ⟨h.1, h.2⟩
  have hshear : S2 ∩ N = S2' ∩ N := by
    ext q
    constructor
    · rintro ⟨hq, hqN⟩
      refine ⟨?_, hqN⟩
      obtain ⟨hxU, -⟩ := hNmem q hqN
      have hq2 : q.2 = gradient ψ q.1 := hq
      set x := q.1
      have hL1 : (Linv q).1 = P x := by
        simp only [hLinvdef, hq2]
        rw [hgψ x (mU2 x hxU), map_smul, hBiB, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]
        abel
      show (Linv q).2 ∈ LimitingSubdiff (sumFn (quadF A b α) g) (Linv q).1
      rw [hL1]
      show q.2 ∈ LimitingSubdiff (sumFn (quadF A b α) g) (P x)
      rw [limSubdiff_sum_iff A hA b α g]
      have hfer := prox_fermat g hg hγ _ (P x) (hPmem x (mU2 x hxU))
      have heq : q.2 - (A (P x) + b) = γ⁻¹ • (T x - P x) := by
        rw [hq2, hgψ x (mU2 x hxU), hBapp]
        simp only [hTdef]
        rw [show x - γ • (A x + b) - P x = (x - P x) - γ • (A x + b) by abel]
        simp only [smul_sub, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul, map_sub, smul_add]
        abel
      rw [heq]; exact hfer
    · rintro ⟨hq, hqN⟩
      refine ⟨?_, hqN⟩
      obtain ⟨hxU, hwV⟩ := hNmem q hqN
      set x := q.1
      set v := q.2
      have hq' : v ∈ LimitingSubdiff (sumFn (quadF A b α) g) (x - γ • Binv v) := hq
      rw [limSubdiff_sum_iff A hA b α g] at hq'
      set y := Binv v with hy
      have hvy : v = y - γ • A y := by rw [← hBapp, hy, hBBi]
      have hTw : T x - γ • (v - (A (x - γ • y) + b)) = x - γ • y := by
        simp only [hTdef]
        rw [hvy]
        simp only [smul_sub, smul_add, map_sub, map_smul, smul_smul]
        module
      have hmem : v - (A (x - γ • y) + b) ∈
          {w | w ∈ V3 ∧ w ∈ LimitingSubdiff g (T x - γ • w)} := by
        refine ⟨hwV, ?_⟩
        rw [hTw]; exact hq'
      rw [hres3 (T x) (mW3 x hxU)] at hmem
      have hw : v - (A (x - γ • y) + b) = γ⁻¹ • (T x - P x) := by
        rw [← hge x hxU]; exact hmem
      have hPx : P x = x - γ • y := by
        rw [← hTw, hw, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]; abel
      show v ∈ ({gradient ψ x} : Set _)
      rw [Set.mem_singleton_iff, hgψ x (mU2 x hxU), hPx]
      rw [show x - (x - γ • y) = γ • y by abel, map_smul, hy, hBBi, smul_smul,
        inv_mul_cancel₀ hγ.ne', one_smul]
  -- metric regularity transfer
  set c : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := γ • Binv with hc
  have hNn : N ∈ 𝓝 ((xbar, 0) : _ × _) := hNopen.mem_nhds hzN
  have hloc : ∀ q ∈ N, q ∈ S2 ↔ ((q.1 - c q.2, q.2) : _ × _) ∈ S1 := by
    intro q hq
    have h1 := Set.ext_iff.1 hshear q
    simp only [Set.mem_inter_iff] at h1
    constructor
    · intro hq2
      have := (h1.1 ⟨hq2, hq⟩).1
      exact this
    · intro hq1
      exact (h1.2 ⟨hq1, hq⟩).1
  set N' := (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    ((q.1 + c q.2, q.2) : _ × _)) ⁻¹' N with hN'
  have hN'n : N' ∈ 𝓝 ((xbar, 0) : _ × _) := by
    apply (show Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ((q.1 + c q.2, q.2) : _ × _)) by fun_prop).continuousAt.preimage_mem_nhds
    simpa using hNn
  have hloc' : ∀ q ∈ N', q ∈ S1 ↔ ((q.1 - (-c) q.2, q.2) : _ × _) ∈ S2 := by
    intro q hq
    have h := hloc _ hq
    simp only [add_sub_cancel_right] at h
    have e : q.1 - (-c) q.2 = q.1 + c q.2 := by
      rw [ContinuousLinearMap.neg_apply, sub_neg_eq_add]
    rw [e]
    exact h.symm
  rw [hψ0]
  exact ⟨MR_transfer _ _ xbar c hNn hloc, MR_transfer _ _ xbar (-c) hN'n hloc'⟩
