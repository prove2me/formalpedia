-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.proposition_7_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:00:49.387477+00:00
-- url     : https://prove2.me/submissions/86b56261-b0f9-4cc8-8d6e-744bbd39c96e

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_i
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_ii
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii

open Filter Topology
open scoped InnerProductSpace

namespace GNC72
open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

lemma tendsto_coe_add {u : ℕ → ℝ} {c : ℝ} {a : ℕ → EReal} {l : EReal}
    (hu : Tendsto u atTop (𝓝 c)) (ha : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun t => (u t : EReal) + a t) atTop (𝓝 ((c : EReal) + l)) :=
  ((EReal.continuousAt_add (p := ((c : EReal), l)) (Or.inl (EReal.coe_ne_top c))
    (Or.inl (EReal.coe_ne_bot c))).tendsto).comp
    (((continuous_coe_real_ereal.tendsto c).comp hu).prodMk_nhds ha)

lemma coe_add_iInf {ι : Sort*} (c : ℝ) (F : ι → EReal) :
    ⨅ i, ((c : EReal) + F i) = (c : EReal) + ⨅ i, F i := by
  apply le_antisymm
  · set m := ⨅ i, ((c : EReal) + F i)
    have h1 : ((-c : ℝ) : EReal) + m ≤ ⨅ i, F i := by
      refine le_iInf fun i => ?_
      have := add_le_add_right (iInf_le (fun i => (c : EReal) + F i) i) ((-c : ℝ) : EReal)
      rwa [ereal_neg_add_cancel] at this
    have h2 := add_le_add_right h1 (c : EReal)
    have e : (c : EReal) + (((-c : ℝ) : EReal) + m) = m := by
      have := ereal_neg_add_cancel (-c) m
      simpa using this
    rwa [e] at h2
  · exact le_iInf fun i => add_le_add_right (iInf_le F i) _

lemma ereal_four (a b c d : ℝ) (h : a + b = c + d) (e : EReal) :
    (a : EReal) + e + (b : EReal) = (c : EReal) + (e + (d : EReal)) := by
  induction e using EReal.rec
  · simp
  · rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]; congr 1; linarith
  · simp

lemma fbe_eq [CompleteSpace E] (f : E → ℝ) (g : E → EReal) {γ : ℝ} (hγ : 0 < γ) (x : E) :
    fbe f g γ x = ((f x - γ / 2 * ‖gradient f x‖ ^ 2 : ℝ) : EReal) +
      moreauEnv g γ (x - γ • gradient f x) := by
  unfold fbe moreauEnv
  rw [← coe_add_iInf]
  congr 1; funext y
  apply ereal_four
  have : y - (x - γ • gradient f x) = (y - x) + γ • gradient f x := by abel
  rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hγ,
    real_inner_comm]
  field_simp
  ring


lemma small_rem [CompleteSpace E] {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 y, |f z - f y - ⟪gradient f y, z - y⟫_ℝ| ≤ ε * ‖z - y‖ := by
  have h1 := hf.hasGradientAt.hasFDerivAt.isLittleO.def hε
  filter_upwards [h1] with z hz
  simpa [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs] using hz

lemma regSubgrad_add_iff [CompleteSpace E] (f : E → ℝ) (g : E → EReal) (y v : E)
    (hf : DifferentiableAt ℝ f y) :
    IsRegularSubgrad (sumFn f g) y v ↔ IsRegularSubgrad g y (v - gradient f y) := by
  have hfin : sumFn f g y ≠ ⊤ ↔ g y ≠ ⊤ := by
    unfold sumFn
    constructor
    · intro h hg; apply h; rw [hg]; simp
    · intro h; exact EReal.add_ne_top (EReal.coe_ne_top _) h
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨hfin.1 h0, fun ε hε => ?_⟩
    filter_upwards [h (ε/2) (by linarith), small_rem hf (by linarith : 0 < ε/2)] with z hz hq
    unfold sumFn at hz
    rw [ereal_rearr] at hz
    refine ereal_le_of_add_le ?_ hz
    rw [inner_sub_left]
    have := (abs_le.1 hq).2
    linarith
  · rintro ⟨h0, h⟩
    refine ⟨hfin.2 h0, fun ε hε => ?_⟩
    filter_upwards [h (ε/2) (by linarith), small_rem hf (by linarith : 0 < ε/2)] with z hz' hq
    unfold sumFn
    rw [ereal_rearr]
    refine ereal_le_of_add_le ?_ hz'
    rw [inner_sub_left]
    have := (abs_le.1 hq).1
    linarith

lemma limSubdiff_add_iff [CompleteSpace E] (f : E → ℝ) (g : E → EReal) {U : Set E} (hU : IsOpen U)
    (hd : ∀ y ∈ U, DifferentiableAt ℝ f y) (hc : ContinuousOn (gradient f) U) {x : E} (hx : x ∈ U)
    (v : E) :
    v ∈ LimitingSubdiff (sumFn f g) x ↔ v - gradient f x ∈ LimitingSubdiff g x := by
  have hfc : ContinuousAt f x := (hd x hx).continuousAt
  have hgc : ContinuousAt (gradient f) x := hc.continuousAt (hU.mem_nhds hx)
  have hfin : sumFn f g x ≠ ⊤ ↔ g x ≠ ⊤ := by
    unfold sumFn
    constructor
    · intro h hg; apply h; rw [hg]; simp
    · intro h; exact EReal.add_ne_top (EReal.coe_ne_top _) h
  have key : ∀ y, g y = ((-(f y) : ℝ) : EReal) + sumFn f g y := by
    intro y; unfold sumFn; rw [ereal_neg_add_cancel]
  constructor
  · rintro ⟨h0, xs, vs, hxs, hφ, hvs, hreg⟩
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hxs.eventually (hU.mem_nhds hx))
    have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
    refine ⟨hfin.1 h0, fun t => xs (t + K), fun t => vs (t + K) - gradient f (xs (t + K)),
      hxs.comp hsh, ?_, (hvs.comp hsh).sub (hgc.tendsto.comp (hxs.comp hsh)), fun t => ?_⟩
    · simp_rw [key]
      exact tendsto_coe_add (hfc.tendsto.comp (hxs.comp hsh)).neg (hφ.comp hsh)
    · exact (regSubgrad_add_iff f g _ _ (hd _ (hK _ (Nat.le_add_left K t)))).1 (hreg _)
  · rintro ⟨h0, xs, ws, hxs, hg, hws, hreg⟩
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hxs.eventually (hU.mem_nhds hx))
    have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
    refine ⟨hfin.2 h0, fun t => xs (t + K), fun t => ws (t + K) + gradient f (xs (t + K)),
      hxs.comp hsh, ?_, ?_, fun t => ?_⟩
    · unfold sumFn
      exact tendsto_coe_add (hfc.tendsto.comp (hxs.comp hsh)) (hg.comp hsh)
    · have := (hws.comp hsh).add (hgc.tendsto.comp (hxs.comp hsh))
      simpa using this
    · rw [regSubgrad_add_iff f g _ _ (hd _ (hK _ (Nat.le_add_left K t)))]
      simpa using hreg (t + K)


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


lemma smooth_facts [CompleteSpace E] (f : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hC2 : ContDiffOn ℝ 2 f O) :
    (∀ y ∈ O, DifferentiableAt ℝ f y) ∧ ContDiffOn ℝ 1 (gradient f) O ∧
      (∀ y ∈ O, ∀ h k : E, ⟪fderiv ℝ (gradient f) y h, k⟫_ℝ = ⟪h, fderiv ℝ (gradient f) y k⟫_ℝ) := by
  have hd : ∀ y ∈ O, DifferentiableAt ℝ f y := fun y hy =>
    (hC2.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num)
  have hfd1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) O := hC2.fderiv_of_isOpen hO (by norm_num)
  let Lin : (E →L[ℝ] ℝ) →ₗ[ℝ] E :=
    { toFun := fun φ => (InnerProductSpace.toDual ℝ E).symm φ
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  set L : (E →L[ℝ] ℝ) →L[ℝ] E :=
    ⟨Lin, (InnerProductSpace.toDual ℝ E).symm.continuous⟩ with hL
  have hgeq : gradient f = fun y => L (fderiv ℝ f y) := by
    funext y; rfl
  have hg1 : ContDiffOn ℝ 1 (gradient f) O := by
    rw [hgeq]; exact L.contDiff.comp_contDiffOn hfd1
  refine ⟨hd, hg1, fun y hy h k => ?_⟩
  have hsymm : IsSymmSndFDerivAt ℝ f y :=
    (hC2.contDiffAt (hO.mem_nhds hy)).isSymmSndFDerivAt (by simp)
  have hdf : DifferentiableAt ℝ (fun y => fderiv ℝ f y) y :=
    (hfd1.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num)
  have hfd : fderiv ℝ (gradient f) y = L.comp (fderiv ℝ (fun y => fderiv ℝ f y) y) := by
    rw [hgeq]; exact (L.hasFDerivAt.comp y hdf.hasFDerivAt).fderiv
  have key : ∀ a b : E, ⟪fderiv ℝ (gradient f) y a, b⟫_ℝ = fderiv ℝ (fderiv ℝ f) y a b := by
    intro a b
    rw [hfd]
    show ⟪(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => fderiv ℝ f y) y a), b⟫_ℝ = _
    rw [InnerProductSpace.toDual_symm_apply]
  rw [key, real_inner_comm, key, hsymm h k]


lemma grad_formula [CompleteSpace E] (f e : E → ℝ) {γ : ℝ} (hγ : γ ≠ 0) (y q : E)
    {H : E →L[ℝ] E} (hf : DifferentiableAt ℝ f y) (hgf : HasFDerivAt (gradient f) H y)
    (hsym : ∀ h k : E, ⟪H h, k⟫_ℝ = ⟪h, H k⟫_ℝ)
    (he : HasGradientAt e (γ⁻¹ • ((y - γ • gradient f y) - q)) (y - γ • gradient f y)) :
    HasGradientAt (fun z => f z - γ / 2 * ‖gradient f z‖ ^ 2 + e (z - γ • gradient f z))
      (γ⁻¹ • ((y - q) - γ • H (y - q))) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := hf.hasGradientAt.hasFDerivAt
  have h2 := hgf.norm_sq
  have hT : HasFDerivAt (fun z => z - γ • gradient f z) (ContinuousLinearMap.id ℝ E - γ • H) y :=
    (hasFDerivAt_id y).sub (hgf.const_smul γ)
  have h3 := he.hasFDerivAt.comp y hT
  have htot := (h1.sub (h2.const_mul (γ / 2))).add h3
  refine htot.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Function.comp_def]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [hsym (y - q) h]
  simp only [inner_sub_left, real_inner_comm (gradient f y) (H h)]
  field_simp
  ring

end GNC72

open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC72 in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal) (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hf : ∃ U₀ ∈ 𝓝 xbar, ContDiffOn ℝ 2 f U₀)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn f g) xbar)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(gradient f xbar)) r ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      ∃ U ∈ 𝓝 xbar, ∃ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        (∀ x ∈ U, GenNewtonSubgrad.ProxReg.prox g γ (x - γ • gradient f x) = {P x}) ∧
        (∃ L, LipschitzOnWith L P U) ∧
        (∀ x ∈ U, fbe f g γ x ≠ ⊤ ∧ fbe f g γ x ≠ ⊥) ∧
        (∀ x ∈ U, DifferentiableAt ℝ (fun z => (fbe f g γ z).toReal) x) ∧
        ContinuousOn (gradient (fun z => (fbe f g γ z).toReal)) U ∧
        (∀ x ∈ U, gradient (fun z => (fbe f g γ z).toReal) x =
          γ⁻¹ • ((x - P x) - γ • fderiv ℝ (gradient f) x (x - P x))) ∧
        (∀ x ∈ U, Function.Bijective
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - γ • fderiv ℝ (gradient f) x) →
          (gradient (fun z => (fbe f g γ z).toReal) x = 0 ↔
            0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn f g) x)) := by
  classical
  obtain ⟨U₀, hU₀, hC2⟩ := hf
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.1 hU₀
  obtain ⟨hdO, hg1, hsymO⟩ := smooth_facts f hOopen (hC2.mono hOsub)
  have hgc : ContinuousOn (gradient f) O := hg1.continuousOn
  have hHc : ContinuousOn (fun y => fderiv ℝ (gradient f) y) O :=
    hg1.continuousOn_fderiv_of_isOpen hOopen le_rfl
  have hgd : ∀ y ∈ O, DifferentiableAt ℝ (gradient f) y := fun y hy =>
    (hg1.contDiffAt (hOopen.mem_nhds hy)).differentiableAt one_ne_zero
  obtain ⟨K, t, ht, hK⟩ := (hg1.contDiffAt (hOopen.mem_nhds hxO)).exists_lipschitzOnWith
  set vbar := -(gradient f xbar) with hvbar
  obtain ⟨l1, hl1, hl1r, H1⟩ := lemma_6_3_i g xbar vbar r ε hg hpb hpr
  obtain ⟨l2, hl2, -, H2⟩ := lemma_6_3_ii g xbar vbar r ε hg hpb hpr
  obtain ⟨l3, hl3, -, H3⟩ := lemma_6_3_iii g xbar vbar r ε hg hpb hpr
  refine ⟨min l1 (min l2 l3), lt_min hl1 (lt_min hl2 hl3), (min_le_left _ _).trans hl1r,
    fun γ hγ hlt => ?_⟩
  have lt1 : γ < l1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have lt2 : γ < l2 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have lt3 : γ < l3 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨W1, hW1, -, hfin1, -, -⟩ := H1 γ hγ lt1
  obtain ⟨W2, hW2, p, hp, -, ⟨Lp, hLp⟩, -⟩ := H2 γ hγ lt2
  obtain ⟨W3, hW3, V3, hV3, hgr3, hres3⟩ := H3 γ hγ lt3
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => y - γ • gradient f y with hTdef
  have hTx : T xbar = xbar + γ • vbar := by
    simp only [hTdef, hvbar, smul_neg, sub_eq_add_neg]
  have hgcx : ContinuousAt (gradient f) xbar := hgc.continuousAt (hOopen.mem_nhds hxO)
  have hTc : ContinuousAt T xbar := continuousAt_id.sub (hgcx.const_smul γ)
  have hW : W1 ∩ W2 ∩ W3 ∈ 𝓝 (T xbar) := by
    rw [hTx]; exact Filter.inter_mem (Filter.inter_mem hW1 hW2) hW3
  have hnc : ContinuousAt (fun y => -(gradient f y)) xbar := hgcx.neg
  set Uset := O ∩ t ∩ (T ⁻¹' (W1 ∩ W2 ∩ W3) ∩ (fun y => -(gradient f y)) ⁻¹' V3) with hUsetdef
  have hUset : Uset ∈ 𝓝 xbar :=
    Filter.inter_mem (Filter.inter_mem (hOopen.mem_nhds hxO) ht)
      (Filter.inter_mem (hTc.preimage_mem_nhds hW) (hnc.preimage_mem_nhds hV3))
  set U := interior Uset with hUdef
  have hUopen : IsOpen U := isOpen_interior
  have hUsub : U ⊆ Uset := interior_subset
  have mO : ∀ y ∈ U, y ∈ O := fun y hy => (hUsub hy).1.1
  have mt : ∀ y ∈ U, y ∈ t := fun y hy => (hUsub hy).1.2
  have mW1 : ∀ y ∈ U, T y ∈ W1 := fun y hy => (hUsub hy).2.1.1.1
  have mW2 : ∀ y ∈ U, T y ∈ W2 := fun y hy => (hUsub hy).2.1.1.2
  have mW3 : ∀ y ∈ U, T y ∈ W3 := fun y hy => (hUsub hy).2.1.2
  have mV3 : ∀ y ∈ U, -(gradient f y) ∈ V3 := fun y hy => (hUsub hy).2.2
  set P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => p (T y) with hPdef
  have hPprox : ∀ y ∈ U, prox g γ (y - γ • gradient f y) = {P y} := fun y hy =>
    hp (T y) (mW2 y hy)
  have hPmem : ∀ y ∈ U, P y ∈ prox g γ (T y) := fun y hy => by
    rw [hp (T y) (mW2 y hy)]; exact Set.mem_singleton _
  have hTL : LipschitzOnWith (1 + ‖γ‖₊ * K) T t := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have hab := hK.dist_le_mul a ha b hb
    rw [dist_eq_norm, dist_eq_norm] at hab
    rw [dist_eq_norm, dist_eq_norm]
    have e : T a - T b = (a - b) - γ • (gradient f a - gradient f b) := by
      simp only [hTdef]; rw [smul_sub]; abel
    rw [e]
    calc ‖(a - b) - γ • (gradient f a - gradient f b)‖
        ≤ ‖a - b‖ + ‖γ • (gradient f a - gradient f b)‖ := norm_sub_le _ _
      _ = ‖a - b‖ + |γ| * ‖gradient f a - gradient f b‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖a - b‖ + |γ| * (K * ‖a - b‖) := by gcongr
      _ = ((1 + ‖γ‖₊ * K : NNReal) : ℝ) * ‖a - b‖ := by
        push_cast; rw [Real.norm_eq_abs]; ring
  have hPL : LipschitzOnWith (Lp * (1 + ‖γ‖₊ * K)) P U :=
    hLp.comp (hTL.mono (fun y hy => mt y hy)) (fun y hy => mW2 y hy)
  set e : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (moreauEnv g γ z).toReal with hedef
  have hfbe : ∀ y ∈ U, fbe f g γ y =
      ((f y - γ / 2 * ‖gradient f y‖ ^ 2 + e (T y) : ℝ) : EReal) := by
    intro y hy
    rw [fbe_eq f g hγ y]
    obtain ⟨h1, h2⟩ := hfin1 (T y) (mW1 y hy)
    have : moreauEnv g γ (y - γ • gradient f y) = ((e (T y) : ℝ) : EReal) :=
      (EReal.coe_toReal h1 h2).symm
    rw [this, ← EReal.coe_add]
  set ψt : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => f z - γ / 2 * ‖gradient f z‖ ^ 2 + e (z - γ • gradient f z) with hψt
  have hψev : ∀ y ∈ U, (fun z => (fbe f g γ z).toReal) =ᶠ[𝓝 y] ψt := by
    intro y hy
    filter_upwards [hUopen.mem_nhds hy] with z hz
    rw [hfbe z hz, EReal.toReal_coe]
  have hgradψ : ∀ y ∈ U, HasGradientAt (fun z => (fbe f g γ z).toReal)
      (γ⁻¹ • ((y - P y) - γ • fderiv ℝ (gradient f) y (y - P y))) y := by
    intro y hy
    have he : HasGradientAt e (γ⁻¹ • ((y - γ • gradient f y) - P y)) (y - γ • gradient f y) :=
      (hgr3 (T y) (mW3 y hy)).2 (P y) (hPmem y hy)
    exact (grad_formula f e hγ.ne' y (P y) (hdO y (mO y hy)) (hgd y (mO y hy)).hasFDerivAt
      (hsymO y (mO y hy)) he).congr_of_eventuallyEq (hψev y hy)
  have hgradeq : ∀ y ∈ U, gradient (fun z => (fbe f g γ z).toReal) y =
      γ⁻¹ • ((y - P y) - γ • fderiv ℝ (gradient f) y (y - P y)) := fun y hy =>
    (hgradψ y hy).gradient
  refine ⟨U, interior_mem_nhds.2 hUset, P, hPprox, ⟨_, hPL⟩, fun y hy => ?_,
    fun y hy => (hgradψ y hy).differentiableAt, ?_, hgradeq, fun y hy hB => ?_⟩
  · rw [hfbe y hy]; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · have hc : ContinuousOn (fun y => γ⁻¹ • ((y - P y) - γ • fderiv ℝ (gradient f) y (y - P y))) U := by
      have hP : ContinuousOn P U := hPL.continuousOn
      have h1 : ContinuousOn (fun y => y - P y) U := continuousOn_id.sub hP
      exact (continuousOn_const (c := γ⁻¹)).smul (h1.sub ((continuousOn_const (c := γ)).smul ((hHc.mono (fun y hy => mO y hy)).clm_apply h1)))
    exact hc.congr (fun y hy => hgradeq y hy)
  · -- (7.5)
    have hsum := limSubdiff_add_iff f g hOopen hdO hgc (mO y hy) 0
    rw [hgradeq y hy, hsum, zero_sub]
    constructor
    · intro h0
      have hB0 : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - γ • fderiv ℝ (gradient f) y) (y - P y) = 0 := by
        rcases smul_eq_zero.1 h0 with h | h
        · exact absurd h (inv_ne_zero hγ.ne')
        · simpa using h
      have hyP : y - P y = 0 := hB.1 (by rw [hB0, map_zero])
      have hPy : P y = y := (sub_eq_zero.1 hyP).symm
      have hfer := prox_fermat g hg hγ (T y) (P y) (hPmem y hy)
      rw [hPy] at hfer
      have : γ⁻¹ • (T y - y) = -gradient f y := by
        simp only [hTdef, sub_sub_cancel_left, smul_neg, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
      rwa [this] at hfer
    · intro h0
      have hmem : -gradient f y ∈ {v | v ∈ V3 ∧ v ∈ LimitingSubdiff g (T y - γ • v)} := by
        refine ⟨mV3 y hy, ?_⟩
        have : T y - γ • -gradient f y = y := by simp [hTdef]
        rw [this]; exact h0
      rw [hres3 (T y) (mW3 y hy)] at hmem
      have hge : gradient e (T y) = γ⁻¹ • (T y - P y) :=
        ((hgr3 (T y) (mW3 y hy)).2 (P y) (hPmem y hy)).gradient
      have h1 : -gradient f y = γ⁻¹ • (T y - P y) := by rw [← hge]; exact hmem
      have h2 : γ⁻¹ • (y - P y) = 0 := by
        have : γ⁻¹ • (T y - P y) = γ⁻¹ • (y - P y) - gradient f y := by
          simp only [hTdef]
          rw [show y - γ • gradient f y - P y = (y - P y) - γ • gradient f y by abel, smul_sub,
            smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
        rw [this] at h1
        have := congrArg (· + gradient f y) h1
        simpa using this.symm
      have hyP : y - P y = 0 := by
        rcases smul_eq_zero.1 h2 with h | h
        · exact absurd h (inv_ne_zero hγ.ne')
        · exact h
      rw [hyP]; simp
