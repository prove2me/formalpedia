-- Prove2me | solution 1 for ConvexRiskFn.Dual.conj_indicator_of_A4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:36:37.659477+00:00
-- url     : https://prove2.me/submissions/1c09e850-b87e-485a-b2d8-c2e485db0ea7

import Definitions.Def_ConvexRiskFn_Dual_Setting
set_option autoImplicit false
open MeasureTheory ConvexRiskFn.Dual Filter Topology
namespace RiskDual

theorem integrable_pos {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f : Ω → ℝ) (hf : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.posPart := by
  apply hf.mono_measure
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_right le_rfl

theorem integrable_neg {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f : Ω → ℝ) (hf : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.negPart := by
  apply hf.mono_measure
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_left le_rfl

theorem pair_add {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f g : Ω → ℝ) (hf : Integrable f μ.totalVariation) (hg : Integrable g μ.totalVariation) :
    pair μ (f+g)=pair μ f+pair μ g := by
  unfold pair
  simp only [Pi.add_apply]
  rw [integral_add (integrable_pos μ f hf) (integrable_pos μ g hg),
    integral_add (integrable_neg μ f hf) (integrable_neg μ g hg)]
  ring

theorem pair_smul {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (a : ℝ) (f : Ω → ℝ) : pair μ (a•f)=a*pair μ f := by
  unfold pair
  simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul]
  ring

theorem pair_const {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω) (a : ℝ) :
    pair μ (fun _ => a)=a*μ Set.univ := by
  unfold pair
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real μ MeasurableSet.univ]
  simp only [integral_const,smul_eq_mul,MeasureTheory.measureReal_def]
  ring

noncomputable def pairingLinear {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (S : PairedSpaces Ω E) (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y) : E →ₗ[ℝ] ℝ where
  toFun X := pair μ (S.toFun X)
  map_add' X Y := by
    rw [map_add,pair_add μ _ _ (S.integrable μ hμ X) (S.integrable μ hμ Y)]
  map_smul' a X := by
    rw [map_smul,pair_smul,smul_eq_mul]
    rfl

end RiskDual
#print axioms RiskDual.pairingLinear

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (ρ : E → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (_hcvx : A1 ρ) (hA4 : A4 ρ) :
    ∀ μ ∈ S.Y,
      ((∀ X, ((pair μ (S.toFun X):ℝ):EReal)≤ρ X) → conj S ρ μ=0) ∧
      ((¬ ∀ X, ((pair μ (S.toFun X):ℝ):EReal)≤ρ X) → conj S ρ μ=⊤) := by
  have hzero : ρ 0=0 := by
    obtain ⟨X,hX⟩ := hp.2
    have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
      EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
    have hc : ContinuousAt (fun t:ℝ => t•X) 0 := by fun_prop
    have hsc : LowerSemicontinuousAt (fun t:ℝ => ρ (t•X)) 0 := by
      have h : LowerSemicontinuousAt ρ ((fun t:ℝ => t•X) 0) := by simpa using hlsc (0:E)
      exact h.comp (g:=fun t:ℝ => t•X) hc
    have hreal : Tendsto (fun t:ℝ => t*(ρ X).toReal) (𝓝[>] 0) (𝓝 (0*(ρ X).toReal)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
    have hco : Tendsto (fun t:ℝ => ((t*(ρ X).toReal:ℝ):EReal)) (𝓝[>] 0) (𝓝 (0:EReal)) := by
      simpa only [Function.comp_def,zero_mul,EReal.coe_zero] using
        (continuous_coe_real_ereal.tendsto _).comp hreal
    have hlim : Tendsto (fun t:ℝ => ρ (t•X)) (𝓝[>] 0) (𝓝 (0:EReal)) := by
      apply hco.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hA4 t X ht,← he,← EReal.coe_mul]
      simp only [EReal.toReal_coe]
    have hle : ρ (0:E)≤0 := by
      have h := (hsc.lowerSemicontinuousWithinAt (Set.Ioi (0:ℝ))).le_liminf
      simpa [hlim.liminf_eq] using h
    have he0 : (((ρ (0:E)).toReal:ℝ):EReal)=ρ 0 :=
      EReal.coe_toReal (ne_of_lt (hle.trans_lt (by simp))) (ne_of_gt (hp.1 0))
    have h := hA4 2 (0:E) (by norm_num)
    rw [smul_zero,← he0,← EReal.coe_mul,EReal.coe_eq_coe_iff] at h
    have hr : (ρ (0:E)).toReal=0 := by linarith
    rw [← he0,hr,EReal.coe_zero]
  intro μ hμ
  let l := RiskDual.pairingLinear S μ hμ
  constructor
  · intro hdom
    apply le_antisymm
    · apply iSup_le
      intro X
      exact EReal.sub_nonpos.mpr (hdom X)
    · have h : ((pair μ (S.toFun (0:E)):ℝ):EReal)-ρ (0:E)≤conj S ρ μ :=
        le_iSup (fun X:E => ((pair μ (S.toFun X):ℝ):EReal)-ρ X) (0:E)
      have hpzero : pair μ (S.toFun (0:E))=0 := by simp [pair]
      simpa only [hpzero,hzero,EReal.coe_zero,sub_zero] using h
  · intro hbad
    push Not at hbad
    obtain ⟨X,hX⟩ := hbad
    have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
      EReal.coe_toReal (ne_of_lt (hX.trans (EReal.coe_lt_top _))) (ne_of_gt (hp.1 X))
    have hd : 0<l X-(ρ X).toReal := by
      rw [← he,EReal.coe_lt_coe_iff] at hX
      exact sub_pos.mpr hX
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro b
    let t := max 1 ((b+1)/(l X-(ρ X).toReal))
    have ht : 0<t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
    have hb : b+1≤t*(l X-(ρ X).toReal) :=
      (div_le_iff₀ hd).mp (le_max_right 1 _)
    have hterm : ((pair μ (S.toFun (t•X)):ℝ):EReal)-ρ (t•X)=
        ((t*(l X-(ρ X).toReal):ℝ):EReal) := by
      rw [hA4 t X ht,← he,← EReal.coe_mul,← EReal.coe_sub]
      congr 1
      change l (t•X)-t*(ρ X).toReal=t*(l X-(ρ X).toReal)
      rw [map_smul,smul_eq_mul]
      ring
    have hle : ((b+1:ℝ):EReal)≤conj S ρ μ :=
      (EReal.coe_le_coe_iff.mpr hb).trans (hterm.symm.le.trans
        (le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (t•X)))
    exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(iii), p. 436: if a proper, lower semicontinuous, convex `ρ` is positively
homogeneous, then its conjugate is the indicator function of the set
`{μ ∈ 𝒴 : ⟨μ, X⟩ ≤ ρ(X) ∀ X ∈ 𝒳}` (value `0` on it, `+∞` off it). -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) (hA4 : A4 ρ) :
    ∀ μ ∈ S.Y,
      ((∀ X, ((pair μ (S.toFun X) : ℝ) : EReal) ≤ ρ X) → conj S ρ μ = 0) ∧
      ((¬ ∀ X, ((pair μ (S.toFun X) : ℝ) : EReal) ≤ ρ X) → conj S ρ μ = ⊤) := by
  exact solution S ρ hp hlsc hcvx hA4
end ConvexRiskFn.Dual

#print axioms solution
