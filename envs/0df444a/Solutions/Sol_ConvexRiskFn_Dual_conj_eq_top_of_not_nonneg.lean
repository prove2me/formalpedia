-- Prove2me | solution 1 for ConvexRiskFn.Dual.conj_eq_top_of_not_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:33:13.823113+00:00
-- url     : https://prove2.me/submissions/a035f449-8d01-4f42-9b57-2918cf117e8e

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
    (S : PairedSpaces Ω E) (hC : CondC S) (ρ : E → EReal)
    (hp : IsProper ρ) (hA2 : A2 S ρ) (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y)
    (hneg : ¬ (0≤μ)) : conj S ρ μ=⊤ := by
  obtain ⟨X,hX⟩ := hp.2
  obtain ⟨Z,hZ,hn⟩ := hC μ hμ hneg
  let l := RiskDual.pairingLinear S μ hμ
  have hnL : l Z<0 := hn
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X := EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro b
  let k := l X-(ρ X).toReal
  let t := max 0 ((b+1-k)/(-l Z))
  have ht : 0≤t := le_max_left _ _
  have hb : b+1≤k-t*l Z := by
    have h := (div_le_iff₀ (neg_pos.mpr hnL)).mp (le_max_right 0 ((b+1-k)/(-l Z)))
    change b+1-k≤t*(-l Z) at h
    nlinarith
  have hm : ρ (X-t•Z)≤ρ X := by
    apply hA2
    intro ω
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    exact sub_le_self _ (mul_nonneg ht (hZ ω))
  have heT : (((ρ (X-t•Z)).toReal:ℝ):EReal)=ρ (X-t•Z) :=
    EReal.coe_toReal (ne_of_lt (hm.trans_lt hX)) (ne_of_gt (hp.1 _))
  have hr : (ρ (X-t•Z)).toReal≤(ρ X).toReal := by
    rw [← he,← heT,EReal.coe_le_coe_iff] at hm
    exact hm
  have hterm : ((k-t*l Z:ℝ):EReal) ≤
      ((pair μ (S.toFun (X-t•Z)):ℝ):EReal)-ρ (X-t•Z) := by
    rw [← heT,← EReal.coe_sub,EReal.coe_le_coe_iff]
    change k-t*l Z≤l (X-t•Z)-(ρ (X-t•Z)).toReal
    rw [map_sub,map_smul,smul_eq_mul]
    dsimp [k]
    linarith
  have hle : ((b+1:ℝ):EReal)≤conj S ρ μ :=
    (EReal.coe_le_coe_iff.mpr hb).trans (hterm.trans
      (le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (X-t•Z)))
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(i), p. 436: under condition (C), if a proper `ρ` satisfies (A2), then
`ρ*(μ) = +∞` for every `μ ∈ 𝒴` that is not nonnegative. -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) (ρ : 𝒳 → EReal)
    (hp : IsProper ρ) (hA2 : A2 S ρ) (μ : MeasureTheory.SignedMeasure Ω) (hμ : μ ∈ S.Y)
    (hneg : ¬ (0 ≤ μ)) :
    conj S ρ μ = ⊤ := by
  exact solution S hC ρ hp hA2 μ hμ hneg
end ConvexRiskFn.Dual

#print axioms solution
