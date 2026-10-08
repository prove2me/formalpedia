-- Prove2me | solution 1 for ConvexRiskFn.Dual.conj_eq_top_of_mass_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:34:08.639424+00:00
-- url     : https://prove2.me/submissions/3d5b22ac-30f9-45ba-a114-0da817559f9b

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
    (S : PairedSpaces Ω E) (one : E) (hone : S.toFun one=fun _ => 1)
    (ρ : E → EReal) (hp : IsProper ρ) (hA3 : A3 one ρ)
    (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y) (hmass : μ Set.univ ≠ 1) :
    conj S ρ μ=⊤ := by
  obtain ⟨X,hX⟩ := hp.2
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X := EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  let l := RiskDual.pairingLinear S μ hμ
  have honeL : l one=μ Set.univ := by
    change pair μ (S.toFun one)=μ Set.univ
    rw [hone]
    simpa using RiskDual.pair_const μ 1
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro b
  let k : ℝ := l X-(ρ X).toReal
  let a : ℝ := (b+1-k)/(μ Set.univ-1)
  have hv : ρ (X+a•one)=(((ρ X).toReal+a:ℝ):EReal) := by
    rw [hA3,← he,← EReal.coe_add]
    simp only [EReal.toReal_coe]
  have hterm : ((pair μ (S.toFun (X+a•one)):ℝ):EReal)-ρ (X+a•one)=
      ((k+a*(μ Set.univ-1):ℝ):EReal) := by
    rw [hv,← EReal.coe_sub]
    congr 1
    change l (X+a•one)-((ρ X).toReal+a)=k+a*(μ Set.univ-1)
    rw [map_add,map_smul,honeL,smul_eq_mul]
    dsimp [k]
    ring
  have ha : k+a*(μ Set.univ-1)=b+1 := by
    dsimp [a]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hmass)]
    ring
  have hle : ((b+1:ℝ):EReal)≤conj S ρ μ := by
    rw [← ha,← hterm]
    exact le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (X+a•one)
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(ii), p. 436: if `𝒳` contains the constant function `1` and a proper `ρ`
satisfies (A3), then `ρ*(μ) = +∞` for every `μ ∈ 𝒴` with `μ(Ω) ≠ 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (one : 𝒳)
    (hone : S.toFun one = fun _ => 1) (ρ : 𝒳 → EReal) (hp : IsProper ρ) (hA3 : A3 one ρ)
    (μ : MeasureTheory.SignedMeasure Ω) (hμ : μ ∈ S.Y) (hmass : μ Set.univ ≠ 1) :
    conj S ρ μ = ⊤ := by
  exact solution S one hone ρ hp hA3 μ hμ hmass
end ConvexRiskFn.Dual

#print axioms solution
