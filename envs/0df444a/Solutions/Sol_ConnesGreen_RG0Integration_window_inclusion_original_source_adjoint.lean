-- Prove2me | solution 1 for ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:57:39.991007+00:00
-- url     : https://prove2.me/submissions/3b54d8c3-e191-4441-a818-82c62d906b37

import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
import Definitions.Def_ConnesGreen_RG0_source_constructors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace ConnesGreen.RG0Integration
private theorem sourceLift_inner (t : ℝ) (f : WindowL2 t) (h : Physical t) :
    ⟪sourceLift t f, h⟫_ℂ = (2 : ℂ) * ⟪f, (h : Ambient t) 1⟫_ℂ := by
  rw [sourceLift, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp [sourceLoad, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_left,
    map_ofNat]
/-- All continuous native sources and columns are valid L2 inputs on a finite
window, so the total extension used in the model is never invoked there. -/
private theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc
private theorem actual_source_memLp (t : ℝ) (ρ : CriticalZeros) :
    MemLp (actualGreenSource ρ) 2 (windowMeasure t) := by
  apply continuous_window_memLp
  unfold actualGreenSource realExpMode
  fun_prop
private theorem supported_energy_mem (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    energyVector t g ∈ energySubspace t := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨⟨g, hg⟩, rfl⟩
private theorem windowL2_inner (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]
private theorem sourceEmbed_L (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    sourceEmbed t (problemOneL g) =
      (⟨energyVector t g, supported_energy_mem t g hg⟩ : Physical t) := by
  apply Subtype.ext
  exact sourceEmbed_L_energyVector t ht g hg

private theorem source_pairing_global (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (ρ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ =
      ∫ x : ℝ, star (actualGreenSource ρ x) * g x := by
  rw [sourceEmbed_L t ht g hg]
  change ⟪sourceLift t (windowL2 t (actualGreenSource ρ)),
    (⟨energyVector t g, supported_energy_mem t g hg⟩ : Physical t)⟫_ℂ = _
  rw [sourceLift_inner]
  have he : (energyVector t g) 1 = (1 / 2 : ℂ) • windowL2 t g := by simp [energyVector]
  rw [he, inner_smul_right]
  have hm : (2 : ℂ) * ((1 / 2 : ℂ) *
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ) =
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ := by ring
  rw [hm, windowL2_inner t _ _ (actual_source_memLp t ρ)
    (continuous_window_memLp t g hg.1.1.continuous)]
  unfold windowMeasure
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have h0 : g x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hx ((hg.2.trans Ioo_subset_Icc_self) h))
  simp [h0]

private theorem supportedTest_mono {t T : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (h : t ≤ T) : SupportedTest T g := by
  exact ⟨hg.1, hg.2.trans (Ioo_subset_Ioo (by linarith) h)⟩

private def testVectorFamily (t : ℝ) : {g : ℝ → ℂ // SupportedTest t g} → Physical t :=
  fun g => sourceEmbed t (problemOneL g.1)

private theorem testVectorFamily_linearCombination_dense (t : ℝ) (ht : 0 < t) :
    DenseRange (Finsupp.linearCombination ℂ (testVectorFamily t)) := by
  let R := LinearMap.range (Finsupp.linearCombination ℂ (testVectorFamily t))
  have hr : DenseRange (Finsupp.linearCombination ℂ (testVectorFamily t)) ↔
      R.topologicalClosure = ⊤ := by
    change Dense (Set.range (Finsupp.linearCombination ℂ (testVectorFamily t))) ↔ _
    rw [dense_iff_closure_eq]
    change closure (↑R : Set (Physical t)) = Set.univ ↔ _
    rw [← Submodule.topologicalClosure_coe]
    exact SetLike.coe_set_eq (p := R.topologicalClosure) (q := ⊤)
  rw [hr, Submodule.topologicalClosure_eq_top_iff]
  apply eq_bot_iff.mpr
  intro v hv
  have hgen : ∀ g : {g : ℝ → ℂ // SupportedTest t g},
      ⟪energyVector t g.1, (v : Ambient t)⟫_ℂ = 0 := by
    intro g
    have hm : testVectorFamily t g ∈ LinearMap.range (Finsupp.linearCombination ℂ (testVectorFamily t)) :=
      ⟨Finsupp.single g 1, by simp⟩
    have hz := (R.mem_orthogonal v).mp hv _ hm
    simpa [testVectorFamily, sourceEmbed_L t ht g.1 g.2] using hz
  have hs : energySubspace t ≤ (ℂ ∙ (v : Ambient t))ᗮ := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _ (ℂ ∙ (v : Ambient t)).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hgen g)
  have hz := Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hs v.2)
  apply Subtype.ext
  exact inner_self_eq_zero.mp hz

private theorem inner_ext_of_dense_generators {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 (u : ι → H)
    (hd : DenseRange (Finsupp.linearCombination ℂ u)) (x y : H)
    (hi : ∀ i, ⟪x, u i⟫_ℂ = ⟪y, u i⟫_ℂ) : x = y := by
  apply ext_inner_right ℂ
  intro z
  refine hd.induction_on (p := fun w => ⟪x, w⟫_ℂ = ⟪y, w⟫_ℂ) z ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner continuous_id)
  · intro a
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum,
      inner_smul_right, hi]


end ConnesGreen.RG0Integration
theorem solution (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (ρ : CriticalZeros) :
    U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
      sourceEmbed t (actualGreenSource ρ) := by
  apply ConnesGreen.RG0Integration.inner_ext_of_dense_generators (ConnesGreen.RG0Integration.testVectorFamily t)
    (ConnesGreen.RG0Integration.testVectorFamily_linearCombination_dense t ht)
  intro g
  dsimp only [ConnesGreen.RG0Integration.testVectorFamily]
  change ⟪U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)),
    sourceEmbed t (problemOneL g.1)⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪sourceEmbed T (actualGreenSource ρ), U (sourceEmbed t (problemOneL g.1))⟫_ℂ = _
  rw [hU g.1 g.2, ConnesGreen.RG0Integration.source_pairing_global T hT g.1 (ConnesGreen.RG0Integration.supportedTest_mono g.2 htT),
    ConnesGreen.RG0Integration.source_pairing_global t ht g.1 g.2]
