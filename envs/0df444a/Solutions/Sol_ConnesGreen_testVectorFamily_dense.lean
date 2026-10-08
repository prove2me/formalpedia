-- Prove2me | solution 1 for ConnesGreen.testVectorFamily_dense
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:17:11.896182+00:00
-- url     : https://prove2.me/submissions/021a779d-46df-4db1-afe6-f5bdb5eb70ed

import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
private theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem supported_energyDomain (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    EnergyDomain t g :=
  ⟨continuous_window_memLp _ _ hg.1.1.continuous,
    continuous_window_memLp _ _ (hg.1.1.continuous_iteratedDeriv 1 (by simp))⟩

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
    have he := ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht g.1 g.2
    change ⟪(sourceEmbed t (problemOneL g.1) : Ambient t), (v : Ambient t)⟫_ℂ = 0 at hz
    rwa [he] at hz
  have hs : energySubspace t ≤ (ℂ ∙ (v : Ambient t))ᗮ := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _ (ℂ ∙ (v : Ambient t)).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hgen g)
  have hz := Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hs v.2)
  apply Subtype.ext
  exact inner_self_eq_zero.mp hz
private theorem supportedTest_add {t : ℝ} {g h : ℝ → ℂ}
    (hg : SupportedTest t g) (hh : SupportedTest t h) : SupportedTest t (g + h) := by
  refine ⟨⟨hg.1.1.add hh.1.1, hg.1.2.add hh.1.2⟩, ?_⟩
  exact tsupport_add g h |>.trans (Set.union_subset hg.2 hh.2)

private theorem supportedTest_smul {t : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (a : ℂ) : SupportedTest t (a • g) := by
  refine ⟨⟨hg.1.1.const_smul a, hg.1.2.smul_left⟩, ?_⟩
  exact (tsupport_smul_subset_right (fun _ : ℝ => a) g).trans hg.2

private theorem windowL2_add (t : ℝ) (g h : ℝ → ℂ)
    (hg : MemLp g 2 (windowMeasure t)) (hh : MemLp h 2 (windowMeasure t)) :
    windowL2 t (g + h) = windowL2 t g + windowL2 t h := by
  simp only [windowL2, dif_pos hg, dif_pos hh, dif_pos (hg.add hh)]
  exact MemLp.toLp_add hg hh

private theorem windowL2_smul (t : ℝ) (g : ℝ → ℂ)
    (hg : MemLp g 2 (windowMeasure t)) (a : ℂ) :
    windowL2 t (a • g) = a • windowL2 t g := by
  simp only [windowL2, dif_pos hg, dif_pos (hg.const_smul a)]
  exact MemLp.toLp_const_smul a hg

private theorem energyVector_add (t : ℝ) (g h : ℝ → ℂ)
    (hg : SupportedTest t g) (hh : SupportedTest t h) :
    energyVector t (g + h) = energyVector t g + energyVector t h := by
  have hd : iteratedDeriv 1 (g + h) = iteratedDeriv 1 g + iteratedDeriv 1 h := by
    funext x
    exact iteratedDeriv_add (hg.1.1.of_le (by simp)).contDiffAt
      (hh.1.1.of_le (by simp)).contDiffAt
  have eg := supported_energyDomain t g hg
  have eh := supported_energyDomain t h hh
  apply (WithLp.equiv 2 _).injective
  funext i
  fin_cases i
  · change windowL2 t (iteratedDeriv 1 (g + h)) = _
    rw [hd, windowL2_add t _ _ eg.2 eh.2]
    rfl
  · change (1 / 2 : ℂ) • windowL2 t (g + h) = _
    rw [windowL2_add t _ _ eg.1 eh.1, smul_add]
    rfl

private theorem energyVector_smul (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (a : ℂ) :
    energyVector t (a • g) = a • energyVector t g := by
  have hd : iteratedDeriv 1 (a • g) = a • iteratedDeriv 1 g := by
    funext x
    exact iteratedDeriv_const_smul (hg.1.1.of_le (by simp)).contDiffAt a
  have eg := supported_energyDomain t g hg
  apply (WithLp.equiv 2 _).injective
  funext i
  fin_cases i
  · change windowL2 t (iteratedDeriv 1 (a • g)) = _
    rw [hd, windowL2_smul t _ eg.2 a]
    rfl
  · change (1 / 2 : ℂ) • windowL2 t (a • g) = a • ((1 / 2 : ℂ) • windowL2 t g)
    rw [windowL2_smul t _ eg.1 a]
    exact smul_comm _ _ _


theorem solution (t : ℝ) (ht : 0 < t) : DenseRange (fun g : {g : ℝ → ℂ // SupportedTest t g} => sourceEmbed t (problemOneL g.1)) := by
  apply (testVectorFamily_linearCombination_dense t ht).mono
  rintro _ ⟨v, rfl⟩
  induction v using Finsupp.induction with
  | zero =>
    have hz : SupportedTest t (0 : ℝ → ℂ) :=
      ⟨⟨contDiff_const, HasCompactSupport.zero⟩, by simp⟩
    refine ⟨⟨0, hz⟩, ?_⟩
    apply Subtype.ext
    change (sourceEmbed t (WeilDefect.problemOneL 0) : Ambient t) = _
    rw [ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht _ hz]
    simp only [energyVector, windowL2, Pi.zero_def]
    apply (WithLp.equiv 2 _).injective
    funext i
    fin_cases i <;> simp <;> exact MemLp.toLp_zero _
  | @single_add i a v hi ha ih =>
    obtain ⟨g, hg⟩ := ih
    let h := a • i.1 + g.1
    have hh : SupportedTest t h := supportedTest_add (supportedTest_smul i.2 a) g.2
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [map_add, Finsupp.linearCombination_single, ← hg]
    apply Subtype.ext
    simp only [testVectorFamily, ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht _ hh,
      ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht i.1 i.2, ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht g.1 g.2,
      Submodule.coe_add, Submodule.coe_smul]
    exact (energyVector_add t _ _ (supportedTest_smul i.2 a) g.2).trans
      (congrArg (fun x => x + energyVector t g.1) (energyVector_smul t i.1 i.2 a))

