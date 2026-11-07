-- Prove2me | solution 1 for BertsekasShreve.BorelInfinite.optimality_equation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:40:41.945111+00:00
-- url     : https://prove2.me/submissions/40b10d86-6c8f-447d-aeca-6c0a275aa0b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel
import Theorems.Thm_BertsekasShreve_BorelInfinite_Jbarstar_eq_expect_Jstar
import Theorems.Thm_BertsekasShreve_BorelInfinite_Tbar_expect_eq_expect_T
import Theorems.Thm_BertsekasShreve_BorelInfinite_optimality_equation_DM
import Theorems.Thm_BertsekasShreve_BorelInfinite_Jstar_sign
import Theorems.Thm_BertsekasShreve_BorelInfinite_Jstar_lowerSemianalytic

open MeasureTheory ProbabilityTheory Filter Topology

namespace BSOptEqAux

open BertsekasShreve.BorelInfinite

lemma ereal_pos_sub_neg (a : EReal) (h : a.toENNReal ≠ ⊤) :
    ((a.toENNReal : EReal) - ((-a).toENNReal : EReal)) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp at h
  | coe r =>
    rcases le_total 0 r with hr | hr
    · have h1 : (-(r : EReal)).toENNReal = 0 := by
        rw [EReal.toENNReal_eq_zero_iff]; exact_mod_cast (by linarith : -r ≤ 0)
      rw [h1, EReal.coe_toENNReal (by exact_mod_cast hr)]; simp
    · have h1 : ((r : EReal)).toENNReal = 0 := by
        rw [EReal.toENNReal_eq_zero_iff]; exact_mod_cast hr
      rw [h1, EReal.coe_toENNReal (by exact_mod_cast (by linarith : 0 ≤ -r))]; simp

lemma expect_dirac {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (x : S) (J : S → EReal) :
    DupacovaWets.Consistency.expect (Measure.dirac x) J = J x := by
  unfold DupacovaWets.Consistency.expect
  rw [lintegral_dirac, lintegral_dirac]
  split_ifs with h
  · rw [EReal.toENNReal_eq_top_iff] at h; exact h.symm
  · exact ereal_pos_sub_neg _ h

lemma measurable_t {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W] (M : Model S C W) :
    Measurable M.t := by
  haveI := M.p_markov
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun zw : (S × C) × W => M.f (zw.1.1, zw.1.2, zw.2)) :=
    M.f_measurable.comp (by fun_prop)
  have key : (fun z => M.t z s) =
      fun z => M.p z (Prod.mk z ⁻¹' ((fun zw : (S × C) × W => M.f (zw.1.1, zw.1.2, zw.2)) ⁻¹' s)) := by
    funext z
    simp only [Model.t]
    have hz : Measurable (fun w => M.f (z.1, z.2, w)) := M.f_measurable.comp (by fun_prop)
    rw [Measure.map_apply hz hs]
    rfl
  rw [key]
  exact Kernel.measurable_kernel_prodMk_left (hf hs)

lemma fbar_isProb {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W] (M : Model S C W)
    (q : Measure (S × C)) [IsProbabilityMeasure q] : IsProbabilityMeasure (M.fbar q) := by
  haveI := M.p_markov
  constructor
  simp only [Model.fbar]
  rw [Measure.bind_apply MeasurableSet.univ (measurable_t M).aemeasurable]
  have : ∀ z, M.t z Set.univ = 1 := by
    intro z
    simp only [Model.t]
    have hf : Measurable (fun w => M.f (z.1, z.2, w)) := M.f_measurable.comp (by fun_prop)
    rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp [this]

end BSOptEqAux

open BSOptEqAux in
theorem solution {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : BertsekasShreve.BorelInfinite.Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) :
    M.Jstar = M.T M.Jstar := by
  open BertsekasShreve.BorelInfinite in
  -- `S` is T2 (it is homeomorphic to a subspace of a metric space), so singletons are Borel.
  haveI : T2Space S := by
    obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ :=
      BertsekasShreve.AnalyticSelection.IsBorelSpace.exists_homeomorph_borel (X := S)
    exact e.isEmbedding.t2Space
  funext x
  -- `J̄(p) = ∫ J* dp`
  have hsign := BertsekasShreve.BorelInfinite.Jstar_sign M
  have hJ : (M.CaseP ∧ ∀ x, 0 ≤ M.Jstar x) ∨ (M.CaseN ∧ ∀ x, M.Jstar x ≤ 0) ∨
      (M.CaseD ∧ ∃ c : ℝ, ∀ x, -(c : EReal) ≤ M.Jstar x ∧ M.Jstar x ≤ (c : EReal)) := by
    rcases hcase with h | h | h
    · exact Or.inl ⟨h, hsign.1 h⟩
    · exact Or.inr (Or.inl ⟨h, hsign.2.1 h⟩)
    · exact Or.inr (Or.inr ⟨h, hsign.2.2 h⟩)
  have hlsa := BertsekasShreve.BorelInfinite.Jstar_lowerSemianalytic M hcase
  have h95 : ∀ (p : Measure S), IsProbabilityMeasure p →
      M.Jbarstar p = DupacovaWets.Consistency.expect p M.Jstar :=
    fun p hp => BertsekasShreve.BorelInfinite.Jbarstar_eq_expect_Jstar M hcase p
  -- `T̄(J̄*)(p_x) = T̄(∫ J* d·)(p_x)`, since `T̄` only evaluates `J̄*` at the probability
  -- measures `f̄(q)`, `q ∈ Ū(p_x)`.
  have hT : M.Tbar M.Jbarstar (Measure.dirac x) =
      M.Tbar (fun p' => DupacovaWets.Consistency.expect p' M.Jstar) (Measure.dirac x) := by
    unfold BertsekasShreve.BorelInfinite.Model.Tbar
    refine iInf_congr fun q => iInf_congr fun hq => ?_
    haveI : IsProbabilityMeasure q := hq.1
    haveI := fbar_isProb M q
    rw [h95 (M.fbar q) inferInstance]
  calc M.Jstar x = DupacovaWets.Consistency.expect (Measure.dirac x) M.Jstar :=
        (expect_dirac x _).symm
    _ = M.Jbarstar (Measure.dirac x) := (h95 _ inferInstance).symm
    _ = M.Tbar M.Jbarstar (Measure.dirac x) :=
        BertsekasShreve.BorelInfinite.optimality_equation_DM M hcase _
    _ = M.Tbar (fun p' => DupacovaWets.Consistency.expect p' M.Jstar) (Measure.dirac x) := hT
    _ = DupacovaWets.Consistency.expect (Measure.dirac x) (M.T M.Jstar) :=
        BertsekasShreve.BorelInfinite.Tbar_expect_eq_expect_T M M.Jstar hlsa hJ _
    _ = M.T M.Jstar x := expect_dirac x _
