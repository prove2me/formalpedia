-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.enlargeEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T16:00:32.72609+00:00
-- url     : https://prove2.me/submissions/47ca468f-cff9-4422-87c0-5afc7f5a077d

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.enlargeEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
import Theorems.Thm_BookProof_ChapterSolovayCoordinates_tailSplitEquiv_map
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N k : ℕ) (headDist : Measure (Fin N → ℝ))
    [IsProbabilityMeasure headDist] :
    Measure.map (enlargeEquiv N k) (coordinateStateMeasure N headDist) =
      coordinateStateMeasure (N + k) (enlargedHeadMeasure N k headDist) := by

  simp only [coordinateStateMeasure]
  have h_tailSplit : Measure.map (↑(tailSplitEquiv k)) coordinateTailMeasure =
      (gaussianHead k).prod coordinateTailMeasure := tailSplitEquiv_map k
  rw [enlargeEquiv]
  -- Define the intermediate equivalences
  let e1 : (Fin N → ℝ) × CoordinateTail ≃ᵐ (Fin N → ℝ) × ((Fin k → ℝ) × CoordinateTail) :=
    (MeasurableEquiv.refl (Fin N → ℝ)).prodCongr (tailSplitEquiv k)
  let e2 : (Fin N → ℝ) × ((Fin k → ℝ) × CoordinateTail) ≃ᵐ ((Fin N → ℝ) × (Fin k → ℝ)) ×
      CoordinateTail :=
    MeasurableEquiv.prodAssoc.symm
  let e3 : ((Fin N → ℝ) × (Fin k → ℝ)) × CoordinateTail ≃ᵐ (Fin (N + k) → ℝ) × CoordinateTail :=
    ((MeasurableEquiv.piCongrLeft (fun x => ℝ) finSumFinEquiv).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm.prodCongr (MeasurableEquiv.refl
          CoordinateTail)
  let e23 := e2.trans e3
  let e123 := e1.trans e23
  -- The enlargeEquiv is e1.trans (e2.trans e3)
  have h_eq : ∀ x, (((MeasurableEquiv.refl (Fin N → ℝ)).prodCongr (tailSplitEquiv k)).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        (((MeasurableEquiv.piCongrLeft (fun x => ℝ) finSumFinEquiv).symm.trans
                (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm.prodCongr
          (MeasurableEquiv.refl CoordinateTail)))) x = e3 (e2 (e1 x)) := by
    intro x; rfl
  have hfun : (⇑(((MeasurableEquiv.refl (Fin N → ℝ)).prodCongr (tailSplitEquiv k)).trans
      ((MeasurableEquiv.prodAssoc.symm).trans
        (((MeasurableEquiv.piCongrLeft (fun x => ℝ) finSumFinEquiv).symm.trans
                (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm.prodCongr
          (MeasurableEquiv.refl CoordinateTail)))) : (Fin N → ℝ) × CoordinateTail → _) =
      (fun x => e3 (e2 (e1 x))) := funext h_eq
  rw [hfun]
  have hcomp : (fun x => e3 (e2 (e1 x))) = e3 ∘ e2 ∘ e1 := rfl
  rw [hcomp]
  have h_comp : (⇑e3 ∘ ⇑e2 ∘ ⇑e1 : (Fin N → ℝ) × CoordinateTail → _) = ⇑(e1.trans e23) := rfl
  rw [h_comp]
  have h_trans : ⇑(e1.trans e23) = ⇑e23 ∘ ⇑e1 := rfl
  rw [h_trans, ← Measure.map_map (MeasurableEquiv.measurable e23) (MeasurableEquiv.measurable e1)]
  simp only [e1]
  have h_map_eq : Measure.map (⇑((MeasurableEquiv.refl (Fin N → ℝ)).prodCongr (tailSplitEquiv k)))
      (headDist.prod coordinateTailMeasure) = headDist.prod (Measure.map (tailSplitEquiv k)
          coordinateTailMeasure) := by
    simp? +unfoldPartialApp [MeasurableEquiv.prodCongr]
    rw [show Prod.map id (⇑(tailSplitEquiv k)) = (fun p : (Fin N → ℝ) × CoordinateTail => (p.1,
        tailSplitEquiv k p.2)) from rfl]
    rw [show (fun p : (Fin N → ℝ) × CoordinateTail => (p.1, tailSplitEquiv k p.2)) = Prod.map (id :
        (Fin N → ℝ) → (Fin N → ℝ)) (tailSplitEquiv k) from rfl]
    ext s hs
    rw [Measure.map_apply (by measurability : Measurable _) hs]
    rw [Measure.prod_apply (by measurability : MeasurableSet (Prod.map id (tailSplitEquiv k) ⁻¹'
                               s))]
    rw [Measure.prod_apply hs]
    apply congr_arg
    funext x
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (by measurability : MeasurableSet _)]
    apply congr_arg
    funext y
    simp [Set.preimage]
  rw [h_map_eq, h_tailSplit]
  unfold enlargedHeadMeasure
  -- Goal: Measure.map e23 (headDist.prod ((gaussianHead k).prod coordinateTailMeasure)) = 
  --       (Measure.map e3' (headDist.prod (gaussianHead k))).prod coordinateTailMeasure
  -- where e3' is the concatenation equiv
  have he23 : ⇑e23 = ⇑e3 ∘ ⇑e2 := rfl
  rw [he23, ← Measure.map_map (MeasurableEquiv.measurable e3) (MeasurableEquiv.measurable e2)]
  simp only [e3]
  -- Step 1: Use Measure.map_map to combine e3.prodCongr refl and e2
  rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable e2)]
  -- The composition (e3.prodCongr refl) ∘ e2 = ((e3'.prodCongr refl) ∘ e2)
  -- We need to simplify: (e3'.prodCongr refl) ∘ e2
  -- e2 reassociates, so (e3'.prodCongr refl) ∘ e2 = (e3' ∘ fst₂) ⊗ refl ∘ snd₂ where fst₂, snd₂ are
  -- projections through e2
  -- Actually, let's just use simp to simplify the composition
  simp only [Function.comp_def]
  -- The function is: fun (a, (b, c)) => (e3' (a, b), c)
  -- This is equivalent to Prod.map e3' id composed with e2
  have h_fun : (fun x => (((MeasurableEquiv.piCongrLeft (fun x => ℝ) finSumFinEquiv).symm.trans 
      (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm.prodCongr (MeasurableEquiv.refl
          CoordinateTail)) (e2 x)) 
      = Prod.map (((MeasurableEquiv.piCongrLeft (fun x => ℝ) finSumFinEquiv).symm.trans 
      (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm) id ∘ e2 := rfl
  rw [h_fun]
  -- Now use Measure.prod_map to split Prod.map e3' id
  ext s hs
  rw [Measure.prod_apply hs]
  -- LHS: Measure.map (Prod.map e3' id ∘ e2) μ
  -- Rewrite using Measure.map_map
  rw [← Measure.map_map (by measurability : Measurable _) (MeasurableEquiv.measurable e2)]
  let e3' : (Fin N → ℝ) × (Fin k → ℝ) ≃ᵐ (Fin (N + k) → ℝ) :=
    ((MeasurableEquiv.piCongrLeft (fun x => ℝ) (finSumFinEquiv (m := N) (n := k))).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi fun x => ℝ)).symm
  have h1 : (Measure.map (Prod.map e3' id) (Measure.map e2 (headDist.prod ((gaussianHead k).prod
      coordinateTailMeasure)))) s =
      (Measure.map e2 (headDist.prod ((gaussianHead k).prod coordinateTailMeasure))) (Prod.map e3'
          id ⁻¹' s) := by
    apply Measure.map_apply
    · measurability
    · measurability
  rw [h1]
  -- Apply Measure.map_apply to LHS
  have h2 : (Measure.map e2 (headDist.prod ((gaussianHead k).prod coordinateTailMeasure)))
      (Prod.map e3' id ⁻¹' s) =
      (headDist.prod ((gaussianHead k).prod coordinateTailMeasure))
        (e2 ⁻¹' (Prod.map e3' id ⁻¹' s)) := by
    apply Measure.map_apply
    · exact MeasurableEquiv.measurable e2
    · measurability
  rw [h2]
  -- Simplify the preimage: e2 = prodAssoc.symm maps (a, (b, c)) ↦ ((a, b), c)
  -- So e2 ⁻¹' (Prod.map e3' id ⁻¹' s) = {(a, b, c) | (e3'(a, b), c) ∈ s}
  have h_preimage : ⇑e2 ⁻¹' (Prod.map ⇑e3' id ⁻¹' s) = 
      {p : (Fin N → ℝ) × (Fin k → ℝ) × CoordinateTail | (e3' (p.1, p.2.1), p.2.2) ∈ s} := by
    ext ⟨a, b, c⟩
    simp [Set.mem_preimage, Prod.map, e2]; rfl
  rw [h_preimage]
  -- Use Measure.prod_apply on LHS
  have h_meas : MeasurableSet {p : (Fin N → ℝ) × (Fin k → ℝ) × CoordinateTail | (e3' (p.1, p.2.1),
      p.2.2) ∈ s} := by
    have : Measurable (fun p : (Fin N → ℝ) × (Fin k → ℝ) × CoordinateTail => (e3' (p.1, p.2.1),
        p.2.2)) := by
      measurability
    exact this hs
  rw [Measure.prod_apply h_meas]
  -- Simplify the inner set: Prod.mk x ⁻¹' {p | (e3' (p.1, p.2.1), p.2.2) ∈ s}
  -- = {(b, c) | (e3' (x, b), c) ∈ s}
  have h_inner : ∀ x : Fin N → ℝ,    Prod.mk x ⁻¹' {p : (Fin N → ℝ) × (Fin k → ℝ) × CoordinateTail |
      (e3' (p.1, p.2.1), p.2.2) ∈ s} = 
      {(b, c) : (Fin k → ℝ) × CoordinateTail | (e3' (x, b), c) ∈ s} := by
    intro x
    ext ⟨b, c⟩
    simp []
  simp_rw [h_inner]
  -- Apply Measure.prod_apply to inner measure
  have h_inner_meas : ∀ x : Fin N → ℝ,    MeasurableSet {(b, c) : (Fin k → ℝ) × CoordinateTail |
      (e3' (x, b), c) ∈ s} := by
    intro x
    have : Measurable (fun p : (Fin k → ℝ) × CoordinateTail => (e3' (x, p.1), p.2)) := by
      measurability
    exact this hs
  -- Rewrite using Measure.prod_apply inside the integral
  have h_lhs_eq : ∀ x : Fin N → ℝ,    ((gaussianHead k).prod coordinateTailMeasure) {(b, c) | (e3'
      (x, b), c) ∈ s} =
      ∫⁻ (b : Fin k → ℝ), coordinateTailMeasure {c | (e3' (x, b), c) ∈ s} ∂gaussianHead k := by
    intro x
    exact Measure.prod_apply (h_inner_meas x)
  simp_rw [h_lhs_eq]
  -- The goal should now be to show LHS = RHS after the previous rewrites
  -- Define the function we're integrating
  let f : (Fin N → ℝ) → (Fin k → ℝ) → ℝ≥0∞ := fun x b => coordinateTailMeasure {c | (e3' (x, b), c)
      ∈ s}
  -- Measurability of the section measure
  have hg : Measurable (fun x => coordinateTailMeasure {x_1 | (x, x_1) ∈ s}) := 
    measurable_measure_prodMk_left hs
  -- Show measurability of f
  have h_f_meas : AEMeasurable (fun p : (Fin N → ℝ) × (Fin k → ℝ) => f p.1 p.2) (headDist.prod
      (gaussianHead k)) := by
    have heq : (fun p : (Fin N → ℝ) × (Fin k → ℝ) => f p.1 p.2) = (fun x => coordinateTailMeasure
        {x_1 | (x, x_1) ∈ s}) ∘ e3' := rfl
    rw [heq]
    exact AEMeasurable.comp_aemeasurable (Measurable.aemeasurable hg) (MeasurableEquiv.measurable
        e3').aemeasurable
  -- Apply Fubini's theorem to LHS: ∫⁻ x, ∫⁻ b, f(x,b) ∂ν ∂μ = ∫⁻ p, f(p.1, p.2) ∂(μ.prod ν)
  have h_fubini : ∫⁻ (x : Fin N → ℝ), ∫⁻ (b : Fin k → ℝ), f x b ∂(gaussianHead k) ∂headDist = 
      ∫⁻ (p : (Fin N → ℝ) × (Fin k → ℝ)), f p.1 p.2 ∂(headDist.prod (gaussianHead k)) := by
    rw [← MeasureTheory.lintegral_lintegral h_f_meas]
  rw [h_fubini]
  -- Show that Prod.mk x ⁻¹' s = {x_1 | (x, x_1) ∈ s}
  have h_set_eq : ∀ x : Fin (N + k) → ℝ, Prod.mk x ⁻¹' s = {x_1 | (x, x_1) ∈ s} := by
    intro x; ext y; simp [Set.mem_preimage]
  simp_rw [h_set_eq]
  -- Now show both integrals are equal using change of variables
  -- RHS integral equals LHS by change of variables with e3'
  have h_rhs_eq : ∫⁻ (x : Fin (N + k) → ℝ), coordinateTailMeasure {x_1 | (x, x_1) ∈ s} 
      ∂Measure.map (⇑e3') (headDist.prod (gaussianHead k)) = 
      ∫⁻ (p : (Fin N → ℝ) × (Fin k → ℝ)), coordinateTailMeasure {x_1 | (e3' p, x_1) ∈ s} 
      ∂(headDist.prod (gaussianHead k)) := by
    symm
    rw [MeasureTheory.lintegral_map hg (MeasurableEquiv.measurable e3')]
  rw [h_rhs_eq]
