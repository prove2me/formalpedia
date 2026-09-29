-- Prove2me | solution 1 for FoundationsML.Stability.stability_generalization_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:25:31.486176+00:00
-- url     : https://prove2.me/submissions/bd78daf5-94bb-41fc-a747-00c8255ac037

import Mathlib
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_UniformlyStable

open MeasureTheory

namespace FoundationsML.Stability

universe u v w

instance aux_sgb_msc : MeasurableSingletonClass (ULift.{v} Bool) :=
  ⟨fun x => (measurableSet_preimage_up (s := ({x} : Set (ULift.{v} Bool)))).mp
    (Set.toFinite _).measurableSet⟩

/-- The loss: `-1` on label `true`, `0` on label `false` (bounded above by `0`, not below). -/
noncomputable def aux_sgb_L : PUnit.{w+1} → ULift.{v} Bool → ℝ :=
  fun _ b => if b.down then -1 else 0

/-- The constant algorithm. -/
def aux_sgb_A : (Fin 1 → PUnit.{u+1} × ULift.{v} Bool) → (PUnit.{u+1} → PUnit.{w+1}) :=
  fun _ _ => PUnit.unit

/-- Uniform distribution on `PUnit × ULift Bool`. -/
noncomputable def aux_sgb_D : Measure (PUnit.{u+1} × ULift.{v} Bool) :=
  (PMF.uniformOfFintype (PUnit.{u+1} × ULift.{v} Bool)).toMeasure

instance aux_sgb_D_prob : IsProbabilityMeasure aux_sgb_D.{u, v} := by
  unfold aux_sgb_D; infer_instance

lemma aux_sgb_gen (S : Fin 1 → PUnit.{u+1} × ULift.{v} Bool) :
    GeneralizationError aux_sgb_D aux_sgb_L.{v, w} (aux_sgb_A S) = -1/2 := by
  unfold GeneralizationError aux_sgb_D
  rw [PMF.integral_eq_sum]
  simp [Fintype.sum_prod_type, Loss, aux_sgb_L, PMF.uniformOfFintype_apply]
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  simp [Equiv.ulift]
  norm_num

lemma aux_sgb_set :
    {S : Fin 1 → PUnit.{u+1} × ULift.{v} Bool |
        GeneralizationError aux_sgb_D aux_sgb_L.{v, w} (aux_sgb_A S) ≤
        EmpiricalError aux_sgb_L S (aux_sgb_A S) + 0 +
          (2 * ((1 : ℕ) : ℝ) * 0 + 0) * Real.sqrt (Real.log (1 / (1/4 : ℝ)) / (2 * ((1 : ℕ) : ℝ)))}
      = Set.univ.pi (fun _ : Fin 1 => {z : PUnit.{u+1} × ULift.{v} Bool | z.2.down = false}) := by
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, aux_sgb_gen]
  simp only [EmpiricalError, Loss, aux_sgb_L, Fin.sum_univ_one, Fin.forall_fin_one]
  rcases (S 0).2 with ⟨_ | _⟩ <;> norm_num

lemma aux_sgb_half :
    aux_sgb_D.{u, v} {z : PUnit.{u+1} × ULift.{v} Bool | z.2.down = false} = 1/2 := by
  unfold aux_sgb_D
  rw [PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type, Set.indicator, PMF.uniformOfFintype_apply]
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  simp [Equiv.ulift]


end FoundationsML.Stability

open FoundationsML.Stability
open MeasureTheory

theorem solution : ¬ (∀
    {X Y Y' : Type} [MeasurableSpace (X × Y)] (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 0 < m)
    (L : Y' → Y → ℝ) (A : (Fin m → X × Y) → (X → Y')) (β M : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hstab : UniformlyStable L A β)
    (hbound : ∀ S : Fin m → X × Y, ∀ z : X × Y, Loss L (A S) z ≤ M)
    (hAmeas : ∀ S : Fin m → X × Y, Measurable (Loss L (A S)))
    (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × Y | GeneralizationError D L (A S) ≤
        EmpiricalError L S (A S) + β +
          (2 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro h
  have key := h aux_sgb_D (m := 1) one_pos
    aux_sgb_L aux_sgb_A 0 0 le_rfl le_rfl
    (by intro S S' _ z; rw [show aux_sgb_A S = aux_sgb_A S' from rfl]; simp)
    (by intro S z; unfold Loss aux_sgb_L; split_ifs <;> norm_num)
    (fun S => measurable_of_countable _)
    (1/4) (by norm_num)
  rw [aux_sgb_set, Measure.pi_pi, Fin.prod_univ_one, aux_sgb_half] at key
  norm_num at key
