-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.ae_code_property_on_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:55:46.190311+00:00
-- url     : https://prove2.me/submissions/07b630ea-e00d-4575-bf24-f8ff166b1a91

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_CommonTypical
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_ae_code_property
import Theorems.Thm_BianchiIX_gaussCode_recurrence
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_pos (a : ℕ → ℕ+) : 0 < gaussCode a := by
  rw [gaussCode_recurrence a]
  apply gaussInv_pos _ (gaussCode_mem_unit (shiftDigits a 1)).1
  exact_mod_cast Nat.succ_le_of_lt (a 0).pos

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_lt_one (a : ℕ → ℕ+) : gaussCode a < 1 := by
  rw [gaussCode_recurrence a]
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have ht := gaussCode_pos (shiftDigits a 1)
  unfold gaussInv
  exact (div_lt_one (by positivity)).mpr (by linarith)

end
end

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1), P y) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), P (T.code x) := by
  have hp := E.ae_code_property hbudget ((ae_restrict_iff' isOpen_Ioo.measurableSet).mp hP)
  filter_upwards [hp] with x hx
  exact hx ⟨gaussCode_pos (T.digits x), gaussCode_lt_one (T.digits x)⟩
