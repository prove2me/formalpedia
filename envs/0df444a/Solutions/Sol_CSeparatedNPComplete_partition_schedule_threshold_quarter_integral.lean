-- Prove2me | solution 1 for CSeparatedNPComplete.partition_schedule_threshold_quarter_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:53.723731+00:00
-- url     : https://prove2.me/submissions/84611688-f527-40a2-894f-1e74add2379a

module
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Definitions.Def_CSeparatedNPComplete_Gadget
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (d : Nat) (s : Fin d → Nat) :
    ∃ z : ℤ, partition_schedule_threshold d (fun i => (s i : ℝ)) = (z : ℝ) / 4 := by
  refine ⟨(∑ i, (s i : ℤ)) * (d : ℤ) * ((d : ℤ) + 1) - 3 * (d : ℤ), ?_⟩
  simp only [partition_schedule_threshold, dot, Pi.one_apply, mul_one]
  push_cast
  ring
end CSeparatedNPComplete
