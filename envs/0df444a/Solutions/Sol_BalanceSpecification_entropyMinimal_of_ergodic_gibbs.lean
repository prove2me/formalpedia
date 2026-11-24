-- Prove2me | solution 1 for BalanceSpecification.entropyMinimal_of_ergodic_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:14.855545+00:00
-- url     : https://prove2.me/submissions/14d993bd-08c8-4f38-8c0b-a91e23b7665f

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_entropy_lt_of_proper_subshift_of_ergodic_gibbs
public import Theorems.Thm_BalanceSpecification_entropyMinimal_of_nonempty_subshift_entropy_lt


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution
    {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hErg : Ergodic (shiftMap X) (μ : Measure X.carrier)) : EntropyMinimal X := by
  apply entropyMinimal_of_nonempty_subshift_entropy_lt hX
  intro Y hY hproper
  exact entropy_lt_of_proper_subshift_of_ergodic_gibbs hX hG hErg hY hproper
end BalanceSpecification
