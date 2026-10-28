-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservablePoincare.observable_poincare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:27:42.663426+00:00
-- url     : https://prove2.me/submissions/e693b7b0-da6e-4b6d-b24f-ed80fa81c9a3

/-
Required support modules adapted from meelgroup/arlib, commit 6262f60ad7556be62e94e87f6b5811cf299e7d94. Copyright and authorship notices are preserved in each file. Module import paths use CountingMatroidSupport; original declaration namespaces are retained for proof compatibility. Arlib is not a Lake package dependency.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BalancedCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_DisjointFlowSum
import Definitions.Def_CountingMatroid_Analysis_EmbeddedFlow
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LeafCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_Arlib_MarkovChains_sum_pair_sq
import Theorems.Thm_CountingMatroid_Analysis_DefectMeanExchangeFlow_defect_mean_exchange_flow
import Theorems.Thm_CountingMatroid_Analysis_ExchangeFlowEnergy_conditional_mean_demand_pairing
import Theorems.Thm_CountingMatroid_Analysis_ExchangeFlowEnergy_flow_energy_bound
import Theorems.Thm_CountingMatroid_Analysis_ObservablePoincare_ideal_dirichlet_min_weights
import Theorems.Thm_CountingMatroid_Analysis_ObservablePoincare_observable_poincare_constant_bound
import Theorems.Thm_CountingMatroid_Analysis_ObservableVarianceDecomposition_class_mass_le_one
import Theorems.Thm_CountingMatroid_Analysis_ObservableVarianceDecomposition_class_mass_partition
import Theorems.Thm_CountingMatroid_Analysis_ObservableVarianceDecomposition_observable_variance_decomposition
import Theorems.Thm_CountingMatroid_Analysis_OnePairObservablePoincare_one_pair_observable_poincare
import Theorems.Thm_CountingMatroid_Analysis_TransversalEventMean_large_pair_event_mean_bound
import Theorems.Thm_CountingMatroid_Analysis_TransversalEventMean_pair_event_mass_partition
import Theorems.Thm_CountingMatroid_Analysis_TransversalVarianceBound_transversal_variance_bound
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.ObservablePoincare
end CountingMatroid.Analysis.ObservablePoincare
namespace CountingMatroid.Analysis.DefectMeanExchangeFlow
end CountingMatroid.Analysis.DefectMeanExchangeFlow
namespace CountingMatroid.Analysis.DefectTransportRaw
end CountingMatroid.Analysis.DefectTransportRaw
namespace CountingMatroid.Analysis.DefectLeafClassifier
end CountingMatroid.Analysis.DefectLeafClassifier
namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
namespace CountingMatroid.Analysis.ConditionalLeafClassifier
end CountingMatroid.Analysis.ConditionalLeafClassifier
namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
namespace CountingMatroid.Analysis.DefectSlotFutureBound
end CountingMatroid.Analysis.DefectSlotFutureBound
namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
namespace CountingMatroid.Analysis.DefectPartitionTriangle
end CountingMatroid.Analysis.DefectPartitionTriangle
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.TransversalVarianceBound
end CountingMatroid.Analysis.TransversalVarianceBound
namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Dirichlet form, the Poincaré inequality, and positive semidefiniteness

Where `Var_μ(f)` measures the *global* variation of `f`, the Dirichlet form
`ℰ_P(f)` measures its *local* variation along the edges of the transition graph
`(Ω, P)`.  The entire mixing-time theory is the comparison of the two: a chain
mixes quickly exactly when local variation controls global variation, which is
the Poincaré inequality `γ · Var_μ(f) ≤ ℰ_P(f)`.

* `dirichlet μ P f g` — the bilinear form `⟪f, (I - P) g⟫_μ`; the Dirichlet form
  proper is the quadratic case `dirichlet μ P f f`.
* `sum_pair_sq` — the workhorse: for a *stationary* `μ` and any `s : ℝ`,
  `∑ x, ∑ y, μ x * P x y * (f x + s * f y) ^ 2 = (1 + s²)⟪f,f⟫ + 2s⟪f, Pf⟫`.
  Specialising to `s = -1` gives the pair form of the Dirichlet form, and to
  `s = 1` the lower bound `-⟪f,f⟫ ≤ ⟪f, Pf⟫`.  Both signs matter: one says the
  chain is a contraction, the other that it cannot overshoot.
* `dirichlet_self_eq_pair` — `ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`, the
  paper's definition, here a theorem.
* `SpectralGapAtLeast μ P γ` — the Poincaré inequality.  Following the source
  monograph we take this *as* the definition of the spectral gap: for reversible
  chains it agrees with `1 - λ₂`, and for non-reversible ones it is the right
  notion anyway (the "Poincaré constant"), so no eigenvalue is ever needed.
* `NonnegDefinite μ P` — `0 ≤ ⟪f, P f⟫_μ` for all `f`, the PSD condition.  This
  is what upgrades the spectral gap to the *absolute* spectral gap, and hence
  what makes the gap control the decay of variance; see
  `Arlib.MarkovChains.Techniques.SpectralGap`.

The pay-off proved here is `ip_act_le_of_gap`: on a mean-zero function a chain
with gap `γ` which is PSD satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`, the
two-sided bound that drives everything downstream.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The Dirichlet form -/



theorem dirichlet_apply (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    dirichlet μ P f g = ip μ f g - ip μ f (P.act g) := rfl

/-! ## The pair expansion

Everything about the Dirichlet form flows from a single computation: expanding
`∑_{x,y} μ(x) P(x,y) (f x + s · f y)²` for a stationary `μ`.  The `f x²` term is
resummed with `∑_y P x y = 1`, the `f y²` term with stationarity, and the cross
term is `⟪f, P f⟫_μ` on the nose. -/



/-- **Pair form of the Dirichlet form.**
`ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`.

This is the monograph's *definition* of the Dirichlet form; for us it is a
theorem, and it is the form in which the Dirichlet form is compared to the pair
form of the variance (`Var_eq_pair`). -/
theorem dirichlet_self_eq_pair {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) :
    dirichlet μ P f f = (1 / 2) * ∑ x, ∑ y, μ x * P x y * (f x - f y) ^ 2 := by
  have key := sum_pair_sq h f (-1)
  have rw_sub : ∀ x y : Ω, μ x * P x y * (f x + (-1) * f y) ^ 2
      = μ x * P x y * (f x - f y) ^ 2 := fun x y => by ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => rw_sub x y] at key
  rw [dirichlet_apply, key]
  ring

/-- The Dirichlet form is nonnegative: local variation is a sum of squares. -/
theorem dirichlet_self_nonneg {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : 0 ≤ dirichlet μ P f f := by
  rw [dirichlet_self_eq_pair h f]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  exact mul_nonneg (mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y)) (sq_nonneg _)

/-! ## Two-sided control of `⟪f, P f⟫_μ`

A stochastic kernel is a contraction on `L²(μ)`: taking `s = -1` above bounds
`⟪f, P f⟫_μ` from above by `⟪f, f⟫_μ`, and taking `s = 1` bounds it from below
by `-⟪f, f⟫_μ`.  These are the elementary substitutes for "all eigenvalues lie
in `[-1, 1]`". -/







/-! ## Symmetry and bilinearity -/











/-! ## The spectral gap -/









/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/





end Arlib.MarkovChains

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.IdealExchangeChain

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open Arlib.Probability Arlib.MarkovChains























/-- INTERNAL: Identify the operational rational type mean with expectation
under the concrete ideal stationary law, for correlated-observation analysis.
TEXLINE: main.tex:1241-1247 -/
theorem operational_type_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (kind : StateKind n) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (typeIndicator kind) =
      (typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  unfold Ex typeMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = kind
  · simp [operationalLaw, typeIndicator, hk]
  · simp [operationalLaw, typeIndicator, hk]





end CountingMatroid.Analysis.IdealExchangeChain

end

section


set_option autoImplicit false

/-!
Weighted moments for the operational classifier, and the first inequality
in the paper's observable Poincare proof. These identities do not assert
the quantitative transversal variance or defect transport estimates.
-/

namespace CountingMatroid.Analysis.ObservableVarianceDecomposition

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist







/-- INTERNAL: A classifier fiber has nonnegative probability mass. -/
theorem class_mass_nonneg {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) : 0 ≤ classMass π kind := by
  classical
  apply Finset.sum_nonneg
  intro state _
  split_ifs
  · exact π.coe_nonneg state
  · exact le_rfl



/-- INTERNAL: The conditional transversal second moment is nonnegative. -/
theorem transversal_variance_nonneg {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) : 0 ≤ transversalVariance π H := by
  classical
  unfold transversalVariance
  apply div_nonneg _ (class_mass_nonneg π .transversal)
  apply Finset.sum_nonneg
  intro state _
  split_ifs
  · exact mul_nonneg (π.coe_nonneg state) (sq_nonneg _)
  · exact le_rfl

/-- INTERNAL: The classifier-fiber mass equals the operational type mean.
TEXLINE: main.tex:721-744 -/
theorem operational_class_mass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) (kind : StateKind n) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) kind =
      (StationaryMeanIdentities.typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  rw [← operational_type_mean r o₁ o₂ q w hq hw kind]
  simp [classMass, Ex, typeIndicator]



/-- INTERNAL: Rejected classifier states have zero operational mass. -/
theorem operational_invalid_mass_zero {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) .invalid = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro state _
  by_cases hk : (classifyState state).val = .invalid
  · simp [hk, operationalLaw, StationaryMeanIdentities.stateWeight, weightOfKind]
  · simp [hk]

/-- INTERNAL: Diagonal defect labels have zero operational mass, even
without a separate correctness theorem for the classifier. -/
theorem diagonal_class_mass_zero {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) (i : Fin n) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) (.defect i i) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro state _
  by_cases hk : (classifyState state).val = .defect i i
  · simp [hk, operationalLaw, StationaryMeanIdentities.stateWeight, weightOfKind]
  · simp [hk]



end CountingMatroid.Analysis.ObservableVarianceDecomposition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · classifier mass identities, nonnegative transversal variance, and the projection's squared-deviation decomposition, including rejected and diagonal zero-mass classes.
-/

end

section


set_option autoImplicit false

/-!
The event selection and conditional-mean part of the paper's defect transfer
argument. The exchange transport estimate is separate: these results do not
assert an energy bound for transferring a defect mean to this event.
-/

namespace CountingMatroid.Analysis.TransversalEventMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open Arlib.Probability









/-- PAPER: main.tex:868-873
One of the four assignments at the specified pairs carries at least
one quarter of the transversal mass. -/
theorem large_pair_event {n : ℕ} (π : FinDist (PairedSet n)) (i k : Fin n) :
    ∃ a b : Bool,
      classMass π .transversal / 4 ≤ eventMass π (pairEvent i k a b) := by
  have hpart := pair_event_mass_partition π i k
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hpart
  by_contra h
  push_neg at h
  have hff := h false false
  have hft := h false true
  have htf := h true false
  have htt := h true true
  linarith





end CountingMatroid.Analysis.TransversalEventMean

end

section


set_option autoImplicit false

/-!
Signed exchange flows and their energy inequality. Conductances may vanish:
a flow must be zero on those pairs. These facts supply the summation-by-parts
and Cauchy--Schwarz step in the paper's transport construction; they do not
construct the recursively balanced flow or bound its energy.
-/

namespace CountingMatroid.Analysis.ExchangeFlowEnergy

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open Arlib.Probability
open scoped BigOperators













/-- INTERNAL: The energy of a potential is nonnegative for nonnegative
conductances. -/
theorem potential_energy_nonneg {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (hκ : ∀ x y, 0 ≤ κ x y) (H : α → ℝ) :
    0 ≤ potentialEnergy κ H := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hκ x y) (sq_nonneg _)

/-- INTERNAL: A certified divergence and a current-energy bound suffice
for the corresponding potential-mean estimate.
TEXLINE: main.tex:499-510 -/
theorem FlowCertificate.pairing_sq_le {α : Type*} [Fintype α]
    {κ : α → α → ℝ} {demand : α → ℝ} (flow : FlowCertificate κ demand)
    (hκ : ∀ x y, 0 ≤ κ x y) (K : ℝ) (hcost : flowEnergy κ flow.current ≤ K)
    (H : α → ℝ) : (∑ x, demand x * H x) ^ 2 ≤ K * potentialEnergy κ H := by
  simp_rw [← flow.divergence_eq]
  exact (flow_energy_bound κ flow.current hκ flow.antisymmetric flow.supported H).trans
    (mul_le_mul_of_nonneg_right hcost (potential_energy_nonneg κ hκ H))





end CountingMatroid.Analysis.ExchangeFlowEnergy

end
set_option autoImplicit false

/-!
The paper's observable Poincare estimate for the concrete operational law.
The energy identity below handles zero target weights explicitly. The
quantitative transport and transversal estimates are independent same-paper
obligations in DefectMeanExchangeFlow and TransversalVarianceBound;
stationarity alone does not establish them. The defect-mean step is reduced
to an exchange-supported signed current with prescribed conditional-mean
divergence and a normalized energy bound. Its summation-by-parts and
Cauchy--Schwarz implications are proved in ExchangeFlowEnergy. The one-pair
boundary case is closed outright using the constant-two estimate in
OnePairObservablePoincare.
-/

namespace CountingMatroid.Analysis.ObservablePoincare
end CountingMatroid.Analysis.ObservablePoincare
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservablePoincare

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- PAPER: main.tex:928-951
The observable Poincare inequality for exact matroid-oracle weights and good
multipliers. It controls the energy of the original function, preserving
its fluctuations within each defect fiber on the right-hand side. -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    Var π (observableProjection π H) ≤
      2000 * (n : ℝ) ^ 6 * dirichlet π (idealChain r o₁ o₂ q w hn hq hw) H H := by
  classical
  intro π
  let p₀ := classMass π .transversal
  let m₀ := classMean π H .transversal
  let V := transversalVariance π H
  let E := (1 / 2 : ℝ) * ∑ state : PairedSet n, ∑ next : PairedSet n,
    exchangeProposal n hn state next * min (π state) (π next) *
      (H state - H next) ^ 2
  have hEeq : E = dirichlet π (idealChain r o₁ o₂ q w hn hq hw) H H :=
    (ideal_dirichlet_min_weights r o₁ o₂ q w hn hq hw H).symm
  have hE : 0 ≤ E := by
    rw [hEeq]
    exact dirichlet_self_nonneg (ideal_chain_stationary r o₁ o₂ q w hn hq hw) H
  by_cases hnOne : n = 1
  · subst n
    have hzero : π ∅ = 0 := by
      have hk : (classifyState (∅ : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
    have hfullmass : π {(0, false), (0, true)} = 0 := by
      have hk : (classifyState ({(0, false), (0, true)} : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
    have htwo := OnePairObservablePoincare.one_pair_observable_poincare π hzero hfullmass H
    change Var π (observableProjection π H) ≤ 2 * E at htwo
    have hbound : Var π (observableProjection π H) ≤ 2000 * E :=
      htwo.trans (by nlinarith [hE])
    simpa only [Nat.cast_one, one_pow, mul_one, hEeq] using hbound
  have hp : 1 / (5 * (n : ℝ) ^ 2) ≤ p₀ := by
    dsimp only [p₀, π]
    rw [operational_class_mass]
    have hmass := (TypeMassLowerBounds.good_type_mass_bounds
      r o₁ o₂ q w hn hq hgood).2.1
    have hcast := (Rat.cast_le (K := ℝ)).mpr hmass
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hcast
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hp₀ : 0 < p₀ := (div_pos (by norm_num) (by positivity)).trans_le hp
  let κ := fun state next : PairedSet n =>
    exchangeProposal n hn state next * min (π state) (π next)
  have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
    mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
      (le_min (π.coe_nonneg state) (π.coe_nonneg next))
  have hpotential : potentialEnergy κ H = E := rfl
  let R := 2 * (n : ℝ) ^ 2 * E / p₀
  choose a b hlarge using (fun i k : Fin n => large_pair_event π i k)
  -- Choose the large two-pair event before asking for transport. Event
  -- selection and its conditional-mean variance bound are already proved.
  -- R is the paper's normalization D(H)/c₀ = 2n² E(H)/π(Ω₀).
  suffices hpaper :
      V ≤ (n : ℝ) * (1 + 8 * (n : ℝ)) * R ∧
      ∀ i k : Fin n, i ≠ k →
        (classMean π H (.defect i k) -
          eventMean π H (pairEvent i k (a i k) (b i k))) ^ 2 ≤
          (8 + 32 * (n : ℝ)) * R by
    obtain ⟨htrans, htransport⟩ := hpaper
    have hdef (i k : Fin n) (hik : i ≠ k) :
        (classMean π H (.defect i k) - m₀) ^ 2 ≤
          2 * (8 + 32 * (n : ℝ)) * R + 8 * V := by
      have hevent := large_pair_event_mean_bound π H i k (a i k) (b i k)
        hp₀ (hlarge i k)
      change (eventMean π H (pairEvent i k (a i k) (b i k)) - m₀) ^ 2 ≤
        4 * V at hevent
      have ht := htransport i k hik
      nlinarith [sq_nonneg (classMean π H (.defect i k) + m₀ -
        2 * eventMean π H (pairEvent i k (a i k) (b i k)))]
    have hV : 0 ≤ V := transversal_variance_nonneg π H
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let B := 2 * (8 + 32 * (n : ℝ)) * R + 8 * V
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hmass : (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) ≤ 1 := by
      have hpart := class_mass_partition π
      have hinvalid : classMass π .invalid = 0 :=
        operational_invalid_mass_zero r o₁ o₂ q w hq hw
      rw [hinvalid] at hpart
      have hpos := class_mass_nonneg π .transversal
      linarith
    have hdefsum : (∑ i : Fin n, ∑ k : Fin n,
        classMass π (.defect i k) * (classMean π H (.defect i k) - m₀) ^ 2) ≤ B := by
      calc
        _ ≤ ∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k) * B := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro k _
          by_cases hik : i = k
          · subst k
            have hz : classMass π (.defect i i) = 0 :=
              diagonal_class_mass_zero r o₁ o₂ q w hq hw i
            simp [hz]
          · exact mul_le_mul_of_nonneg_left (hdef i k hik)
              (class_mass_nonneg π (.defect i k))
        _ = (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) * B := by
          simp only [Finset.sum_mul]
        _ ≤ B := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hB
    have hmoment : (∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - m₀) ^ 2 else 0) = p₀ * V := by
      change _ = p₀ * ((∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - m₀) ^ 2 else 0) / p₀)
      field_simp [hp₀.ne']
    have hvar := observable_variance_decomposition r o₁ o₂ q w hq hw H m₀
    dsimp only at hvar
    rw [hmoment] at hvar
    have hweighted : p₀ * V ≤ V := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (class_mass_le_one π .transversal) hV
    calc
      Var π (observableProjection π H) ≤ p₀ * V +
          ∑ i : Fin n, ∑ k : Fin n,
            classMass π (.defect i k) * (classMean π H (.defect i k) - m₀) ^ 2 := hvar
      _ ≤ V + B := add_le_add hweighted hdefsum
      _ = 9 * V + 2 * (8 + 32 * (n : ℝ)) * R := by dsimp [B]; ring
      _ ≤ 9 * ((n : ℝ) * (1 + 8 * (n : ℝ)) * R) +
          2 * (8 + 32 * (n : ℝ)) * R :=
        add_le_add (mul_le_mul_of_nonneg_left htrans (by norm_num : (0 : ℝ) ≤ 9)) le_rfl
      _ = (72 * (n : ℝ) ^ 2 + 73 * (n : ℝ) + 16) * R := by ring
      _ ≤ 2000 * (n : ℝ) ^ 6 * E := observable_poincare_constant_bound n hn p₀ E hp hE
      _ = _ := by rw [hEeq]
  constructor
  · exact TransversalVarianceBound.transversal_variance_bound
      n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw hgood H
  · intro i k hik
    let A := pairEvent i k (a i k) (b i k)
    -- The paper constructs this current before choosing H. Its cost is
    -- measured using the normalized ideal-exchange conductances κ, so the
    -- conversion from the unnormalized coefficient is exactly 2n²/p₀.
    suffices hflow : ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) A),
        flowEnergy κ flow.current ≤ (8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀) by
      obtain ⟨flow, hcost⟩ := hflow
      have hb := flow.pairing_sq_le hκ
        ((8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀)) hcost H
      rw [conditional_mean_demand_pairing, hpotential] at hb
      change (classMean π H (.defect i k) - eventMean π H A) ^ 2 ≤ _
      calc
        _ ≤ ((8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀)) * E := hb
        _ = (8 + 32 * (n : ℝ)) * R := by dsimp [R]; ring
    exact DefectMeanExchangeFlow.defect_mean_exchange_flow
      n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw hgood
      i k hik (a i k) (b i k) (hlarge i k)
