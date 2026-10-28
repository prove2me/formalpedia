-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduledTransversalTraceMixing.scheduled_transversal_trace_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:28:49.854252+00:00
-- url     : https://prove2.me/submissions/de57253e-856d-47aa-839b-5d39db96cd69

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
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
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
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
import Definitions.Def_CountingMatroid_Analysis_TransversalTraceSpectralGap
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Field
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
import Theorems.Thm_CountingMatroid_Analysis_IdealChainNonnegDefinite_exchange_proposal_holding
import Theorems.Thm_CountingMatroid_Analysis_IdealChainNonnegDefinite_nonnegDefinite_of_holding
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceChain_trace_chain_iter
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceHarmonic_uncappedReturn_reversible
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceMixing_pointwise_mixing_le_of_gap
import Theorems.Thm_CountingMatroid_Analysis_TransversalTraceSpectralGap_transversal_trace_spectral_gap

namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing
end CountingMatroid.Analysis.ScheduledTransversalTraceMixing
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing
end CountingMatroid.Analysis.PositiveTimeTraceMixing
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace CountingMatroid.Analysis.IdealChainNonnegDefinite
end CountingMatroid.Analysis.IdealChainNonnegDefinite
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
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
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
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
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
section


set_option autoImplicit false

/-!
Finite positive-time return kernels. Each row counts only returns completed
within the horizon; missing mass is retained as abort mass. The construction
uses the library's zero-time hitting recursion only after an initial transition,
so a starting transversal is not mistaken for an immediate return. Stationarity
also proves almost-sure return from positive-mass target states. This module
does not claim the spectral estimate or finite-bit operational coupling.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceKernel

open Arlib.Probability Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]





































/-- INTERNAL: Capping loses mass pointwise relative to the uncapped return.
TEXLINE: main.tex:1207-1212 -/
theorem returnWithin_le_uncapped (P : FinChain Ω) (A : Finset Ω)
    (k : ℕ) (x y : Ω) :
    (returnWithin P A k).entry x y ≤ (uncappedReturn P A).entry x y :=
  le_ciSup (returnWithin_bddAbove P A x y) k















end CountingMatroid.Analysis.PositiveTimeTraceKernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · built finite and uncapped positive-time return subkernels, their row budgets and cap domination; stationarity proves full return mass at positive-mass target states. The scheduled spectral estimate and finite-bit coupling belong to the consuming children.
-/


end

section


set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]



























/-- PAPER: main.tex:1058-1059
A positive-time return includes each one-step transition inside the target,
so in particular the trace inherits every underlying holding probability. -/
theorem uncappedReturn_ge_transition (P : FinChain Ω) (A : Finset Ω)
    (x y : Ω) (hy : y ∈ A) :
    P x y ≤ (uncappedReturn P A).entry x y := by
  apply le_trans ?_ (returnWithin_le_uncapped P A 1 x y)
  change P x y ≤ ∑ z, P x z * (targetIdentity A).entry z y
  have heq : (∑ z, P x z * (targetIdentity A).entry z y) = P x y := by
    have hcell (z : Ω) : P x z * (targetIdentity A).entry z y =
        if z = y then P x y else 0 := by
      by_cases hzy : z = y
      · subst z; simp [targetIdentity, hy]
      · simp [targetIdentity, hzy]
    simp [hcell]
  exact heq.ge

end CountingMatroid.Analysis.PositiveTimeTraceHarmonic

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · monotone hitting limits give the harmonic residual and boundary energy identity; symmetry proves trace detailed balance, and one-step returns preserve holding probabilities. No almost-sure-hitting assumption on zero-weight states is needed.
-/

end

section


set_option autoImplicit false

/-!
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]







/-- PAPER: main.tex:1033-1037,1056-1058
The concrete trace is reversible with its conditional stationary law. -/
theorem trace_chain_reversible (μ : FinDist Ω) (P : FinChain Ω)
    (hrev : Reversible μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) (hA : 0 < ∑ x ∈ A, μ x) :
    Reversible (traceLaw μ A hA) (traceChain μ P hrev.stationary A hμ) := by
  intro x y
  change (μ x / _) * (uncappedReturn P A).entry x y =
    (μ y / _) * (uncappedReturn P A).entry y x
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    uncappedReturn_reversible μ P hrev A x y x.property y.property]

/-- PAPER: main.tex:1033-1037,1058-1059
The concrete trace inherits half-laziness from the underlying chain. -/
theorem trace_chain_holding (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) (hhold : ∀ x, (1 / 2 : ℝ) ≤ P x x)
    (x : A) : (1 / 2 : ℝ) ≤ traceChain μ P hst A hμ x x :=
  (hhold x).trans (uncappedReturn_ge_transition P A x x x.property)





end CountingMatroid.Analysis.PositiveTimeTraceChain

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · constructed the stochastic trace on the boundary subtype, its reversible conditional law, holding probability, exact finite-power bridge, and harmonic-extension energy scaling.
-/

end

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Metropolis–Hastings chain

The general theory in `Arlib.MarkovChains.Techniques` is stated for a chain `P`
together with a distribution `μ` reversible for it.  This module supplies such
pairs.  Given an arbitrary *symmetric* proposal chain `Q` and an arbitrary
target `μ` of full support, the Metropolis construction manufactures a chain
that is reversible with respect to `μ`: propose a move `x → y` according to
`Q`, and accept it with probability `min 1 (μ y / μ x)`.  The acceptance ratio
is exactly what is needed to turn the symmetry of `Q` into detailed balance for
`μ`, because `μ x * min 1 (μ y / μ x) = min (μ x) (μ y)` is already symmetric
in `x` and `y`.  That one line is the whole idea; everything else is
bookkeeping to check that the resulting matrix is stochastic.

This is why the construction belongs in the `Chains/` half of the library: it
is the standard way to *produce* a reversible chain with a prescribed
stationary distribution, and hence the source of the objects the spectral
theory in `Techniques/` talks about.

* `mhRate` — the off-diagonal transition rate `Q x y * min 1 (μ y / μ x)`.
* `mhRate_nonneg`, `mhRate_le_proposal` — the two elementary bounds.
* `mhRate_detailed_balance` — `μ x * mhRate μ Q x y = Q x y * min (μ x) (μ y)`,
  the identity that does all the work.
* `mhStay` — the holding probability `1 - ∑ z ≠ x, mhRate μ Q x z`, together
  with `sum_erase_mhRate_le_one` and `mhStay_nonneg`.
* `metropolis` — the Metropolis chain itself, as a `FinChain Ω`.
* `metropolis_reversible` — **the main theorem**: for `μ` of full support and
  `Q` symmetric, `μ` satisfies detailed balance for `metropolis μ Q`.
* `metropolis_stationary` — the resulting stationarity statement.
* `uniformProposal` and `metropolis_uniform_reversible` — a concrete
  instantiation with the uniform proposal, to exhibit the interface in use.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The acceptance rate -/













/-! ## The holding probability -/

section Stay

variable [DecidableEq Ω]







end Stay

/-! ## The Metropolis chain -/

section Chain

variable [DecidableEq Ω]





/-- On the diagonal the Metropolis chain holds. -/
@[simp] theorem metropolis_apply_self (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    metropolis μ Q x x = mhStay μ Q x := if_pos rfl





end Chain

/-! ## A concrete instance: the uniform proposal -/

section Uniform

variable (Ω)
variable [Nonempty Ω]







variable {Ω}





end Uniform

end Arlib.MarkovChains

end

section


set_option autoImplicit false

/-!
The schedule supplies pointwise factor-two domination for the concrete
uncapped positive-time transversal trace, from every transversal start.
This is an analytical estimate; it does not identify the finite-tape restart law.
-/
namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.TransversalTraceSpectralGap
open CountingMatroid.Analysis.PositiveTimeTraceChain
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Evaluate a transversal weight independently of its multipliers.
TEXLINE: main.tex:721-728 -/
private theorem transversal_weight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (x : PairedSet n)
    (hx : x ∈ transversalSet n) :
    stateWeight r o₁ o₂ q w x =
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ x).val) := by
  have hk : (classifyState x).val = .transversal := by
    simpa only [transversalSet, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  simp [stateWeight, hk, weightOfKind, CountingMatroid.Model.Operations.natSub,
    CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support]

/-- INTERNAL: The conditional trace law is the transversal weight divided
by its partition sum, and is independent of the defect multipliers.
TEXLINE: main.tex:1023-1037,1215-1218 -/
private theorem trace_law_formula {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < w a) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let A := transversalSet n
    (∑ x ∈ A, π x) = (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) /
      (normalizer r o₁ o₂ q w : ℝ) := by
  classical
  dsimp only
  have hid := (stationary_mean_identities r o₁ o₂ q 1 w hq hw).2.1
  have hc := congrArg (fun a : ℚ => (a : ℝ)) hid
  simp only [typeMean, Rat.cast_div, Rat.cast_sum, apply_ite, Rat.cast_zero] at hc
  simpa only [transversalSet, Finset.sum_filter, operationalLaw, ite_div, zero_div,
    Finset.sum_div] using hc

/-- INTERNAL: The explicit trace length suppresses the spectral contraction
below the paper's uniform lower mass bound.
TEXLINE: main.tex:1215-1223 -/
private theorem schedule_trace_decay (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    (1 - 1 / (18 * (n : ℝ) ^ 4)) ^ s.τ ≤ (1 / 2 : ℝ) ^ (n * (s.L + 1)) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let b := 18 * n ^ 4
  let N := n * (s.L + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : (b : ℝ) = 18 * (n : ℝ) ^ 4 := by simp [b]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase0 : 0 ≤ 1 - 1 / (b : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hb1
    exact sub_nonneg.mpr (by simpa only [div_one] using this)
  have hbase1 : 1 - 1 / (b : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have hblock : (1 - 1 / (b : ℝ)) ^ b ≤ (1 / 2 : ℝ) :=
    (Real.one_sub_div_pow_le_exp_neg (n := b) (t := 1) hb1).trans
      Real.exp_neg_one_lt_half.le
  have hτ : s.τ = 20 * n ^ 4 * (N + 2) := by rfl
  have hlength : b * N ≤ s.τ := by
    rw [hτ]
    dsimp [b]
    nlinarith
  calc
    _ = (1 - 1 / (b : ℝ)) ^ s.τ := by rw [hbr]
    _ ≤ (1 - 1 / (b : ℝ)) ^ (b * N) :=
      pow_le_pow_of_le_one hbase0 hbase1 hlength
    _ = ((1 - 1 / (b : ℝ)) ^ b) ^ N := pow_mul _ _ _
    _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_left₀ (pow_nonneg hbase0 _) hblock _



end CountingMatroid.Analysis.ScheduledTransversalTraceMixing

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · normalized the concrete boundary law, bounded every transversal mass below by 2^(-n*(L+1)), and applied spectral contraction at the actual scheduled trace length. No finite-tape coupling is assumed.
-/

end
set_option autoImplicit false

/-!
The schedule supplies pointwise factor-two domination for the concrete
uncapped positive-time transversal trace, from every transversal start.
This is an analytical estimate; it does not identify the finite-tape restart law.
-/
namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing
end CountingMatroid.Analysis.ScheduledTransversalTraceMixing
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduledTransversalTraceMixing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.TransversalTraceSpectralGap
open CountingMatroid.Analysis.PositiveTimeTraceChain
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- PAPER: main.tex:1215-1223,1242-1244
After the scheduled number of positive-time trace transitions, every starting
transversal has endpoint density at most twice the current transversal law. -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (w : Multipliers n) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hw : ∀ a, 0 < w a)
    (hgood : ∀ a,
      (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) a) / 4 ≤ w a ∧
      w a ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) a))
    (x y : PairedSet n) (hx : x ∈ transversalSet n) (hy : y ∈ transversalSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    let P := idealChain r o₁ o₂ (s.ρ ^ j) w hn hq hw
    (PositiveTimeTraceKernel.iterate
      (PositiveTimeTraceKernel.uncappedReturn P (transversalSet n)) s.τ).entry x y ≤
      2 * ((((s.ρ ^ j) ^
        (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ y).val) : ℚ) : ℝ) /
        (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) : ℝ)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hρ := AnnealingPartitionDrift.schedule_power_lower n p hn
  have hq : 0 < s.ρ ^ j := pow_pos hρ.1 j
  have hq1 : s.ρ ^ j ≤ 1 := pow_le_one₀ hρ.1.le hρ.2.1
  let q := s.ρ ^ j
  let π := operationalLaw r o₁ o₂ q w hq hw
  let P := idealChain r o₁ o₂ q w hn hq hw
  let A := transversalSet n
  have hCq : 0 < TransversalPartition.partitionSum r o₁ o₂ q :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hC : (0 : ℝ) < (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    exact_mod_cast hCq
  have hZ : (0 : ℝ) < (normalizer r o₁ o₂ q w : ℝ) := by
    exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  have hπ : ∀ z ∈ A, 0 < π z := by
    intro z hz
    change 0 < (stateWeight r o₁ o₂ q w z : ℝ) / _
    rw [transversal_weight r o₁ o₂ q w z hz]
    exact div_pos (by exact_mod_cast pow_pos hq _) hZ
  have hA : 0 < ∑ z ∈ A, π z := by
    rw [trace_law_formula r o₁ o₂ q w hq hw]
    exact div_pos hC hZ
  let μ := traceLaw π A hA
  let Q := traceChain π P (ideal_chain_stationary r o₁ o₂ q w hn hq hw) A hπ
  have hμ (z : A) : μ z =
      ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ) /
      (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    change (π z / (∑ z ∈ A, π z)) = _
    rw [trace_law_formula r o₁ o₂ q w hq hw]
    change ((stateWeight r o₁ o₂ q w z : ℝ) / _) / _ = _
    rw [transversal_weight r o₁ o₂ q w z z.property]
    field_simp
  let N := n * (s.L + 1)
  let m := (1 / 2 : ℝ) ^ N
  have hm : 0 < m := by dsimp [m]; positivity
  have hmin : ∀ z : A, m ≤ μ z := by
    intro z
    rw [hμ]
    have hCupper : (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) ≤ (2 : ℝ) ^ n := by
      have hcq : TransversalPartition.partitionSum r o₁ o₂ q ≤ (2 : ℚ) ^ n := by
        calc
          _ ≤ ∑ _z : Finset (Fin n), (1 : ℚ) :=
            Finset.sum_le_sum fun z _ => pow_le_one₀ hq.le hq1
          _ = _ := by simp
      exact_mod_cast hcq
    have hWlower : (1 / 2 : ℝ) ^ j ≤
        ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ) := by
      have hpow : (1 / 2 : ℚ) ^ j ≤ q ^ n := by
        change (1 / 2 : ℚ) ^ j ≤ (s.ρ ^ j) ^ n
        rw [← pow_mul, Nat.mul_comm j n, pow_mul]
        exact pow_le_pow_left₀ (by norm_num) hρ.2.2 j
      have hd : n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val ≤ n :=
        Nat.sub_le _ _
      have hfinal := hpow.trans (pow_le_pow_of_le_one hq.le hq1 hd)
      change (1 / 2 : ℝ) ^ j ≤
        (((s.ρ ^ j) ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ)
      have hh := (Rat.cast_le (K := ℝ)).mpr hfinal
      norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
      simpa only [Rat.cast_pow] using hh
    have hNj : n + j ≤ N := by
      have hmL := Nat.le_mul_of_pos_left s.L hn
      dsimp [N]
      nlinarith
    calc
      m ≤ (1 / 2 : ℝ) ^ (n + j) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hNj
      _ = (1 / 2 : ℝ) ^ j / (2 : ℝ) ^ n := by
        rw [pow_add, div_pow, one_pow]
        ring
      _ ≤ _ := div_le_div₀ (by positivity) hWlower hC hCupper
  have hrev : Reversible π P := metropolis_reversible_zero_weights π
    (exchangeProposal n hn) (exchange_proposal_symmetric n hn)
  have hQrev : Reversible μ Q := trace_chain_reversible π P hrev A hπ hA
  have hholding : ∀ z, (1 / 2 : ℝ) ≤ P z z := by
    intro z
    have hlazy := IdealChainNonnegDefinite.exchange_proposal_holding n hn z
    have hsum : exchangeProposal n hn z z +
        ∑ v ∈ Finset.univ.erase z, exchangeProposal n hn z v = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ z)]
      exact (exchangeProposal n hn).sum_coe z
    have hle : (∑ v ∈ Finset.univ.erase z, mhRate π (exchangeProposal n hn) z v) ≤
        ∑ v ∈ Finset.univ.erase z, exchangeProposal n hn z v :=
      Finset.sum_le_sum fun v _ => mhRate_le_proposal π (exchangeProposal n hn) z v
    change (1 / 2 : ℝ) ≤ metropolis π (exchangeProposal n hn) z z
    rw [metropolis_apply_self, mhStay]
    linarith
  have hpsd : NonnegDefinite μ Q := IdealChainNonnegDefinite.nonnegDefinite_of_holding
    μ Q hQrev.stationary (trace_chain_holding π P hrev.stationary A hπ hholding)
  have hgap := transversal_trace_spectral_gap n r M₁ M₂ o₁ o₂ q w hn
    hfull hr h₁ h₂ hq hq1 hw hgood hπ hA
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : 1 / (18 * (n : ℝ) ^ 4) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 18 * (n : ℝ) ^ 4)).mpr
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hnreal 4
    norm_num at this
    linarith
  have hmix := PositiveTimeTraceMixing.pointwise_mixing_le_of_gap μ Q hQrev hpsd
    (1 / (18 * (n : ℝ) ^ 4)) m hgap hγ hm hmin s.τ
    (schedule_trace_decay n p hn) ⟨x, hx⟩ ⟨y, hy⟩
  rw [trace_chain_iter π P hrev.stationary A hπ, hμ] at hmix
  exact hmix
