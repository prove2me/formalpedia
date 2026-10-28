-- Prove2me | solution 1 for CountingMatroid.Analysis.PositiveTimeTraceMixing.pointwise_mixing_le_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:58:48.56995+00:00
-- url     : https://prove2.me/submissions/76c84305-0736-4945-ab81-6de1a7d2fc3f

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
import Theorems.Thm_Arlib_MarkovChains_Var_act_le
import Theorems.Thm_Arlib_MarkovChains_comp_stationary

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
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing
end CountingMatroid.Analysis.PositiveTimeTraceMixing
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
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Finite Markov chains: kernels, stationarity, reversibility

The basic objects of the spectral-independence development, in the form used
throughout: everything is finite and everything stays in `ℝ`.

* `FinDist Ω` — a probability distribution on a finite type.
* `FinKernel α β` — a row-stochastic matrix from `α` to `β`.  Deliberately
  *rectangular*: the up/down operators of the local-to-global machinery move
  between different level types, and it is much less painful to have one notion
  covering both them and ordinary chains.
* `FinChain Ω := FinKernel Ω Ω` — a Markov chain.
* `FinKernel.act` — the action `(P f)(x) = ∑ y, P x y * f y` on functions,
  which is the form in which transition matrices are actually used below.
* `FinKernel.push` — the action `(ν P)(y) = ∑ x, ν x * P x y` on distributions.
* `FinKernel.row` — the `x`-th row of a kernel, i.e. the law of one step started
  at `x`, packaged as a `FinDist`.
* `FinDist.dirac` and `FinKernel.push_dirac` — the point mass, and the identity
  `K.push δ_x = K.row x` that reconciles the two ways of saying "started at
  `x`".
* `Stationary`, `Reversible` — the two standing hypotheses of the theory.

`Reversible.stationary` records that detailed balance implies stationarity.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Distributions on a finite type -/



namespace FinDist

variable {Ω : Type*} [Fintype Ω]







theorem sum_coe (μ : FinDist Ω) : ∑ x, μ x = 1 := μ.p_sum











/-! ### The point mass -/

section Dirac

variable [DecidableEq Ω]





end Dirac

end FinDist

/-! ## Stochastic kernels -/





namespace FinKernel

variable {α β γ : Type*} [Fintype β]







































theorem comp_apply [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) (x : α) (z : γ) :
    (K ∘ₖ L) x z = ∑ y, K x y * L y z := rfl

/-- The action of a composite kernel is the composite of the actions. -/
theorem act_comp [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) (f : γ → ℝ) :
    (K ∘ₖ L).act f = K.act (L.act f) := by
  funext x
  simp only [act, comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring



@[simp] theorem act_id {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (f : Ω → ℝ) :
    (FinKernel.id Ω).act f = f := by
  funext x; simp [act, FinKernel.id]





theorem iter_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) (t : ℕ) :
    P.iter (t + 1) = P ∘ₖ P.iter t := rfl

theorem act_iter_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (t : ℕ) (f : Ω → ℝ) :
    (P.iter (t + 1)).act f = P.act ((P.iter t).act f) := by
  rw [iter_succ, act_comp]

end FinKernel



/-! ## Stationarity and reversibility -/

variable {Ω : Type*} [Fintype Ω]









end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability (FinDist FinKernel FinChain  Stationary Reversible)

end Arlib.MarkovChains

namespace Arlib.MarkovChains.FinDist

export Arlib.Probability.FinDist (p p_nonneg p_sum mk coe_eq coe_nonneg sum_coe
        )

end Arlib.MarkovChains.FinDist

namespace Arlib.MarkovChains.FinKernel

export Arlib.Probability.FinKernel (P P_nonneg P_sum mk coe_eq coe_nonneg sum_coe act
    
           comp
  comp_apply act_comp id act_id iter iter_zero iter_succ act_iter_succ)

end Arlib.MarkovChains.FinKernel

namespace Arlib.MarkovChains.Reversible

export Arlib.Probability.Reversible (stationary)

end Arlib.MarkovChains.Reversible

namespace Arlib.MarkovChains.Stationary



end Arlib.MarkovChains.Stationary

end

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `L²(μ)` functional calculus: expectation, inner product, variance

The functional-analytic side of the spectral-independence machinery is carried
out entirely in `L²(μ)` for a distribution `μ` on a finite type.  This module
sets up the three functionals used everywhere downstream and the identities
relating them.

* `Ex μ f` — expectation `∑ x, μ x * f x`.
* `ip μ f g` — inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`.
* `Var μ f` — variance `μ((f - μ(f))²)`.

The key identities, all elementary algebra over a finite sum:

* `Var_eq_ip_sub_sq` — `Var μ f = ⟪f, f⟫_μ - (μ f)²`;
* `Var_eq_pair` — the *pair form* `Var μ f = ½ ∑ x, ∑ y, μ x * μ y * (f x - f y)²`,
  which is what makes variance directly comparable to a Dirichlet form;
* `Var_eq_ip_self_of_mean_zero` — on mean-zero functions variance *is* the
  squared norm, which is why almost every proof below starts by centering `f`.

We also record that `ip μ` is a positive semidefinite symmetric bilinear form
(`isBilin_ip`, `ip_comm`, `ip_self_nonneg`), so that `psd_cauchy_schwarz` from
`Arlib.Probability.Bilinear` applies to it directly, together with the
lambda-form bilinearity lemmas (`ip_add_left`, `ip_smul_right`, …) that the
computations downstream actually rewrite with.

Two families of "support only" lemmas are here because *every* guarded-total
construction in the development produces a junk value off the support of the
averaging distribution: `Ex_congr_ae`, `Var_congr_ae` and `Ex_mono_of_ne_zero`
say that expectations, variances and their monotonicity see only the support.

Finally, `Ex_push_eq` and `ip_push_eq` transport `Ex` and `ip` along a
*rectangular* kernel; they involve no stationarity and are the bookkeeping that
makes the law of total variance (`Arlib.MarkovChains.Techniques.LevelVariance`)
a three-line
computation.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-! ## Expectation -/





























/-- Stationarity says exactly that the chain preserves expectations. -/
theorem Ex_act_of_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : Ex μ (P.act f) = Ex μ f := by
  simp only [Ex, FinKernel.act]
  calc ∑ x, μ x * ∑ y, P x y * f y
      = ∑ x, ∑ y, μ x * P x y * f y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, μ x * P x y * f y := Finset.sum_comm
    _ = ∑ y, μ y * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, h y]

/-! ## Inner product -/







theorem ip_self_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ ip μ f f :=
  Finset.sum_nonneg fun x _ => by
    have : μ x * f x * f x = μ x * (f x) ^ 2 := by ring
    rw [this]; exact mul_nonneg (μ.coe_nonneg x) (sq_nonneg _)











/-! ### Explicit bilinearity

`isBilin_ip` states bilinearity in terms of `Pi` addition and scalar
multiplication.  Most computations downstream are much smoother with the
arguments written as explicit lambdas, so we record that form too. -/











/-! ## Variance -/



theorem Var_apply (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ∑ x, μ x * (f x - Ex μ f) ^ 2 := rfl



/-- `Var_μ(f) = ⟪f, f⟫_μ - (μ f)²`. -/
theorem Var_eq_ip_sub_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ f f - (Ex μ f) ^ 2 := by
  have key : ∀ x, μ x * (f x - Ex μ f) ^ 2
      = μ x * f x * f x - 2 * Ex μ f * (μ x * f x) + (Ex μ f) ^ 2 * μ x := by
    intro x; ring
  rw [Var_apply, Finset.sum_congr rfl fun x _ => key x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [μ.sum_coe]
  simp only [ip, Ex, mul_one]
  ring









/-- On a mean-zero function, variance is the squared `L²(μ)` norm. -/
theorem Var_eq_ip_self_of_mean_zero {μ : FinDist Ω} {f : Ω → ℝ} (h : Ex μ f = 0) :
    Var μ f = ip μ f f := by
  rw [Var_eq_ip_sub_sq, h]; ring









/-! ## Pushforwards

Two bookkeeping identities for a *rectangular* kernel `K : α → β`, both plain
`Finset.sum_comm`.  They are what makes the law of total variance a three-line
computation. -/

section Push

variable {α β : Type*} [Fintype α] [Fintype β]





end Push

/-! ## χ²-divergence -/













end FinDist

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability.FinDist (Ex       
        Ex_act_of_stationary
  ip   ip_self_nonneg     
       Var Var_apply 
  Var_eq_ip_sub_sq     Var_eq_ip_self_of_mean_zero
        
      )

end Arlib.MarkovChains

end

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







/-! ## Two-sided control of `⟪f, P f⟫_μ`

A stochastic kernel is a contraction on `L²(μ)`: taking `s = -1` above bounds
`⟪f, P f⟫_μ` from above by `⟪f, f⟫_μ`, and taking `s = 1` bounds it from below
by `-⟪f, f⟫_μ`.  These are the elementary substitutes for "all eigenvalues lie
in `[-1, 1]`". -/







/-! ## Symmetry and bilinearity -/











/-! ## The spectral gap -/







/-- On a mean-zero function the Poincaré inequality reads
`⟪f, P f⟫_μ ≤ (1 - γ) ⟪f, f⟫_μ`. -/
theorem ip_act_self_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hgap : SpectralGapAtLeast μ P γ) {f : Ω → ℝ} (hf : Ex μ f = 0) :
    ip μ f (P.act f) ≤ (1 - γ) * ip μ f f := by
  have h := hgap f
  rw [Var_eq_ip_self_of_mean_zero hf, dirichlet_apply] at h
  linarith

/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/



/-- **Two-sided spectral bound.**  For a PSD chain with spectral gap at least
`γ`, every mean-zero `f` satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`.

This is the hypothesis under which variance decays geometrically; see
`Arlib.MarkovChains.Techniques.SpectralGap`. -/
theorem ip_act_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hpsd : NonnegDefinite μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1)
    {f : Ω → ℝ} (hf : Ex μ f = 0) :
    |ip μ f (P.act f)| ≤ (1 - γ) * ip μ f f := by
  refine abs_le.mpr ⟨?_, ip_act_self_le_of_gap hgap hf⟩
  have h0 := hpsd f
  have hnn : 0 ≤ (1 - γ) * ip μ f f :=
    mul_nonneg (by linarith) (ip_self_nonneg μ f)
  linarith

end Arlib.MarkovChains

end

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# From the spectral gap to decay of variance

The Poincaré inequality of `Arlib.MarkovChains.Techniques.Dirichlet` bounds the
quadratic form `⟪f, P f⟫_μ`.  What the mixing arguments actually need is a bound
on the *norm* `⟪P f, P f⟫_μ`, i.e. on `‖P‖` rather than on the numerical range.
Textbooks pass between the two through the spectral theorem for self-adjoint
operators.  We do not: the passage is an elementary variational argument, and
this module carries it out.

* `AbsSpectralBound μ P c` — `|⟪f, P f⟫_μ| ≤ c ⟪f, f⟫_μ` for every mean-zero
  `f`.  This is the *absolute* spectral gap in variational clothing: `c` plays
  the role of `λ* = max{λ₂, |λ_N|}`.
* `absSpectralBound_of_gap` — a positive semidefinite chain with spectral gap at
  least `γ` satisfies `AbsSpectralBound μ P (1 - γ)`.  PSD-ness is exactly what
  rules out the eigenvalue near `-1`, which is why the monograph notes that for
  the Glauber dynamics the gap and the absolute gap coincide.
* `ip_act_sq_le` — **the operator bound**: `AbsSpectralBound μ P c` upgrades to
  `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ` on mean-zero `f`.  The proof evaluates the
  hypothesis at the two test functions `f ± t · P f`, subtracts (the `P²` terms
  cancel), and reads off the discriminant of the resulting nonnegative quadratic
  in `t` — the same discriminant trick that gives `psd_cauchy_schwarz`, and
  again no eigenvalue is involved.
* `Var_act_le`, `Var_iter_le` — `Var_μ(P^t f) ≤ c^{2t} Var_μ(f)`.
* `relDensity_push`, `chiSq_push_le`, `chiSq_iter_le` — the same decay
  transported to the χ²-divergence, which is the quantity that converts into a
  mixing-time bound: for a reversible chain the relative density evolves by the
  chain acting on functions, `ν P / μ = P (ν / μ)`, so `χ²` contracts by `c²` a
  step.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The action of a kernel on an affine combination -/



/-! ## The absolute spectral bound -/





/-- **A positive semidefinite chain with spectral gap `γ` has absolute spectral
bound `1 - γ`.**  This is where PSD-ness earns its keep: the Poincaré inequality
alone controls only the top of the spectrum, and positive semidefiniteness is
the elementary substitute for "no eigenvalue near `-1`". -/
theorem absSpectralBound_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hpsd : NonnegDefinite μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1) :
    AbsSpectralBound μ P (1 - γ) := fun _ hf => ip_act_le_of_gap hpsd hgap hγ hf

/-! ## The operator bound

The numerical-range bound `|⟪f, P f⟫| ≤ c ⟪f, f⟫` upgrades to the norm bound
`⟪P f, P f⟫ ≤ c² ⟪f, f⟫`.  Evaluate the hypothesis at `f + t · P f` and at
`f - t · P f` and subtract: the terms involving `P²` cancel, leaving

  `4 t ⟪P f, P f⟫ ≤ 2c ⟪f, f⟫ + 2c t² ⟪P f, P f⟫`  for every real `t`,

a nonnegative quadratic in `t` whose discriminant must be `≤ 0`. -/



/-! ## Decay of variance -/



section Iterate

variable [DecidableEq Ω]

/-- **Geometric decay of variance.**  `Var_μ(P^t f) ≤ (c²)^t Var_μ(f)`.

This is the quantitative content of "the chain forgets its starting point": the
`L²(μ)` distance to equilibrium shrinks by a factor `c` each step. -/
theorem Var_iter_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) (f : Ω → ℝ) (t : ℕ) :
    Var μ ((P.iter t).act f) ≤ (c ^ 2) ^ t * Var μ f := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ]
      calc Var μ (P.act ((P.iter t).act f))
          ≤ c ^ 2 * Var μ ((P.iter t).act f) := Var_act_le hrev hc _
        _ ≤ c ^ 2 * ((c ^ 2) ^ t * Var μ f) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (c ^ 2) ^ (t + 1) * Var μ f := by ring

/-- Variance decay for a positive semidefinite chain, stated directly in terms of
the spectral gap: `Var_μ(P^t f) ≤ (1 - γ)^{2t} Var_μ(f)`. -/
theorem Var_iter_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpsd : NonnegDefinite μ P)
    (hgap : SpectralGapAtLeast μ P γ) (hγ1 : γ ≤ 1) (f : Ω → ℝ) (t : ℕ) :
    Var μ ((P.iter t).act f) ≤ ((1 - γ) ^ 2) ^ t * Var μ f :=
  Var_iter_le hrev (absSpectralBound_of_gap hpsd hgap hγ1) f t

end Iterate

/-! ## Decay of the χ²-divergence

Variance decay becomes a statement about *distributions* through the relative
density.  For a reversible chain the density of the pushed-forward distribution
is the chain acting on the density: `ν P / μ = P (ν / μ)`.  This is detailed
balance read in the other direction, and it is what makes `χ²` — a functional of
distributions — decay at the rate governing `L²(μ)` functions. -/





end Arlib.MarkovChains

end

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Comparison of chains, and the gap of an iterate

Almost no spectral gap is ever computed.  What one does instead is *transfer* a
gap: take a chain whose Poincaré constant is known, show that the chain one
actually cares about has a Dirichlet form at least comparable to it, and read
off a gap for free.  This is the comparison method, and it is the reason a
module in `Chains/` can bound a gap without ever evaluating a sum.

The method is completely elementary here, and that is the point of the pair form
`dirichlet_self_eq_pair`: both Dirichlet forms are finite sums
`½ ∑_{x,y} μ(x) · K(x,y) · (f x - f y)²` over the *same* index set with the
*same* weights `μ(x) (f x - f y)²`, so domination of one form by the other is a
term-by-term inequality between the kernels — and only off the diagonal, since
the diagonal terms carry the factor `(f x - f x)² = 0`.

* `DirichletLe μ P Q A` — `ℰ_P(f) ≤ A · ℰ_Q(f)` for every `f`; "`Q` dominates
  `P` with constant `A`".  Reflexive with `A = 1`, and composes by multiplying
  constants.
* `spectralGapAtLeast_of_dirichletLe` — **the comparison theorem**: if `Q`
  dominates `P` with constant `A > 0` and `P` has gap `γ`, then `Q` has gap
  `γ / A`.  It is `Q` that inherits the gap, because `Q`'s Dirichlet form is the
  larger one.
* `dirichletLe_of_entrywise` — **the practical criterion**: for `μ` stationary
  for both chains, an entrywise bound `P(x,y) ≤ A · Q(x,y)` *off the diagonal*
  suffices.  The diagonal is genuinely irrelevant, which is what makes the
  criterion usable: laziness, holding probabilities and self-loops may be
  changed at will.
* `absSpectralBound_mono`, `comp_reversible`, `iter_reversible` — the small API
  needed to iterate.
* `absSpectralBound_iter` — **the absolute spectral bound of an iterate**:
  `AbsSpectralBound μ P c` with `0 ≤ c` gives `AbsSpectralBound μ (P^t) (c^t)`,
  and hence `spectralGapAtLeast_iter`, the Poincaré inequality for `P^t` with
  constant `1 - c^t`.  The proof runs the operator bound `ip_act_sq_le` `t`
  times to control `‖P^t f‖`, then applies Cauchy–Schwarz once; no eigenvalue,
  and in particular no "the eigenvalues of `P^t` are the `t`-th powers of those
  of `P`", is involved.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Domination of Dirichlet forms -/











/-! ## Transfer of the spectral gap

The comparison theorem itself, which is one line of division once the two
Poincaré inequalities are lined up. -/



/-! ## The entrywise criterion

In practice one never verifies `DirichletLe` directly; one compares the two
transition matrices entry by entry.  The pair form turns the comparison of the
forms into exactly that, and only off the diagonal: the terms with `x = y` carry
the factor `(f x - f x)² = 0` on both sides. -/







/-! ## Monotonicity of the absolute spectral bound -/



/-! ## Stationarity and reversibility of composites

Stationarity passes to any composite.  Reversibility does *not*: detailed balance
for `P ∘ₖ Q` unwinds to `μ(x) (PQ)(x,z) = μ(z) (QP)(z,x)`, so one needs the two
chains to commute.  They do in the case that matters, `P` with its own iterate,
which is `FinKernel.iter_succ'`. -/





section Iterate

variable [DecidableEq Ω]

/-- The identity kernel preserves every distribution. -/
theorem id_stationary (μ : FinDist Ω) : Stationary μ (FinKernel.id Ω) := by
  intro y; simp [FinKernel.id]



/-- Stationarity passes to every iterate. -/
theorem iter_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) (t : ℕ) :
    Stationary μ (P.iter t) := by
  induction t with
  | zero => exact id_stationary μ
  | succ t ih => exact comp_stationary h ih



/-! ## The absolute spectral bound of an iterate

The `L²(μ)` norm of `P^t f` is controlled by running the operator bound
`ip_act_sq_le` once per step; the numerical range of `P^t` then follows from a
single application of Cauchy–Schwarz.  This replaces the textbook step "the
eigenvalues of `P^t` are the `t`-th powers of those of `P`". -/







end Iterate

end Arlib.MarkovChains

end
set_option autoImplicit false

/-!
Pointwise finite-chain mixing from the library's variance contraction. A
uniform lower bound on the stationary law converts squared-error decay into
the factor-two endpoint density needed for the warm restart argument.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing
end CountingMatroid.Analysis.PositiveTimeTraceMixing
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceMixing

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: A spectral contraction smaller than the minimum stationary
mass gives pointwise factor-two domination of every row after k steps.
TEXLINE: main.tex:1070-1079,1219-1223 -/
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : FinDist Ω) (P : FinChain Ω) (hrev : Reversible μ P)
    (hpsd : NonnegDefinite μ P) (γ m : ℝ)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1)
    (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (k : ℕ)
    (hdecay : (1 - γ) ^ k ≤ m) (x y : Ω) : P.iter k x y ≤ 2 * μ y := by
  let f : Ω → ℝ := fun z => if z = y then 1 else 0
  have hfmean : Ex μ f = μ y := by simp [Ex, f]
  have hfvar : Var μ f ≤ μ y := by
    rw [Var_eq_ip_sub_sq, hfmean]
    have hself : ip μ f f = μ y := by simp [ip, f]
    rw [hself]
    nlinarith [sq_nonneg (μ y)]
  have hact : (P.iter k).act f x = P.iter k x y := by simp [FinKernel.act, f]
  have hmean : Ex μ ((P.iter k).act f) = μ y := by
    rw [Ex_act_of_stationary (iter_stationary hrev.stationary k), hfmean]
  have hpoint : μ x * (P.iter k x y - μ y) ^ 2 ≤ Var μ ((P.iter k).act f) := by
    rw [Var_apply]
    have hs := Finset.single_le_sum (s := Finset.univ) (a := x)
      (f := fun z => μ z * ((P.iter k).act f z - Ex μ ((P.iter k).act f)) ^ 2)
      (fun z _ => mul_nonneg (μ.coe_nonneg z) (sq_nonneg _)) (Finset.mem_univ x)
    simpa only [hmean, hact] using hs
  have hvar := Var_iter_le_of_gap hrev hpsd hgap hγ f k
  have hpow : ((1 - γ) ^ 2) ^ k = ((1 - γ) ^ k) ^ 2 := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [hpow] at hvar
  have hpow0 : 0 ≤ (1 - γ) ^ k := pow_nonneg (by linarith) k
  have hdecay2 : ((1 - γ) ^ k) ^ 2 ≤ m ^ 2 := by
    nlinarith
  have hminprod : m ^ 2 ≤ μ x * μ y := by
    have hprod := mul_le_mul (hmin x) (hmin y) hm.le (μ.coe_nonneg x)
    nlinarith
  have hpoint2 : μ x * (P.iter k x y - μ y) ^ 2 ≤ μ x * (μ y) ^ 2 := by
    calc
      _ ≤ ((1 - γ) ^ k) ^ 2 * Var μ f := hpoint.trans hvar
      _ ≤ ((1 - γ) ^ k) ^ 2 * μ y :=
        mul_le_mul_of_nonneg_left hfvar (sq_nonneg _)
      _ ≤ m ^ 2 * μ y := mul_le_mul_of_nonneg_right hdecay2 (μ.coe_nonneg y)
      _ ≤ (μ x * μ y) * μ y := mul_le_mul_of_nonneg_right hminprod (μ.coe_nonneg y)
      _ = _ := by ring
  have hx : 0 < μ x := hm.trans_le (hmin x)
  have he := le_of_mul_le_mul_left hpoint2 hx
  have habs : |P.iter k x y - μ y| ≤ μ y := by
    apply (sq_le_sq₀ (abs_nonneg _) (μ.coe_nonneg y)).mp
    simpa only [sq_abs] using he
  linarith [(abs_le.mp habs).2]
