-- Prove2me | solution 1 for ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T04:43:27.822348+00:00
-- url     : https://prove2.me/submissions/dfed03be-263c-482d-a55b-f57577e3a120

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke110
import Theorems.Thm_GlobalClassFieldTheory_Reciprocity_chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
import Theorems.Thm_chosenFinitePlaceLocalizedResidueEquiv_equivariant

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_IntegerRingComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The finite completion and its defining prime ideal have residue fields
of the same cardinality. -/
theorem finitePlaceCompletion_residueField_card
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card 𝓀[ChosenFinitePlaceBaseCompletion (K := K) v] =
      Nat.card (𝓞 K ⧸ v.asIdeal) :=
  Nat.card_congr (finitePlaceIdealResidueEquivCompletion v).symm.toEquiv
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ArithmeticUnramifiedPrimeArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Arithmetic Frobenius at an unramified finite place

The pre-existing local class-formation coordinate has geometric
Frobenius normalization.  This file supplies the canonical prime Artin
element used in the ideal-theoretic formulation: the ordinary normalized
prime idèle maps to arithmetic Frobenius.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- At an unramified chosen finite place, the arithmetic prime Artin
element really is the global decomposition-group transport of local
arithmetic Frobenius. The local input has valuation `-1` in the
construction's convention, and arithmetic global reciprocity inverts
that geometric local Artin value. -/
theorem arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hunram := by
  let w := chosenFinitePlaceExtension (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  have hgeometric :
      Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x =
        (chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
    change Reciprocity.finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x = _
    rw [Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor]
    change Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (Reciprocity.finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) = _
    rw [Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
      (K := K) (L := L) v hunram, map_inv]
    rfl
  rw [arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin,
    Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply]
  rw [hgeometric, inv_inv]

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldMaximalSubextension
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
private noncomputable def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GroupTheory_Transfer_Witt
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Witt's transfer theorem

For a finitely generated group `G` with finite abelianization, the transfer
from `G / G'` to `G' / G''` is trivial.

The proof follows Witt's group-ring argument. This file first
constructs the required right Fox coefficients directly from free words; no
presentation relations are assumed as extra input.
-/

open scoped BigOperators Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace Witt

open Subgroup

variable {G : Type*} [Group G]

/-- Finite index of the commutator gives finiteness of the
abelianization. -/
noncomputable instance finiteAbelianizationOfFiniteIndex
    [FiniteIndex (commutator G)] :
    Finite (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _

end Witt
end Transfer
end GroupTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_RationalFiniteNormTransfer_FieldSpine
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerTopField_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Fixed-field instance spine for rational finite-norm transport

This leaf names the finite-dimensional, scalar-tower, number-field, Galois,
and quotient instances reused by the rational finite-norm transport modules.
The public dependent type aliases are compiled once here.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

namespace RationalFiniteNormTransferInternal

/-- The canonical absolute algebra structure on a rational relative fixed field. -/
@[reducible] noncomputable def absoluteAlgebra
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Algebra ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  inferInstance

end RationalFiniteNormTransferInternal


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_SmallHilbertTowerRealization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GroupTheory.Transfer.Witt.finiteAbelianizationOfFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Actual realization of the two-stage small Hilbert tower

The first small Hilbert class field is the actual finite abelian
subextension selected in `HilbertClassFieldRealization`.  Over its actual
fixed field, the closed finite-index small-Hilbert norm subgroup has a
finite Galois norm neighbourhood.  We embed that neighbourhood in the
rational separable closure compatibly with the already chosen first
stage.  Finite abelian classification then selects the second small
Hilbert class field over the literal first-stage subgroup.

The compatibility of the embedding is essential: an unrelated chosen
copy of the middle number field would produce a class field over a
conjugate closed subgroup rather than over the first-stage subgroup
itself.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open AlgebraicNumberTheory
open ClassFormation
open CyclicCohomology
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open RamificationTheory
open Reciprocity

/-- The ordinary idèle-class operations used by the two-stage transport,
fixed at the canonical principal-subgroup quotient. -/
@[instance_reducible]
private noncomputable def smallHilbertTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertTowerIdeleClassCommGroup

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_MathlibFrobeniusHilbertComparison
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Frobenius and Hilbert class fields implementation

This module supplies the implementation proofs for the compact public
statements in `ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields`.

The prime element exposed below is the arithmetic-normalized prime Artin
element.  Its residue action identifies it with Mathlib's arithmetic
Frobenius at every unramified finite prime.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

open NumberField IsDedekindDomain
open LocalFieldTheory
open scoped ValuativeRel

/-- In an abelian extension, Mathlib's chosen arithmetic Frobenius is
independent of the prime above a fixed base prime.  Mathlib chooses
conjugate lifts, and conjugacy is equality in the abelian Galois group. -/
theorem arithmeticFrobeniusAt_eq_of_liesOver
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hw' : w'.asIdeal.LiesOver v.asIdeal) :
    arithmeticFrobeniusAt (K := K) w =
      arithmeticFrobeniusAt (K := K) w' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L)
      w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over))
  calc
    arithmeticFrobeniusAt (K := K) w =
        τ * arithmeticFrobeniusAt (K := K) w * τ⁻¹ := by
      rw [IsMulCommutative.is_comm.comm τ
        (arithmeticFrobeniusAt (K := K) w), mul_assoc,
        mul_inv_cancel, mul_one]
    _ = arithmeticFrobeniusAt (K := K) w' := hτ

/-- At an unramified finite prime, the arithmetic-normalized prime Artin
element is Mathlib's arithmetic Frobenius, independently of the chosen prime
above the base prime. -/
theorem arithmeticPrimeArtin_eq_arithmeticFrobeniusAt_oai
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
      arithmeticFrobeniusAt (K := K) w := by
  classical
  let w₀ := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let P : Ideal (𝓞 K) := v.asIdeal
  let Q : Ideal (𝓞 L) := W.asIdeal
  let G := L ≃ₐ[K] L
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : Algebra C E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w₀
  have hW : Q.LiesOver P :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w₀
  let : Q.LiesOver P := hW
  let : w.asIdeal.LiesOver P := hw
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hEw : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : Q.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Q w.asIdeal G
  have hunramQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)
  have hChosen : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v :=
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunramQ
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hChosen
  let vK := HeightOneSpectrum.adicAbv K v
  let eD : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 ≃*
      (E ≃ₐ[C] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w₀
  let f : E ≃ₐ[C] E := arithmeticFrobeniusOfUnramifiedValuation C E
  let δ : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 :=
    eD.symm f
  have heDδ : eD δ = f := eD.apply_symm_apply f
  have hδ : (δ : G) =
      GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen := by
    change (eD.symm f : G) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w₀ f
    rfl
  let e : (𝓞 L ⧸ Q) ≃+* 𝓀[E] :=
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
  have hCard : Nat.card 𝓀[C] =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    rw [finitePlaceCompletion_residueField_card (K := K) v,
      hW.over.symm]
  have hResidue (x : 𝓞 L) :
      Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x) =
        (Ideal.Quotient.mk Q x) ^
          Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    apply e.injective
    calc
      e (Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x)) =
          LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            (eD δ) (e (Ideal.Quotient.mk Q x)) :=
        chosenFinitePlaceLocalizedResidueEquiv_equivariant
          (K := K) (L := L) v δ x
      _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            f (e (Ideal.Quotient.mk Q x)) := by
        simp only [heDδ]
      _ = (e (Ideal.Quotient.mk Q x)) ^ Nat.card 𝓀[C] :=
        galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
          C E (e (Ideal.Quotient.mk Q x))
      _ = e ((Ideal.Quotient.mk Q x) ^
            Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) := by
        exact (congrArg
          (fun n : ℕ => (e (Ideal.Quotient.mk Q x)) ^ n) hCard).trans
          (map_pow e (Ideal.Quotient.mk Q x) _).symm
  have hArith : IsArithFrobAt (𝓞 K) (δ : G) Q := by
    intro x
    change NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x -
        x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [← Ideal.Quotient.eq, map_pow]
    exact hResidue x
  have hMath : IsArithFrobAt (𝓞 K)
      (arithmeticFrobeniusAt (K := K) W) Q := by
    change IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) G Q) Q
    exact IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  have hInertiaCard : Nat.card (Q.inertia G) = 1 := by
    calc
      Nat.card (Q.inertia G) = P.ramificationIdxIn (𝓞 L) :=
        Ideal.card_inertia_eq_ramificationIdxIn (G := G) P Q
      _ = Q.ramificationIdx (𝓞 K) :=
        Ideal.ramificationIdxIn_eq_ramificationIdx P Q G
      _ = 1 := hEQ.trans hEw
  have hInertiaBot : Q.inertia G = ⊥ :=
    (Subgroup.eq_bot_iff_card (Q.inertia G)).mpr hInertiaCard
  have hDiff : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ ∈
      Q.inertia G := hArith.mul_inv_mem_inertia hMath
  have hDiffEq : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ = 1 := by
    simpa only [hInertiaBot, Subgroup.mem_bot] using hDiff
  have hδEq : (δ : G) = arithmeticFrobeniusAt (K := K) W :=
    mul_inv_eq_one.mp hDiffEq
  calc
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
        GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hChosen :=
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen
    _ = (δ : G) := hδ.symm
    _ = arithmeticFrobeniusAt (K := K) W := hδEq
    _ = arithmeticFrobeniusAt (K := K) w :=
      arithmeticFrobeniusAt_eq_of_liesOver
        (K := K) (L := L) v W w hW hw

end ClassFieldTheory.GlobalClassFieldComparison
end
end

theorem solution : type_of% @ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt_oai := @ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt_oai
