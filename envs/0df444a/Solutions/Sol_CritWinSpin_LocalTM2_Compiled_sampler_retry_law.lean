-- Prove2me | solution 1 for CritWinSpin.LocalTM2.Compiled.sampler_retry_law
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:36:29.254462+00:00
-- url     : https://prove2.me/submissions/c65037cb-80b9-4735-adcb-6826a7be4ee1

import Mathlib
import Definitions.Def_CritWinSpin_SamplerMachine

set_option linter.all false

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.DensityAnalysis

namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

end EulerDensity

namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

end EulerDensity

end CritWinSpin.Implementation.DensityAnalysis

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.MetropolisFlux

variable {E : Type*} [MeasurableSpace E]

end CritWinSpin.Implementation.MetropolisFlux

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.LangevinAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end CritWinSpin.Implementation.LangevinAlgebra

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.DensityIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

end CritWinSpin.Implementation.DensityIntegrals

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinJointDensity

open DensityAnalysis LangevinAlgebra

end CritWinSpin.Implementation.LangevinJointDensity

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CritWinSpin.Implementation.GaussianMoments

end CritWinSpin.Implementation.GaussianMoments

end

end

section

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CritWinSpin.Implementation.ContractiveOperator

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

variable (P : (E → ℝ) → E → ℝ) (q : ℝ)

end CritWinSpin.Implementation.ContractiveOperator

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.NoiseOperator

open ContractiveOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

end CritWinSpin.Implementation.NoiseOperator

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinDefect

open DensityAnalysis LangevinAlgebra LangevinJointDensity

end CritWinSpin.Implementation.LangevinDefect

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.LangevinConvergence

open DensityAnalysis LangevinAlgebra ContractiveOperator

end CritWinSpin.Implementation.LangevinConvergence

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.KernelTests

variable {A X : Type*} [Fintype A]

end CritWinSpin.Implementation.KernelTests

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.LangevinBudget
open DensityAnalysis LangevinAlgebra ContractiveOperator LangevinConvergence

end CritWinSpin.Implementation.LangevinBudget
end

end

section

open MeasureTheory IsingLTL.BeliefProp

set_option autoImplicit false
set_option maxHeartbeats 2400000

open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeAnalysis

section SpinAndPhi

noncomputable def mgf (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

theorem mgf_pos (S : SpinLaw) (t : ℝ) : 0 < mgf S t := by
  unfold mgf
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hterm : 0 < (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := by
    have hρ : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 hmem
    positivity
  have hnn : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := fun x hx => by
    have : 0 < (S.ρ x : ℝ) := by exact_mod_cast S.pos x hx
    positivity
  exact lt_of_lt_of_le hterm (Finset.single_le_sum hnn hmem)

end SpinAndPhi

section LinearAlgebraAndHessian

end LinearAlgebraAndHessian

end CritWinSpin.Implementation.EnvelopeAnalysis

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.SmoothGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end CritWinSpin.Implementation.SmoothGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeGeometry

open EnvelopeAnalysis

end CritWinSpin.Implementation.EnvelopeGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.PiVolumeTransfer

open DensityAnalysis

end CritWinSpin.Implementation.PiVolumeTransfer

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.Regularization

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f R : Ω → ℝ)

end CritWinSpin.Implementation.Regularization

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RegularizedGibbsMoments

open DensityAnalysis

end CritWinSpin.Implementation.RegularizedGibbsMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeMoments

open DensityAnalysis EnvelopeGeometry

end CritWinSpin.Implementation.EnvelopeMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin
open scoped NNReal

namespace CritWinSpin.Implementation.EnvelopeCertificate
open DensityAnalysis LangevinBudget EnvelopeGeometry

end CritWinSpin.Implementation.EnvelopeCertificate
end

end

section
set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.MomentBudget

end CritWinSpin.Implementation.MomentBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeParameters
open DensityAnalysis EnvelopeGeometry LangevinBudget

end CritWinSpin.Implementation.EnvelopeParameters
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open Turing StateTransition QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

def wordValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (wordValue bs)

theorem wordValue_bits (n : ℕ) : wordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp [wordValue, ih]

def readQuoted : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bs, tail) ← readQuoted rest
      pure (b :: bs, tail)
  | _ => none

theorem readQuoted_encode (bs tail : List Bool) :
    readQuoted (bs.flatMap (fun b => [true, b]) ++ false :: false :: tail) =
      some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readQuoted, ih]

def readBin (xs : List Bool) : Option (ℕ × List Bool) := do
  let (bs, rest) ← readQuoted xs
  pure (wordValue bs, rest)

theorem readBin_encBin (n : ℕ) (tail : List Bool) :
    readBin (encBin n ++ tail) = some (n, tail) := by
  simp [readBin, encBin, List.append_assoc, readQuoted_encode, wordValue_bits]

def readInt : List Bool → Option (ℤ × List Bool)
  | sign :: xs => do
      let (n, tail) ← readBin xs
      pure ((if sign then -(n : ℤ) else (n : ℤ)), tail)
  | [] => none

theorem readInt_encInt (z : ℤ) (tail : List Bool) :
    readInt (encInt z ++ tail) = some (z, tail) := by
  by_cases hz : z < 0
  · simp [encInt, hz, readInt, readBin_encBin, abs_of_neg hz]
  · simp [encInt, hz, readInt, readBin_encBin, abs_of_nonneg (le_of_not_gt hz)]

def readRat (xs : List Bool) : Option (ℚ × List Bool) := do
  let (num, rest) ← readInt xs
  let (den, tail) ← readBin rest
  pure (Rat.divInt num den, tail)

theorem readRat_encRat (q : ℚ) (tail : List Bool) :
    readRat (encRat q ++ tail) = some (q, tail) := by
  simp [readRat, encRat, List.append_assoc, readInt_encInt, readBin_encBin]

def readRats : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
      let (q, rest) ← readRat xs
      let (qs, tail) ← readRats n rest
      pure (q :: qs, tail)

theorem readRats_encode (qs : List ℚ) (tail : List Bool) :
    readRats qs.length (qs.flatMap encRat ++ tail) = some (qs, tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [readRats, List.append_assoc, readRat_encRat, ih]

theorem ofFn_flatMap {α β : Type} {N : ℕ} (f : Fin N → α) (g : α → List β) :
    (List.ofFn f).flatMap g = (List.ofFn (fun i => g (f i))).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [List.ofFn_succ, ih]

theorem readRats_encConfig {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) (tail : List Bool) :
    readRats N (encConfig x ++ tail) = some (List.ofFn (fun i => (x i : ℚ)), tail) := by
  have h := readRats_encode (List.ofFn (fun i => (x i : ℚ))) tail
  simpa only [List.length_ofFn, ofFn_flatMap, encConfig] using h

theorem encConfig_injective {S : SpinLaw} {N : ℕ} :
    Function.Injective (encConfig (S := S) (N := N)) := by
  intro x y hxy
  have h := readRats_encConfig x []
  rw [hxy, readRats_encConfig y []] at h
  have hlists : List.ofFn (fun i => (y i : ℚ)) = List.ofFn (fun i => (x i : ℚ)) :=
    congrArg Prod.fst (Option.some.inj h)
  have hfun := List.ofFn_injective hlists
  funext i
  apply Subtype.ext
  exact (congrFun hfun i).symm

theorem decConfig_encConfig {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) :
    decConfig S N (encConfig x) = some x := by
  classical
  unfold decConfig
  split_ifs with h
  · congr 1
    exact encConfig_injective (Classical.choose_spec h)
  · exact False.elim (h ⟨x, rfl⟩)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem binaryWords_encoded (bs tail : List Bool) :
    binaryWords (bs.flatMap (fun b => [true, b]) ++ [false, false] ++ tail) = (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (b :: (binaryWords (bs.flatMap (fun c => [true, c]) ++
          [false, false] ++ tail)).1,
        (binaryWords (bs.flatMap (fun c => [true, c]) ++ [false, false] ++ tail)).2) = _
      rw [ih]

theorem binaryTotal_encBin (n : ℕ) (tail : List Bool) :
    binaryTotal (encBin n ++ tail) = (n, tail) := by
  change (Word.value (binaryWords (n.bits.flatMap (fun b => [true, b]) ++
      [false, false] ++ tail)).1,
    (binaryWords (n.bits.flatMap (fun b => [true, b]) ++ [false, false] ++ tail)).2) = _
  rw [binaryWords_encoded]
  simp only [Word.value_bits]

theorem integerTotal_encInt (z : ℤ) (tail : List Bool) :
    integerTotal (encInt z ++ tail) = (z, tail) := by
  by_cases hz : z < 0
  · simp [integerTotal, encInt, hz, binaryTotal_encBin, Signed.value, abs_of_neg hz]
  · simp [integerTotal, encInt, hz, binaryTotal_encBin, Signed.value,
      abs_of_nonneg (le_of_not_gt hz)]

theorem rationalTotal_encRat (q : ℚ) (tail : List Bool) :
    rationalTotal (encRat q ++ tail) = (q, tail) := by
  simp [rationalTotal, encRat, List.append_assoc, integerTotal_encInt, binaryTotal_encBin]

theorem tupleWords_encoded (bs tail : List Bool) :
    tupleWords (bs.flatMap (fun b => [b, b]) ++ false :: true :: tail) = (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [tupleWords, ih]

theorem requestPair_tupleCode (ω x : List Bool) :
    requestPair (tupleCode [ω, x]) = (ω, x) := by
  simp [requestPair, tupleCode, List.append_assoc, tupleWords_encoded]

end CritWinSpin.LocalTM2

end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem zip_ofFn {α β : Type} {N : ℕ} (f : Fin N → α) (g : Fin N → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simpa [List.ofFn_succ] using
        congrArg (List.cons (f 0, g 0)) (ih (fun i => f i.succ) (fun i => g i.succ))

theorem dot_ofFn {N : ℕ} (f g : Fin N → ℚ) :
    dot (List.ofFn f, List.ofFn g) = ∑ i, f i * g i := by
  rw [dot, zip_ofFn, List.map_ofFn]
  exact List.sum_ofFn

theorem matrixVector_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) :
    matrixVector (List.ofFn (fun i => List.ofFn (A i)), List.ofFn v) =
      List.ofFn (A.mulVec v) := by
  rw [matrixVector, List.map_ofFn]
  congr 1
  funext i
  exact dot_ofFn (A i) v

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem normalize_tv_le {α : Type} [Fintype α] (f w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hF : 0 < ∑ x, f x) (hW : 0 < ∑ x, w x) :
    tvDist (fun x => w x / ∑ y, w y) (fun x => f x / ∑ y, f y) ≤
      (∑ x, |w x - f x|) / ∑ x, f x := by
  classical
  let F := ∑ x, f x
  let W := ∑ x, w x
  have hF0 : F ≠ 0 := hF.ne'
  have hW0 : W ≠ 0 := hW.ne'
  have hpoint (x : α) :
      F * |w x / W - f x / F| ≤ |w x - f x| + (w x / W) * |F - W| := by
    have hid : F * (w x / W - f x / F) =
        (w x - f x) + (w x / W) * (F - W) := by field_simp [hF0, hW0]; ring
    calc
      F * |w x / W - f x / F| = |F * (w x / W - f x / F)| := by
        rw [abs_mul, abs_of_pos hF]
      _ ≤ |w x - f x| + |(w x / W) * (F - W)| := by rw [hid]; exact abs_add_le _ _
      _ = |w x - f x| + (w x / W) * |F - W| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (hw x) hW.le)]
  have hsum : F * (∑ x, |w x / W - f x / F|) ≤
      (∑ x, |w x - f x|) + |F - W| := by
    have hh := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpoint x
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_div] at hh
    have hnorm : (∑ x, w x) / W = 1 := div_self hW0
    simpa only [hnorm, one_mul] using hh
  have hdiff : |F - W| ≤ ∑ x, |w x - f x| := by
    change |(∑ x, f x) - ∑ x, w x| ≤ _
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_sub_comm])
  unfold tvDist
  change (∑ x, |w x / W - f x / F|) / 2 ≤ (∑ x, |w x - f x|) / F
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hF]
  nlinarith

theorem normalize_tv_of_uniform_error {α : Type} [Fintype α]
    (f w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hF : 0 < ∑ x, f x) (hW : 0 < ∑ x, w x)
    (d : ℝ) (herr : ∀ x, |w x - f x| ≤ d) :
    tvDist (fun x => w x / ∑ y, w y) (fun x => f x / ∑ y, f y) ≤
      (Fintype.card α : ℝ) * d / ∑ x, f x := by
  apply (normalize_tv_le f w hw hF hW).trans
  apply div_le_div_of_nonneg_right _ hF.le
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => herr x)

namespace DyadicRounding

noncomputable def floorCounts {α : Type} (p : α → ℝ) (T : ℕ) (a : α) : ℕ :=
  ⌊(T : ℝ) * p a⌋₊

noncomputable def floorTotal {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) : ℕ :=
  ∑ a, floorCounts p T a

noncomputable def deficit {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) : ℕ :=
  T - floorTotal p T

open Classical in
noncomputable def counts {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) (a₀ a : α) : ℕ :=
  floorCounts p T a + if a = a₀ then deficit p T else 0

theorem floorTotal_le {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) :
    floorTotal p T ≤ T := by
  have hs := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg T) (hp.1 a))
  rw [← Finset.mul_sum, hp.2, mul_one] at hs
  exact_mod_cast hs

theorem counts_total {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) (a₀ : α) :
    ∑ a, counts p T a₀ a = T := by
  classical
  have hc := floorTotal_le p hp T
  simp only [counts, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal p T + (T - floorTotal p T) = T
  omega

end DyadicRounding

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
namespace FiniteTicket

def bucket : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, ticket => if ticket < c then 0 else 1 + bucket cs (ticket - c)

theorem bucket_lt_length (cs : List ℕ) (ticket : ℕ) (h : ticket < cs.sum) :
    bucket cs ticket < cs.length := by
  induction cs generalizing ticket with
  | nil => simp at h
  | cons c cs ih =>
      simp only [List.sum_cons] at h
      simp only [bucket, List.length_cons]
      split_ifs with hc
      · omega
      · have := ih (ticket - c) (by omega)
        omega

def bitTicketEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) :=
  (Equiv.piCongrRight fun _ : Fin L => finTwoEquiv.symm).trans finFunctionFinEquiv

theorem bitTicketEquiv_value (L : ℕ) (ω : Fin L → Bool) :
    (bitTicketEquiv L ω).val = ∑ i, (ω i).toNat * 2 ^ i.val := by
  rw [bitTicketEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (finTwoEquiv.symm (ω i)).val * 2 ^ i.val = (ω i).toNat * 2 ^ i.val
  cases h : ω i <;> rfl

def wordNumber : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * wordNumber bs

theorem wordNumber_ofFn (L : ℕ) (ω : Fin L → Bool) :
    wordNumber (List.ofFn ω) = ∑ i, (ω i).toNat * 2 ^ i.val := by
  induction L with
  | zero => simp [wordNumber]
  | succ L ih =>
      rw [List.ofFn_succ, wordNumber, Fin.sum_univ_succ, ih]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem bitTicket_wordNumber (L : ℕ) (ω : Fin L → Bool) :
    (bitTicketEquiv L ω).val = wordNumber (List.ofFn ω) := by
  rw [bitTicketEquiv_value, wordNumber_ofFn]

theorem unused_bits_expectation (L R : ℕ) (f : (Fin L → Bool) → ℝ) :
    (1 / (2 : ℝ) ^ (L + R)) *
        (∑ ω : Fin (L + R) → Bool, f (fun i => ω (Fin.castAdd R i))) =
      (1 / (2 : ℝ) ^ L) * ∑ ω : Fin L → Bool, f ω := by
  classical
  have hs : (∑ ω : Fin (L + R) → Bool, f (fun i => ω (Fin.castAdd R i))) =
      (2 : ℝ) ^ R * ∑ ω : Fin L → Bool, f ω := by
    calc
      _ = ∑ ω : (Fin L → Bool) × (Fin R → Bool), f ω.1 := by
        apply Fintype.sum_equiv (Fin.appendEquiv L R).symm
        intro ω
        rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [Finset.mul_sum]
  rw [hs, pow_add]
  field_simp

def drawIndex {n : ℕ} (L : ℕ) (counts : Fin n → ℕ) (htotal : ∑ i, counts i = 2 ^ L)
    (ω : Fin L → Bool) : Fin n :=
  ⟨bucket (List.ofFn counts) (bitTicketEquiv L ω).val, by
    have ht : (bitTicketEquiv L ω).val < (List.ofFn counts).sum := by
      simpa only [List.sum_ofFn, htotal] using (bitTicketEquiv L ω).isLt
    simpa only [List.length_ofFn] using bucket_lt_length _ _ ht⟩

end FiniteTicket
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem rationalFloor_correct (q : ℚ) : rationalFloor q = ⌊q⌋₊ := by
  by_cases hq : q < 0
  · simp [rationalFloor, hq, Nat.floor_of_nonpos hq.le]
  · have hq0 : 0 ≤ q := le_of_not_gt hq
    have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0)
    have hrepr : (q.num.natAbs : ℚ) / q.den = q := by
      rw [← Int.cast_natCast, hnum, Rat.num_div_den]
    rw [rationalFloor, if_neg hq]
    calc
      q.num.natAbs / q.den = ⌊((q.num.natAbs : ℚ) / q.den)⌋₊ :=
        (Rat.natFloor_natCast_div_natCast _ _).symm
      _ = ⌊q⌋₊ := congrArg Nat.floor hrepr

theorem naturalSum_eq (xs : List ℕ) : naturalSum xs = xs.sum := by
  have hcast : (xs.map (fun n : ℕ => (n : ℚ))).sum = (xs.sum : ℚ) := by
    induction xs with
    | nil => simp
    | cons n xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
  rw [naturalSum, hcast, rationalFloor_correct, Nat.floor_natCast]

theorem bucketScan_state (cs : List ℕ) (i ticket : ℕ) (done : Bool) :
    (cs.foldl (fun s c => bucketStep (s, c)) (i, ticket, done)).1 =
      if done then i else i + FiniteTicket.bucket cs ticket := by
  induction cs generalizing i ticket done with
  | nil => cases done <;> simp [FiniteTicket.bucket]
  | cons c cs ih =>
      rw [List.foldl_cons]
      cases done with
      | true =>
          rw [show bucketStep ((i, ticket, true), c) = (i, ticket, true) by rfl, ih]
          simp
      | false =>
          by_cases hc : ticket < c
          · rw [show bucketStep ((i, ticket, false), c) = (i, ticket, true) by
              simp [bucketStep, hc], ih]
            simp [FiniteTicket.bucket, hc]
          · rw [show bucketStep ((i, ticket, false), c) = (i + 1, ticket - c, false) by
              simp [bucketStep, hc], ih]
            simp [FiniteTicket.bucket, hc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem bucketScan_eq (cs : List ℕ) (ticket : ℕ) :
    bucketScan (cs, ticket) = FiniteTicket.bucket cs ticket := by
  simpa [bucketScan] using bucketScan_state cs 0 ticket false

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem map_range_eq_ofFn {α : Type} (N : ℕ) (f : ℕ → α) :
    (List.range N).map f = List.ofFn (fun i : Fin N => f i.val) := by
  apply List.ext_getElem <;> simp

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

theorem log_one_add_gap {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - Real.log (1 + u) ∧ u - Real.log (1 + u) ≤ u ^ 2 := by
  have hb : 0 < 1 + u := by linarith
  have hupper := Real.log_le_sub_one_of_pos hb
  have hlower := Real.one_sub_inv_le_log_of_pos hb
  have hid : 1 - (1 + u)⁻¹ - (u - u ^ 2) = u ^ 3 / (1 + u) := by
    field_simp [hb.ne']
    ring
  have hnon : 0 ≤ 1 - (1 + u)⁻¹ - (u - u ^ 2) := by
    rw [hid]
    positivity
  constructor <;> linarith

theorem logarithmic_exp_error {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    0 ≤ x - (n : ℝ) * Real.log (1 + x / n) ∧
      x - (n : ℝ) * Real.log (1 + x / n) ≤ x ^ 2 / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := log_one_add_gap (div_nonneg hx hnr.le)
  have hid : x - (n : ℝ) * Real.log (1 + x / n) =
      (n : ℝ) * (x / n - Real.log (1 + x / n)) := by field_simp [hnr.ne']
  have hpow : (n : ℝ) * (x / n) ^ 2 = x ^ 2 / n := by field_simp [hnr.ne']
  rw [hid]
  exact ⟨mul_nonneg hnr.le hg.1,
    (mul_le_mul_of_nonneg_left hg.2 hnr.le).trans_eq hpow⟩

theorem reciprocalExp_error (x : ℚ) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n)
    (hsmall : (x : ℝ) ^ 2 / n ≤ 1) :
    0 ≤ reciprocalExp x n ∧
      |(reciprocalExp x n : ℝ) - Real.exp (-(x : ℝ))| ≤ 2 * (x : ℝ) ^ 2 / n := by
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 1 + (x : ℝ) / n := by positivity
  obtain ⟨hd0, hd1⟩ := logarithmic_exp_error hxr n hn
  let d := (x : ℝ) - (n : ℝ) * Real.log (1 + (x : ℝ) / n)
  have hd : |d| ≤ 1 := by rw [abs_of_nonneg hd0]; exact hd1.trans hsmall
  have heq : (reciprocalExp x n : ℝ) = Real.exp (-(x : ℝ)) * Real.exp d := by
    rw [← Real.exp_add]
    have hid : -(x : ℝ) + d = -((n : ℝ) * Real.log (1 + (x : ℝ) / n)) := by dsimp [d]; ring
    rw [hid, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hbase]
    simp [reciprocalExp]
  refine ⟨by dsimp [reciprocalExp]; positivity, ?_⟩
  calc
    |(reciprocalExp x n : ℝ) - Real.exp (-(x : ℝ))| =
        Real.exp (-(x : ℝ)) * |Real.exp d - 1| := by
      rw [heq, show Real.exp (-(x : ℝ)) * Real.exp d - Real.exp (-(x : ℝ)) =
        Real.exp (-(x : ℝ)) * (Real.exp d - 1) by ring,
        abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * (2 * |d|) := mul_le_mul
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hxr))
      (Real.abs_exp_sub_one_le hd) (abs_nonneg _) zero_le_one
    _ ≤ 2 * (x : ℝ) ^ 2 / n := by
      rw [abs_of_nonneg hd0]
      simpa only [one_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hd1 (by norm_num : (0 : ℝ) ≤ 2)

theorem exp_neg_cutoff {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d)
    (hcut : 1 / d ≤ x) : Real.exp (-x) ≤ d := by
  have hexp := Real.add_one_le_exp x
  have hdexp : 1 / d ≤ Real.exp x := by linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hd]
  simpa only [one_div] using hdexp

theorem expNegativeApprox_error (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d) (hd1 : d ≤ 1) :
    0 ≤ expNegativeApprox x d ∧
      |(expNegativeApprox x d : ℝ) - Real.exp (-(x : ℝ))| ≤ (d : ℝ) := by
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hdr1 : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
  unfold expNegativeApprox
  split_ifs with hcut
  · refine ⟨le_rfl, ?_⟩
    simpa only [Rat.cast_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)] using
      exp_neg_cutoff hxr hdr (by exact_mod_cast hcut)
  · let n := reciprocalTerms x d
    have hn : 0 < n := by dsimp [n, reciprocalTerms]; omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hceilQ := (Nat.lt_floor_add_one (2 * x ^ 2 / d)).le
    have hceil : 2 * (x : ℝ) ^ 2 / d ≤ (n : ℝ) := by
      have hh : 2 * x ^ 2 / d ≤ (n : ℚ) := by
        dsimp [n, reciprocalTerms]
        exact hceilQ.trans (by norm_cast; omega)
      exact_mod_cast hh
    have hscale : 2 * (x : ℝ) ^ 2 ≤ (d : ℝ) * n := by
      simpa only [mul_comm] using (div_le_iff₀ hdr).mp hceil
    have hsmall : (x : ℝ) ^ 2 / n ≤ 1 := by
      rw [div_le_iff₀ hnr]
      nlinarith [mul_le_mul_of_nonneg_right hdr1 hnr.le]
    obtain ⟨hpos, herr⟩ := reciprocalExp_error x hx n hn hsmall
    refine ⟨hpos, herr.trans ?_⟩
    rw [div_le_iff₀ hnr]
    exact hscale

theorem reciprocalTerms_bound (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d)
    (hcut : x < 1 / d) :
    (reciprocalTerms x d : ℝ) ≤ 2 / (d : ℝ) ^ 3 + 2 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hcutr : (x : ℝ) < 1 / d := by exact_mod_cast hcut
  have harg : (0 : ℚ) ≤ 2 * x ^ 2 / d := by positivity
  have hceilQ := Nat.floor_le harg
  have hceil : (reciprocalTerms x d : ℝ) ≤ 2 * (x : ℝ) ^ 2 / d + 2 := by
    dsimp only [reciprocalTerms]
    have hc : (⌊2 * x ^ 2 / d⌋₊ : ℝ) ≤ 2 * (x : ℝ) ^ 2 / d := by exact_mod_cast hceilQ
    push_cast
    linarith
  apply hceil.trans
  have hsq : (x : ℝ) ^ 2 ≤ (1 / (d : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hxr hcutr.le 2
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) hdr.le
  have heq : 2 * (1 / (d : ℝ)) ^ 2 / d = 2 / (d : ℝ) ^ 3 := by field_simp
  rw [heq] at hdiv
  linarith

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem exponentialTerms_eq (x d : ℚ) : exponentialTerms (x, d) = reciprocalTerms x d := by
  simp only [exponentialTerms, rationalFloor_correct, reciprocalTerms]

theorem expWithFuel_eq (x d : ℚ) (fuel : List Unit)
    (hfuel : reciprocalTerms x d ≤ fuel.length) :
    expWithFuel ((x, d), fuel) = expNegativeApprox x d := by
  simp only [expWithFuel, exponentialTerms_eq, expNegativeApprox]
  split_ifs
  · rfl
  · simp [List.map_const', List.length_take, Nat.min_eq_left hfuel, List.prod_replicate,
      reciprocalExp, one_div]

theorem expWithFuel_eq_uniform (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d)
    (fuel : List Unit) (hfuel : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    expWithFuel ((x, d), fuel) = expNegativeApprox x d := by
  by_cases hcut : 1 / d ≤ x
  · simp only [expWithFuel, expNegativeApprox, if_pos hcut]
  · apply expWithFuel_eq
    have hh := (reciprocalTerms_bound x d hx hd (lt_of_not_ge hcut)).trans hfuel
    exact_mod_cast hh

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

theorem weightDenominatorBound_positive (S : SpinLaw) : 0 < weightDenominatorBound S := by
  dsimp [weightDenominatorBound]
  omega

theorem spin_weight_bounds (S : SpinLaw) (a : ℚ) (ha : a ∈ S.A) :
    1 / (weightDenominatorBound S : ℚ) ≤ S.ρ a ∧ S.ρ a ≤ 1 := by
  have hp := S.pos a ha
  have hD := weightDenominatorBound_positive S
  have hden : (S.ρ a).den ≤ weightDenominatorBound S := by
    have hh := Finset.single_le_sum (f := fun x => (S.ρ x).den) (fun x _ => Nat.zero_le _) ha
    dsimp only [weightDenominatorBound]
    omega
  have hnum0 : 0 ≤ (S.ρ a).num := Rat.num_nonneg.mpr hp.le
  have hnumne : (S.ρ a).num ≠ 0 := by
    intro he
    have hz : S.ρ a = 0 := Rat.num_eq_zero.mp he
    linarith
  have hnum : (1 : ℤ) ≤ (S.ρ a).num := by omega
  refine ⟨?_, ?_⟩
  · calc
      1 / (weightDenominatorBound S : ℚ) ≤ 1 / ((S.ρ a).den : ℚ) :=
        one_div_le_one_div_of_le (by exact_mod_cast (S.ρ a).den_pos) (by exact_mod_cast hden)
      _ ≤ ((S.ρ a).num : ℚ) / (S.ρ a).den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
      _ = S.ρ a := Rat.num_div_den _
  · have hh := Finset.single_le_sum (f := S.ρ) (fun x hx => (S.pos x hx).le) ha
    simpa only [S.sum_one] using hh

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

noncomputable def alphabetEquiv (S : SpinLaw) :
    Fin (alphabet S).length ≃ {a : ℚ // a ∈ S.A} :=
  (List.Nodup.getEquiv (alphabet S) S.A.nodup_toList).trans
    (Equiv.subtypeEquivRight (fun a : ℚ => show a ∈ alphabet S ↔ a ∈ S.A from Finset.mem_toList))

theorem alphabetEquiv_value (S : SpinLaw) (i : Fin (alphabet S).length) :
    ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ) = (alphabet S)[i.val] := rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

open Classical in
theorem outLaw_reclock {α : Type} (M : RandMachine) (x : Str) (dec : Str → Option α)
    (y : Option α) (K : ℕ) (hK : M.coins x = K) :
    outLaw M x dec y = (1 / (2 : ℝ) ^ K) *
      ∑ ω : Fin K → Bool,
        if dec (M.run (tupleCode [List.ofFn ω, x])) = y then (1 : ℝ) else 0 := by
  cases hK
  rfl

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp

theorem rationalFloor_real (q : ℚ) : rationalFloor q = ⌊(q : ℝ)⌋₊ := by
  rw [rationalFloor_correct, ← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

theorem normalizedRationals_ofFn {n : ℕ} (w : Fin n → ℚ) :
    normalizedRationals (List.ofFn w) = List.ofFn (fun i => w i / ∑ j, w j) := by
  simp only [normalizedRationals, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem quantizedCounts_ofFn {n : ℕ} (w : Fin (n + 1) → ℚ) (T : ℕ) :
    quantizedCounts (List.ofFn w, T) =
      List.ofFn (DyadicRounding.counts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T 0) := by
  classical
  have hc : ((normalizedRationals (List.ofFn w)).map
      (fun q => rationalFloor ((T : ℚ) * q))) =
      List.ofFn (DyadicRounding.floorCounts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T) := by
    rw [normalizedRationals_ofFn, List.map_ofFn]
    congr 1
    funext i
    change rationalFloor ((T : ℚ) * (w i / ∑ j, w j)) = _
    rw [rationalFloor_real]
    simp [DyadicRounding.floorCounts]
  simp only [quantizedCounts, hc, naturalSum_eq, List.sum_ofFn]
  simp only [List.ofFn_succ, List.isEmpty_cons, Bool.false_eq_true, ite_false,
    List.head?_cons, Option.getD_some, List.tail_cons]
  simp [DyadicRounding.counts, DyadicRounding.deficit, DyadicRounding.floorTotal]

theorem wordValue_wordNumber (xs : List Bool) : Word.value xs = FiniteTicket.wordNumber xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [Word.value, FiniteTicket.wordNumber, ih]

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem expNegativeApprox_zero (d : ℚ) (hd : 0 < d) : expNegativeApprox 0 d = 1 := by
  have hcut : ¬1 / d ≤ (0 : ℚ) := not_le.mpr (by positivity)
  simp [expNegativeApprox, hcut, reciprocalExp, reciprocalTerms, hd]

theorem shifted_exponential_normalize {α : Type} [Fintype α] (E ρ : α → ℝ) (U : ℝ) :
    (fun x => (Real.exp (E x - U) * ρ x) / ∑ y, Real.exp (E y - U) * ρ y) =
      (fun x => (Real.exp (E x) * ρ x) / ∑ y, Real.exp (E y) * ρ y) := by
  funext x
  have heq (y : α) : Real.exp (E y - U) * ρ y = Real.exp (-U) * (Real.exp (E y) * ρ y) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  simp only [heq, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

def enumeratedWeights {α : Type} (E ρ : α → ℚ) (U d : ℚ) (x : α) : ℚ :=
  ρ x * expNegativeApprox (U - E x) d

theorem enumeratedWeights_tv {α : Type} [Fintype α]
    (E ρ : α → ℚ) (U d : ℚ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hρ : ∀ x, 0 < ρ x ∧ ρ x ≤ 1) (hU : ∀ x, E x ≤ U)
    (xstar : α) (hstar : E xstar = U) :
    tvDist
      (fun x => (enumeratedWeights E ρ U d x : ℝ) / ∑ y, (enumeratedWeights E ρ U d y : ℝ))
      (fun x => (Real.exp (E x : ℝ) * (ρ x : ℝ)) /
        ∑ y, Real.exp (E y : ℝ) * (ρ y : ℝ)) ≤
      (Fintype.card α : ℝ) * d / (ρ xstar : ℝ) := by
  classical
  let f : α → ℝ := fun x => Real.exp (-(U - E x : ℚ) : ℝ) * (ρ x : ℝ)
  let w : α → ℝ := fun x => (enumeratedWeights E ρ U d x : ℝ)
  have hρpos (x : α) : (0 : ℝ) < ρ x := by exact_mod_cast (hρ x).1
  have hwpos (x : α) : 0 ≤ w x := by
    dsimp only [w, enumeratedWeights]
    push_cast
    have he := (expNegativeApprox_error (U - E x) d (sub_nonneg.mpr (hU x)) hd hd1).1
    exact mul_nonneg (hρpos x).le (by exact_mod_cast he)
  have hfpos (x : α) : 0 < f x := mul_pos (Real.exp_pos _) (hρpos x)
  have hfstar : f xstar = (ρ xstar : ℝ) := by simp [f, hstar]
  have hwstar : w xstar = (ρ xstar : ℝ) := by
    simp [w, enumeratedWeights, hstar, expNegativeApprox_zero d hd]
  have hFbound : (ρ xstar : ℝ) ≤ ∑ x, f x := by
    rw [← hfstar]
    exact Finset.single_le_sum (fun x _ => (hfpos x).le) (Finset.mem_univ xstar)
  have hWbound : (ρ xstar : ℝ) ≤ ∑ x, w x := by
    rw [← hwstar]
    exact Finset.single_le_sum (fun x _ => hwpos x) (Finset.mem_univ xstar)
  have hF : 0 < ∑ x, f x := (hρpos xstar).trans_le hFbound
  have hW : 0 < ∑ x, w x := (hρpos xstar).trans_le hWbound
  have herr (x : α) : |w x - f x| ≤ (d : ℝ) := by
    have happrox := (expNegativeApprox_error (U - E x) d (sub_nonneg.mpr (hU x)) hd hd1).2
    have hρ1 : (ρ x : ℝ) ≤ 1 := by exact_mod_cast (hρ x).2
    calc
      |w x - f x| = (ρ x : ℝ) *
          |(expNegativeApprox (U - E x) d : ℝ) - Real.exp (-(U - E x : ℚ) : ℝ)| := by
        dsimp only [w, f, enumeratedWeights]
        push_cast
        rw [mul_comm (Real.exp _) _, ← mul_sub, abs_mul, abs_of_pos (hρpos x)]
      _ ≤ (ρ x : ℝ) * d := mul_le_mul_of_nonneg_left happrox (hρpos x).le
      _ ≤ (d : ℝ) := by
        have hdr : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
        nlinarith
  have htv := normalize_tv_of_uniform_error f w hwpos hF hW (d : ℝ) herr
  have hden : (Fintype.card α : ℝ) * d / ∑ x, f x ≤
      (Fintype.card α : ℝ) * d / (ρ xstar : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (hρpos xstar) hFbound
  have hf : (fun x => f x / ∑ y, f y) =
      (fun x => (Real.exp (E x : ℝ) * (ρ x : ℝ)) /
        ∑ y, Real.exp (E y : ℝ) * (ρ y : ℝ)) := by
    have heq : f = fun x => Real.exp ((E x : ℝ) - U) * (ρ x : ℝ) := by
      funext x
      dsimp only [f]
      congr 2
      push_cast
      ring
    rw [heq]
    exact shifted_exponential_normalize (fun x => (E x : ℝ)) (fun x => (ρ x : ℝ)) (U : ℝ)
  rw [← hf]
  exact htv.trans hden

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp
open CritWinSpin.Implementation.EnvelopeAnalysis

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

theorem phiMeanWithFuel_correct (S : SpinLaw) (t d : ℚ) (ht : 0 ≤ t) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    phiMeanWithFuel S ((t, d), fuel) = phiDerivativeApprox S t d := by
  have he (a : ℚ) (ha : a ∈ S.A) :
      expWithFuel ((t - t * a, d), fuel) = expNegativeApprox (t - t * a) d := by
    have ha1 := (S.mem_Icc a ha).2
    exact expWithFuel_eq_uniform _ _ (by nlinarith) hd fuel hf
  unfold phiMeanWithFuel tiltRecords spinTable alphabet phiDerivativeApprox tiltApproxWeight
  simp only [List.map_map, Function.comp_def, Finset.sum_map_toList]
  congr 1
  · calc
      _ = ∑ a ∈ S.A, a * (S.ρ a * expNegativeApprox (t - t * a) d) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha]
      _ = _ := (Finset.sum_coe_sort S.A
        (fun a : ℚ => a * (S.ρ a * expNegativeApprox (t - t * a) d))).symm
  · calc
      _ = ∑ a ∈ S.A, S.ρ a * expNegativeApprox (t - t * a) d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha]
      _ = _ := (Finset.sum_coe_sort S.A
        (fun a : ℚ => S.ρ a * expNegativeApprox (t - t * a) d)).symm

theorem positiveModifiedWithFuel_correct (S : SpinLaw) (s t d : ℚ) (ht : 0 ≤ t) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    positiveModifiedWithFuel S (s, ((t, d), fuel)) = positiveModifiedDerivativeApprox S s t d := by
  unfold positiveModifiedWithFuel rationalMin positiveModifiedDerivativeApprox
  rw [phiMeanWithFuel_correct S t d ht hd fuel hf]
  exact (min_def _ _).symm

theorem modifiedWithFuel_correct (S : SpinLaw) (s t d : ℚ) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    modifiedWithFuel S (s, ((t, d), fuel)) = modifiedDerivativeApprox S s t d := by
  by_cases ht : t < 0
  · simp only [modifiedWithFuel, modifiedDerivativeApprox, ht, ite_true]
    rw [positiveModifiedWithFuel_correct S s (-t) d (by linarith) hd fuel hf]
  · simp only [modifiedWithFuel, modifiedDerivativeApprox, ht, ite_false]
    exact positiveModifiedWithFuel_correct S s t d (by linarith) hd fuel hf

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem matrixEntry_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (i j : Fin N) :
    matrixEntry (List.ofFn (fun i => List.ofFn (A i)), (i.val, j.val)) = A i j := by
  simp [matrixEntry, List.getElem?_eq_getElem, i.isLt, j.isLt]

theorem matrixProductEntry_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (sites : List Unit) (hsites : sites.length = N) (i j : Fin N) :
    matrixProductEntry ((List.ofFn (fun i => List.ofFn (A i)), sites), (i.val, j.val)) =
      (A ^ 2) i j := by
  simp only [matrixProductEntry, siteNumbers, hsites]
  rw [map_range_eq_ofFn, List.sum_ofFn]
  simp only [matrixEntry_ofFn]
  simp only [pow_two, Matrix.mul_apply]

theorem roundedRootRows_ofFn {N : ℕ} (A X : Matrix (Fin N) (Fin N) ℚ)
    (sites : List Unit) (hsites : sites.length = N) (d : ℚ) :
    roundedRootRows (((List.ofFn (fun i => List.ofFn (A i)), sites), d),
      List.ofFn (fun i => List.ofFn (X i))) =
        List.ofFn (fun i => List.ofFn (fun j => clampedRound ((sqrtStepQ A X) i j, d))) := by
  simp only [roundedRootRows, siteNumbers, hsites]
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  rw [map_range_eq_ofFn]
  congr 1
  funext j
  rw [matrixEntry_ofFn, matrixEntry_ofFn, matrixProductEntry_ofFn X sites hsites i j]
  simp only [sqrtStepQ, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  congr 1
  ring

theorem rootZeroRows_correct (N : ℕ) :
    rootZeroRows (List.replicate N ()) =
      List.ofFn (fun _ : Fin N => List.ofFn (fun _ : Fin N => (0 : ℚ))) := by
  simp [rootZeroRows, List.ofFn_const]

theorem rootCompute_correct {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (d : ℚ)
    (fuel : List Unit) :
    rootCompute (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d), fuel) =
      List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d fuel.length i)) := by
  have hfold (xs : List Unit) (n : ℕ) :
      xs.foldl (fun st _ => roundedRootStep st)
        (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
          List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d n i))) =
        (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
          List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d (n + xs.length) i))) := by
    induction xs generalizing n with
    | nil => simp
    | cons u xs ih =>
        rw [List.foldl_cons]
        change xs.foldl (fun st _ => roundedRootStep st)
          (_, roundedRootRows (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
            List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d n i)))) = _
        rw [roundedRootRows_ofFn A (roundedMatrixSqrt A d n) (List.replicate N ()) (List.length_replicate ..) d]
        change xs.foldl (fun st _ => roundedRootStep st)
          (_, List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d (n + 1) i))) = _
        rw [ih]
        simp only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold rootCompute
  rw [rootZeroRows_correct]
  have hh := hfold fuel 0
  have hz : List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d 0 i)) =
      List.replicate N (List.replicate N (0 : ℚ)) := by
    change List.ofFn (fun _ : Fin N => List.ofFn (fun _ : Fin N => (0 : ℚ))) = _
    simp only [List.ofFn_const]
  rw [hz] at hh
  simpa only [Nat.zero_add, List.ofFn_const] using congrArg Prod.snd hh

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

def driftInputOf {N : ℕ} (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ)
    (s a d : ℚ) (fuel : List Unit) : DriftInput :=
  (((List.ofFn (fun i => List.ofFn (L i)), List.ofFn h),
    (List.replicate N (), (s, a, d))), (List.ofFn z, fuel))

theorem driftCoefficients_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    driftCoefficients S (driftInputOf L h z s a d fuel) =
      List.ofFn (fun i => modifiedDerivativeApprox S s (L.mulVec z i + h i) d) := by
  unfold driftCoefficients driftArguments driftInputOf
  rw [matrixVector_ofFn, zip_ofFn, List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  exact modifiedWithFuel_correct S s (L.mulVec z i + h i) d hd fuel hf

theorem driftTransposeProduct_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length)
    (i : Fin N) :
    driftTransposeProduct S (driftInputOf L h z s a d fuel, i.val) =
      ∑ j, L j i * modifiedDerivativeApprox S s (L.mulVec z j + h j) d := by
  unfold driftTransposeProduct
  rw [driftCoefficients_correct S L h z s a d hd fuel hf]
  simp only [driftInputOf, siteNumbers, List.length_replicate]
  rw [map_range_eq_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp [matrixEntry_ofFn, j.isLt]

theorem driftWithFuel_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    driftWithFuel S (driftInputOf L h z s a d fuel) =
      List.ofFn (approximateGradient S L h z s a d) := by
  unfold driftWithFuel
  simp only [siteNumbers, driftInputOf, List.length_replicate]
  change (List.range N).map _ = _
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  change (1 + a) * ((List.ofFn z)[i.val]?).getD 0 -
    driftTransposeProduct S (driftInputOf L h z s a d fuel, i.val) = _
  rw [driftTransposeProduct_correct S L h z s a d hd fuel hf i]
  simp [driftInputOf, approximateGradient, i.isLt]

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section

theorem snappedDriftWithFuel_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d snap : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    snappedDriftWithFuel S (snap, driftInputOf L h z s a d fuel) =
      List.ofFn (approximateGradient S L h (fun i => roundTowardZero (z i, snap)) s a d) := by
  unfold snappedDriftWithFuel
  simp only [driftInputOf, List.map_ofFn]
  change driftWithFuel S (driftInputOf L h (fun i => roundTowardZero (z i, snap)) s a d fuel) = _
  exact driftWithFuel_correct S L h _ s a d hd fuel hf

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory ProbabilityTheory

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGrid

end CritWinSpin.Implementation.GaussianGrid

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def gaussianCoinBudget (k : ℕ) : ℕ :=
  gaussianBits k + gaussianGridSize k + 2 * (gaussianMeshDen k) ^ 3 + 2

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic IsingLTL.BeliefProp

theorem quantizedCounts_ofFn_pos {n : ℕ} (hn : 0 < n) (w : Fin n → ℚ) (T : ℕ) :
    quantizedCounts (List.ofFn w, T) =
      List.ofFn (DyadicRounding.counts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T ⟨0, hn⟩) := by
  cases n with
  | zero => omega
  | succ n => exact quantizedCounts_ofFn w T

theorem sampleScalarTable_ofFn {n : ℕ} (v : Fin n → ℚ)
    (L : ℕ) (cs : Fin n → ℕ) (htotal : ∑ i, cs i = 2 ^ L) (ω : Fin L → Bool) :
    sampleScalarTable ((List.ofFn v, List.ofFn cs), List.ofFn ω) =
      v (FiniteTicket.drawIndex L cs htotal ω) := by
  unfold sampleScalarTable
  rw [bucketScan_eq, wordValue_wordNumber, ← FiniteTicket.bitTicket_wordNumber]
  have hb := (FiniteTicket.drawIndex L cs htotal ω).isLt
  change FiniteTicket.bucket (List.ofFn cs) (FiniteTicket.bitTicketEquiv L ω).val < n at hb
  simp only [List.getElem?_ofFn, hb, dite_true, Option.getD_some]
  rfl

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGridLaw

open GaussianGrid

end CritWinSpin.Implementation.GaussianGridLaw

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp ProbabilityTheory MeasureTheory
open CritWinSpin.Implementation.GaussianGrid

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory
noncomputable section

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory ProbabilityTheory

theorem gaussianNoiseBits_budget (k : ℕ) : gaussianNoiseBits k = gaussianCoinBudget k := by
  unfold gaussianNoiseBits gaussianNoiseTail gaussianCoinBudget
  omega

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem bitBlock_ofFn {N B : ℕ} (ω : Fin (N * B) → Bool) (i : Fin N) :
    bitBlock ((List.ofFn ω, B), i.val) = List.ofFn (fun j => ω (blockIndex i j)) := by
  apply List.ext_getElem
  · simp only [bitBlock, List.length_take, List.length_drop, List.length_ofFn]
    have hm : i.val * B + B ≤ N * B := by
      nlinarith [Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)]
    omega
  · intro j hj hj'
    simp only [bitBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    congr 1

def splitBitEquiv (N B : ℕ) : (Fin (N * B) → Bool) ≃ (Fin N → Fin B → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin N) (Fin B) Bool)

theorem splitBitEquiv_apply (N B : ℕ) (ω : Fin (N * B) → Bool) (i : Fin N) (j : Fin B) :
    splitBitEquiv N B ω i j = ω (blockIndex i j) := by
  change ω (finProdFinEquiv (i, j)) = ω (blockIndex i j)
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, blockIndex, Nat.mul_comm, Nat.add_comm]

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation.EnvelopeAnalysis

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

theorem bitBlock_append (xs ys : List Bool) (B i : ℕ) (hi : (i + 1) * B ≤ xs.length) :
    bitBlock ((xs ++ ys, B), i) = bitBlock ((xs, B), i) := by
  have hi0 : i * B ≤ xs.length := by nlinarith
  have hi1 : i * B + B ≤ xs.length := by nlinarith
  unfold bitBlock
  rw [List.drop_append]
  have hz : i * B - xs.length = 0 := Nat.sub_eq_zero_of_le hi0
  rw [hz, List.drop_zero]
  apply List.take_append_of_le_length
  simp only [List.length_drop]
  omega

theorem eulerDrift_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (bits : List Bool) :
    eulerDrift S (D.context, (List.ofFn z, bits)) =
      List.ofFn (approximateGradient S D.L D.h (fun i => roundTowardZero (z i, D.snap))
        D.sCap D.a D.dPhi) := by
  change snappedDriftWithFuel S (D.snap, driftInputOf D.L D.h z D.sCap D.a D.dPhi D.fuel) = _
  exact snappedDriftWithFuel_correct S D.L D.h z D.sCap D.a D.dPhi D.snap hd D.fuel hf

theorem eulerNoise_ofFn {N : ℕ} (D : EulerData N) (z : Fin N → ℚ)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) (i : Fin N) :
    eulerNoise ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) =
      gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j))) := by
  change gaussianDraw (D.k,
    bitBlock ((List.ofFn ω ++ tail, gaussianNoiseBits D.k), i.val)) = _
  have hi : (i.val + 1) * gaussianNoiseBits D.k ≤ (List.ofFn ω).length := by
    simp only [List.length_ofFn]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
  rw [bitBlock_append _ _ _ _ hi, bitBlock_ofFn]

theorem eulerRaw_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool)
    (tail : List Bool) (i : Fin N) :
    eulerRaw S ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) = D.raw S z ω i := by
  change ((List.ofFn z)[i.val]?).getD 0 - D.sigma * D.sigma *
    ((eulerDrift S (D.context, (List.ofFn z, List.ofFn ω ++ tail)))[i.val]?).getD 0 +
      D.sigma * eulerNoise ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) = _
  rw [eulerDrift_ofFn S D hd hf, eulerNoise_ofFn]
  simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some, EulerData.raw, pow_two]

theorem eulerRows_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    eulerRows S (D.context, (List.ofFn z, List.ofFn ω ++ tail)) = List.ofFn (D.cappedNext S z ω) := by
  unfold eulerRows
  have hn : siteNumbers D.context.1.2.1 = List.range N := by simp [EulerData.context, siteNumbers]
  rw [hn]
  change (List.range N).map (fun i => boundedRound
    ((eulerRaw S ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i), D.dRound), D.bound)) = _
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  rw [eulerRaw_ofFn S D hd hf]
  rfl

theorem eulerStep_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    eulerStep S (D.context, (List.ofFn z, List.ofFn ω ++ tail)) =
      (D.context, (List.ofFn (D.cappedNext S z ω), tail)) := by
  unfold eulerStep
  rw [eulerRows_ofFn S D hd hf]
  have hn : D.context.1.2.1.length = N := by simp [EulerData.context]
  simp only [hn]
  change (D.context, (List.ofFn (D.cappedNext S z ω),
    (List.ofFn ω ++ tail).drop (N * gaussianNoiseBits D.k))) = _
  simp

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
noncomputable section

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.ProductWeak

end CritWinSpin.Implementation.ProductWeak

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RoundedEuler

open ContractiveOperator NoiseOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

end CritWinSpin.Implementation.RoundedEuler
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.EulerNoiseOperator
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator

end CritWinSpin.Implementation.EulerNoiseOperator
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.EulerAnalyticStep
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator LangevinBudget EulerNoiseOperator

end CritWinSpin.Implementation.EulerAnalyticStep
end

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerPrecisionArithmetic

end CritWinSpin.Implementation.EulerPrecisionArithmetic
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

open Matrix

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeIntegral

open EnvelopeAnalysis

end CritWinSpin.Implementation.EnvelopeIntegral

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MeasureTheory
open CritWinSpin.Implementation.EnvelopeIntegral
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Matrix

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessPSD
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

end CritWinSpin.Implementation.PreprocessPSD
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessSelection
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD

end CritWinSpin.Implementation.PreprocessSelection
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessBranches
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD PreprocessSelection

end CritWinSpin.Implementation.PreprocessBranches
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessIntegral
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches

end CritWinSpin.Implementation.PreprocessIntegral
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerFiniteBudget
open CritWinSpin.LocalTM2.Compiled EulerAnalyticStep PreprocessIntegral

end CritWinSpin.Implementation.EulerFiniteBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.SpinKernel

open EnvelopeAnalysis

end CritWinSpin.Implementation.SpinKernel

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp

namespace CritWinSpin.Implementation.DensityKernelTV

variable {X A : Type*} [MeasurableSpace X] [Fintype A]

end CritWinSpin.Implementation.DensityKernelTV
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp

variable {A : Type} [Fintype A]

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeKernelTransfer
open DensityAnalysis EnvelopeGeometry ContractiveOperator

end CritWinSpin.Implementation.EnvelopeKernelTransfer
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.HubbardTrialLaw
open Matrix IsingLTL.BeliefProp

end CritWinSpin.Implementation.HubbardTrialLaw
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem rationalReadFold_encoded (qs : List ℚ) (us : List Unit) (hu : us.length = qs.length)
    (tail : List Bool) (acc : List ℚ) :
    us.foldl (fun s u => rationalReadStep (s, u)) (qs.flatMap encRat ++ tail, acc) =
      (tail, qs.reverse ++ acc) := by
  induction qs generalizing us acc with
  | nil => have he : us = [] := List.length_eq_zero_iff.mp hu; subst us; rfl
  | cons q qs ih =>
      cases us with
      | nil => simp at hu
      | cons u us =>
          have hul : us.length = qs.length := by simpa using hu
          rw [List.foldl_cons]
          have hp : (q :: qs).flatMap encRat ++ tail = encRat q ++ (qs.flatMap encRat ++ tail) := by
            simp only [List.flatMap_cons, List.append_assoc]
          rw [hp]
          simp only [rationalReadStep, rationalTotal_encRat]
          change us.foldl (fun s u => rationalReadStep (s, u))
            (qs.flatMap encRat ++ tail, q :: acc) = _
          rw [ih us hul (q :: acc)]
          simp [List.reverse_cons, List.append_assoc]

theorem readRationals_encoded (qs : List ℚ) (us : List Unit) (hu : us.length = qs.length)
    (tail : List Bool) : readRationals (us, qs.flatMap encRat ++ tail) = qs := by
  rw [readRationals, rationalReadFold_encoded qs us hu tail []]
  simp

def instRationals {N : ℕ} (I : Inst N) : List ℚ :=
  (List.ofFn (fun i => List.ofFn (I.1 i))).flatten ++ List.ofFn I.2

theorem instRationals_length {N : ℕ} (I : Inst N) : (instRationals I).length = N * N + N := by
  simp [instRationals, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem flatMap_flatten {α β : Type} (xss : List (List α)) (f : α → List β) :
    xss.flatten.flatMap f = xss.flatMap (fun xs => xs.flatMap f) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp [List.flatMap_append, ih]

theorem encInst_flatRationals {N : ℕ} (I : Inst N) :
    encInst I = encNat N ++ (instRationals I).flatMap encRat := by
  simp only [encInst, instRationals, List.flatMap_append, flatMap_flatten,
    List.map_ofFn, ofFn_flatMap, List.append_assoc]

theorem parseInstTotal_encoded (N : ℕ) (qs : List ℚ) (hlen : qs.length = N * N + N) :
    parseInstTotal (encNat N ++ qs.flatMap encRat) = (N, qs) := by
  let xs := encNat N ++ qs.flatMap encRat
  have hw : QMCNumericRuntime.inputWidth xs = N := by
    simp [xs, encNat, List.append_assoc, QMCNumericRuntime.inputWidth_prefix]
  have ht : siteTokens xs = List.replicate N () := by
    rw [siteTokens, hw]
    simp [xs, encNat, List.append_assoc]
  have hs : (rationalSlots xs).length = qs.length := by
    rw [hlen]
    simp [rationalSlots, ht, List.length_flatMap]
  have hd : xs.drop (QMCNumericRuntime.inputWidth xs + 1) = qs.flatMap encRat := by
    rw [hw]
    simp [xs, encNat, List.drop_append, List.append_assoc]
  have hd' : xs.drop (N + 1) = qs.flatMap encRat := by simpa only [hw] using hd
  change parseInstTotal xs = _
  rw [parseInstTotal, hw, hd']
  have he := readRationals_encoded qs (rationalSlots xs) hs []
  simpa only [List.append_nil] using congrArg (fun qs => (N, qs)) he

theorem parseInstTotal_encInst {N : ℕ} (I : Inst N) :
    parseInstTotal (encInst I) = (N, instRationals I) := by
  rw [encInst_flatRationals]
  exact parseInstTotal_encoded N (instRationals I) (instRationals_length I)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem flatten_uniform_length {α : Type} (rows : List (List α)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = n) : rows.flatten.length = rows.length * n := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = n := by intro r h; exact hrows r (by simp [h])
      simp only [List.flatten_cons, List.length_append, hr, ih ht, List.length_cons]
      ring

theorem flattened_block {α : Type} (rows : List (List α)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = n) (tail : List α) (i : ℕ) (hi : i < rows.length) :
    ((rows.flatten ++ tail).drop (i * n)).take n = rows[i] := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
      have hr := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = n := by intro r h; exact hrows r (by simp [h])
      have hd : ((row :: rows).flatten ++ tail).drop n = rows.flatten ++ tail := by
        simp only [List.flatten_cons, List.append_assoc]
        rw [← hr, List.drop_left]
      cases i with
      | zero =>
          simp only [zero_mul, List.drop_zero, List.getElem_cons_zero, List.flatten_cons,
            List.append_assoc]
          rw [← hr, List.take_left]
      | succ i =>
          have hit : i < rows.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          rw [show (i + 1) * n = n + i * n by ring, ← List.drop_drop, hd]
          exact ih ht i hit

theorem modelFromFlat_instRationals {N : ℕ} (I : Inst N) (sites : List Unit)
    (hsites : sites.length = N) :
    modelFromFlat (sites, instRationals I) = instanceListModel I := by
  let rows := List.ofFn (fun i => List.ofFn (I.1 i))
  have hrows : ∀ row ∈ rows, row.length = N := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    exact List.length_ofFn
  have hlen : rows.flatten.length = N * N := by
    simpa only [rows, List.length_ofFn] using flatten_uniform_length rows N hrows
  apply Prod.ext
  · change (List.range sites.length).map (fun i => ((instRationals I).drop (i * sites.length)).take sites.length) = rows
    rw [hsites]
    apply List.ext_getElem
    · simp [rows]
    · intro i hi hj
      have hir : i < rows.length := by simpa [rows] using hj
      simpa only [List.getElem_map, List.getElem_range, instRationals] using
        flattened_block rows N hrows (List.ofFn I.2) i hir
  · change (instRationals I).drop (sites.length * sites.length) = List.ofFn I.2
    rw [hsites]
    change (rows.flatten ++ List.ofFn I.2).drop (N * N) = _
    rw [← hlen, List.drop_left]

theorem parseModel_encInst {N : ℕ} (I : Inst N) :
    parseModel (encInst I) = (instanceListModel I, List.replicate N ()) := by
  have hw : QMCNumericRuntime.inputWidth (encInst I) = N := by
    rw [encInst_flatRationals]
    simp [QMCNumericRuntime.inputWidth_prefix, QAlgorithms.Complexity.encNat, List.append_assoc]
  have ht : siteTokens (encInst I) = List.replicate N () := by
    rw [siteTokens, hw, encInst_flatRationals]
    simp [QAlgorithms.Complexity.encNat, List.append_assoc]
  rw [parseModel, ht, parseInstTotal_encInst]
  rw [modelFromFlat_instRationals I _ (by simp)]

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

theorem requestParams_encoded {N : ℕ} (I : Inst N) (m : ℕ) :
    requestParams (tupleCode [encInst I, encBin m]) =
      ((instanceListModel I, List.replicate N ()), m) := by
  rw [requestParams, requestPair_tupleCode, parseModel_encInst]
  have hb := binaryTotal_encBin m []
  simpa only [List.append_nil] using congrArg
    (fun p : ℕ × List Bool => ((instanceListModel I, List.replicate N ()), p.1)) hb

def enumerationCoins (S : SpinLaw) (xs : List Bool) : ℕ := enumerationBudget S (requestParams xs)

@[fun_prop] theorem enumerationCoins_poly (S : SpinLaw) : Poly (enumerationCoins S) := by
  unfold enumerationCoins
  fun_prop

section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] List.flatMap
noncomputable section

end
end

noncomputable def enumerationCoinProgram (S : SpinLaw) :
    PolyProgram id Nat.bits (enumerationCoins S) :=
  (BooleanLists.packProgram.comp (Poly.program (enumerationCoins_poly S))).congr _ (fun _ => rfl)

noncomputable def exhaustiveRandMachine (S : SpinLaw) : RandMachine :=
  programRandMachine (rawEnumerationOutputProgram S) (enumerationCoinProgram S)

theorem exhaustiveRandMachine_run {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (ω : List Bool) :
    (exhaustiveRandMachine S).run
      (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
        (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  change rawEnumerationOutput S _ = _
  rw [rawEnumerationOutput, rawEnumerationSelected, requestPair_tupleCode, requestParams_encoded]

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

theorem samplerRequest_encoded {N : ℕ} (I : Inst N) (m : ℕ) (ω : List Bool) :
    samplerRequest (tupleCode [ω, tupleCode [encInst I, encBin m]]) = encodedSamplerInput I m ω := by
  rw [samplerRequest, requestPair_tupleCode, requestParams_encoded]
  rfl

theorem rawEnumerationOutput_encoded {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (ω : List Bool) :
    rawEnumerationOutput S (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
      (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  exact exhaustiveRandMachine_run S I m ω

theorem criticalWindowMachine_run_encoded {N : ℕ} (S : SpinLaw) (C : ℕ)
    (I : Inst N) (m : ℕ) (ω : List Bool) :
    (criticalWindowMachine S C).run (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
      if (List.replicate N ()).isEmpty then [] else
        if preInside S C ((instanceListModel I).1, List.replicate N ()) then
          samplerRetryOutput S C (encodedSamplerInput I m ω)
        else (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  rw [criticalWindowMachine_run_eq, finalSamplerRun, samplerRequest_encoded,
    rawEnumerationOutput_encoded]
  rfl

theorem criticalWindowMachine_coins_encoded {N : ℕ} (S : SpinLaw) (C : ℕ)
    (I : Inst N) (m : ℕ) :
    (criticalWindowMachine S C).coins (tupleCode [encInst I, encBin m]) =
      if (List.replicate N ()).isEmpty then 0 else
        if preInside S C ((instanceListModel I).1, List.replicate N ()) then
          criticalCoins S C (((instanceListModel I).1, List.replicate N ()), m)
        else enumerationBudget S ((instanceListModel I, List.replicate N ()), m) := by
  rw [criticalWindowMachine_coins_eq, finalSamplerCoins, requestParams_encoded]

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

theorem samplerRoot_ofFn {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) :
    samplerRoot C (sampleReference I m F) =
      List.ofFn (fun i => List.ofFn (sampleRootMatrix C I m F i)) := by
  let A : Matrix (Fin N) (Fin N) ℚ := (1 / ((C : ℚ) * C)) • I.1
  have hA : samplerNormalizedMatrix C (sampleReference I m F) =
      List.ofFn (fun i => List.ofFn (A i)) := by
    simp only [samplerNormalizedMatrix, sampleReference, encodedSamplerInput, instanceListModel,
      List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    congr 1
    funext j
    simp only [A, Matrix.smul_apply, smul_eq_mul]
    ring
  have hbuf : unitize (sampleReference I m F).2 = List.replicate F () := by
    simp [sampleReference, encodedSamplerInput, unitize]
  have htarget : samplerRootTarget C (sampleReference I m F) =
      1 / ((C : ℚ) ^ 4 * (m : ℚ) * ((N : ℚ) + 1) ^ 3) := by
    simp [samplerRootTarget, sampleReference, encodedSamplerInput]
  unfold samplerRoot
  rw [hA, hbuf, htarget]
  change (rootCompute (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()),
    rootTolerance ((List.replicate N (), List.replicate F ()),
      1 / ((C : ℚ) ^ 4 * (m : ℚ) * ((N : ℚ) + 1) ^ 3))), List.replicate F ())).map
    (fun row => row.map (fun x => (C : ℚ) * x)) = _
  rw [rootCompute_correct]
  simp only [List.length_replicate, List.map_ofFn, Function.comp_def]
  rfl

theorem sampleEulerData_context {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    (sampleEulerData S C I m F).context = samplerEulerContext S C (sampleReference I m F) := by
  have hbuf : unitize (sampleReference I m F).2 = List.replicate F () := by
    simp [sampleReference, encodedSamplerInput, unitize]
  unfold sampleEulerData EulerData.context samplerEulerContext samplerDriftContext
  rw [samplerRoot_ofFn C I m F, hbuf]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerDataFacts
open CritWinSpin.LocalTM2.Compiled PreprocessPSD

theorem sample_pre {N : ℕ} (I : Inst N) (m F : ℕ) :
    samplerPre (sampleReference I m F) = encodedInput I.1 := rfl

theorem base_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) :
    baseBudget S C (encodedInput I.1,m) = budgetBase S C I m := by
  simp only [baseBudget,budgetBase,List.length_replicate]
  rfl

theorem radius_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    samplerR S C (sampleReference I m F) = radius S C I m := by
  change (baseBudget S C (samplerPre (sampleReference I m F),m))^100 = (budgetBase S C I m)^100
  rw [sample_pre,base_eq]

theorem parameters {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    let D := sampleEulerData S C I m F
    (D.a:ℝ) = 1/(budgetBase S C I m:ℝ) ∧
    (D.dPhi:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.snap:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.dRound:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.sigma:ℝ) = 1/(2048*(radius S C I m:ℝ)^4) ∧
    (D.k:ℝ) = (radius S C I m:ℝ)^100 ∧
    D.sCap = preSelectedLevel S C (encodedInput I.1) ∧
    samplerStepCount S C (sampleReference I m F) = 16*2048^2*(radius S C I m)^12 := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [sampleEulerData,samplerMesh,samplerQuality,samplerStepScale,samplerStepCount,
    radius_eq,sample_pre,base_eq]
  all_goals push_cast
  all_goals try rfl
  have he : (radius S C I m:ℝ)*(radius S C I m:ℝ)*(radius S C I m:ℝ)*(radius S C I m:ℝ) =
      (radius S C I m:ℝ)^4 := by ring
  rw [he]

end CritWinSpin.Implementation.SamplerDataFacts
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerBudgetBounds
open PreprocessIntegral PreprocessPSD

theorem bounds (C N m Q : ℕ) (hC : 2 ≤ C) (hm : 1 ≤ m) :
    let B := C*(N+1)*(m*Q+1)
    let R := B^100
    2^64 ≤ R ∧ N+1 ≤ R ∧ Q ≤ R ∧ 2*C ≤ R ∧ C ≤ R := by
  let B := C*(N+1)*(m*Q+1)
  have hCN : 1 ≤ C*(N+1) := by
    have hh := mul_le_mul (show 1 ≤ C by omega) (show 1 ≤ N+1 by omega) (by decide : 0 ≤ (1:ℕ)) (Nat.zero_le C)
    simpa only [one_mul] using hh
  have hB_CN : C*(N+1) ≤ B := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ m*Q+1 by omega) (Nat.zero_le (C*(N+1)))
    simpa only [mul_one] using hh
  have hB_C : C ≤ B := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ N+1 by omega) (Nat.zero_le C)
    rw [mul_one] at hh
    exact hh.trans hB_CN
  have hB_N : N+1 ≤ B := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ C by omega) (Nat.zero_le (N+1))
    rw [one_mul] at hh
    exact hh.trans hB_CN
  have hB_Q : Q ≤ B := by
    have hq := mul_le_mul_of_nonneg_right hm (Nat.zero_le Q)
    rw [one_mul] at hq
    have hh := mul_le_mul_of_nonneg_right hCN (Nat.zero_le (m*Q+1))
    rw [one_mul] at hh
    exact hq.trans ((Nat.le_succ _).trans hh)
  have hB2 : 2 ≤ B := hC.trans hB_C
  have hB1 : 1 ≤ B := by omega
  have hBR : B ≤ B^100 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB1 (show 1 ≤ (100:ℕ) by decide)
  have hB2R : B^2 ≤ B^100 := Nat.pow_le_pow_right hB1 (by decide)
  have hDouble : 2*C ≤ B^100 := by
    have hh := mul_le_mul_of_nonneg_right hB2 (Nat.zero_le B)
    have hc := mul_le_mul_of_nonneg_left hB_C (show 0 ≤ (2:ℕ) by decide)
    have hi : 2*B ≤ B^2 := by simpa only [pow_two] using hh
    exact hc.trans (hi.trans hB2R)
  have h64 : 2^64 ≤ B^100 := by
    calc
      _ ≤ (2:ℕ)^100 := Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ _ := pow_le_pow_left₀ (by decide : 0 ≤ (2:ℕ)) hB2 100
  exact ⟨h64,hB_N.trans hBR,hB_Q.trans hBR,hDouble,hB_C.trans hBR⟩

end CritWinSpin.Implementation.SamplerBudgetBounds
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.CriticalAnalyticTrial
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled IsingLTL.BeliefProp
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral
open SamplerDataFacts DensityAnalysis EnvelopeGeometry ContractiveOperator LangevinBudget

end CritWinSpin.Implementation.CriticalAnalyticTrial
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.GibbsPerturbation

open IsingLTL.BeliefProp CritWinSpin.LocalTM2

end CritWinSpin.Implementation.GibbsPerturbation
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

theorem tableBits_linear (n m : ℕ) : tableBits (n, m) ≤ 4 * n * m + 1 := by
  unfold tableBits
  change (4 * n * m).size + 1 ≤ 4 * n * m + 1
  have hh : (4 * n * m).size ≤ 4 * n * m := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem gaussian_numeric_bounds (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    gaussianRadius (R ^ 100) ≤ R ^ 101 ∧
      gaussianMeshDen (R ^ 100) ≤ R ^ 401 ∧
      gaussianGridSize (R ^ 100) ≤ R ^ 503 ∧
      gaussianAccuracy (R ^ 100) ≤ R ^ 202 ∧
      gaussianBits (R ^ 100) ≤ R ^ 706 ∧
      gaussianNoiseBits (R ^ 100) ≤ R ^ 1204 := by
  have hR1 : 1 ≤ R := by norm_num at hR ⊢; omega
  have hRbig : 262144 ≤ R := by norm_num at hR; omega
  have hk : 1 ≤ R ^ 100 := one_le_pow₀ hR1
  have hplus : R ^ 100 + 1 ≤ 2 * R ^ 100 := by omega
  have hr : gaussianRadius (R ^ 100) ≤ R ^ 101 := by
    calc
      _ ≤ 32 * R ^ 100 := by unfold gaussianRadius; omega
      _ ≤ R * R ^ 100 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 100).symm
  have hd : gaussianMeshDen (R ^ 100) ≤ R ^ 401 := by
    calc
      _ ≤ 16384 * (2 * R ^ 100) ^ 4 := by unfold gaussianMeshDen; gcongr
      _ = 262144 * R ^ 400 := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ R * R ^ 400 := Nat.mul_le_mul_right _ hRbig
      _ = _ := (pow_succ' R 400).symm
  have hg : gaussianGridSize (R ^ 100) ≤ R ^ 503 := by
    calc
      _ ≤ 2 * R ^ 101 * R ^ 401 := by unfold gaussianGridSize; gcongr
      _ = 2 * R ^ 502 := by rw [mul_assoc, ← pow_add]
      _ ≤ R * R ^ 502 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 502).symm
  have ha : gaussianAccuracy (R ^ 100) ≤ R ^ 202 := by
    calc
      _ ≤ 64 * R ^ 101 * (2 * R ^ 100) := by unfold gaussianAccuracy; gcongr
      _ = 128 * R ^ 201 := by rw [show 201 = 101 + 100 by decide, pow_add]; ring
      _ ≤ R * R ^ 201 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 201).symm
  have hb : gaussianBits (R ^ 100) ≤ R ^ 706 := by
    have hp : 1 ≤ R ^ 705 := one_le_pow₀ hR1
    calc
      _ ≤ 4 * gaussianGridSize (R ^ 100) * gaussianAccuracy (R ^ 100) + 1 := tableBits_linear _ _
      _ ≤ 4 * R ^ 503 * R ^ 202 + 1 := by gcongr
      _ = 4 * R ^ 705 + 1 := by rw [mul_assoc, ← pow_add]
      _ ≤ 5 * R ^ 705 := by omega
      _ ≤ R * R ^ 705 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 705).symm
  have hf : gaussianNoiseBits (R ^ 100) ≤ R ^ 1204 := by
    rw [gaussianNoiseBits_budget]
    have hp : 1 ≤ R ^ 1203 := one_le_pow₀ hR1
    have h706 : R ^ 706 ≤ R ^ 1203 := Nat.pow_le_pow_right hR1 (by decide)
    have h503 : R ^ 503 ≤ R ^ 1203 := Nat.pow_le_pow_right hR1 (by decide)
    calc
      _ ≤ R ^ 706 + R ^ 503 + 2 * (R ^ 401) ^ 3 + 2 := by unfold gaussianCoinBudget; gcongr
      _ = R ^ 706 + R ^ 503 + 2 * R ^ 1203 + 2 := by rw [← pow_mul]
      _ ≤ 6 * R ^ 1203 := by omega
      _ ≤ R * R ^ 1203 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 1203).symm
  exact ⟨hr, hd, hg, ha, hb, hf⟩

theorem finite_table_bits_budget (R n : ℕ) (hR : 2 ^ 64 ≤ R) (hn : n ≤ R) :
    tableBits (n, R ^ 100 + 1) ≤ R ^ 102 := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hk : 1 ≤ R ^ 100 := one_le_pow₀ hR1
  have hp : 1 ≤ R ^ 101 := one_le_pow₀ hR1
  calc
    _ ≤ 4 * n * (R ^ 100 + 1) + 1 := tableBits_linear _ _
    _ ≤ 4 * R * (2 * R ^ 100) + 1 := by gcongr <;> omega
    _ = 8 * R ^ 101 + 1 := by rw [pow_succ']; ring
    _ ≤ 9 * R ^ 101 := by omega
    _ ≤ R * R ^ 101 := Nat.mul_le_mul_right _ (by norm_num at hR; omega)
    _ = _ := (pow_succ' R 101).symm

theorem random_fuel_suffices (S : SpinLaw) (R N Q : ℕ) (hR : 2 ^ 64 ≤ R)
    (hN : N ≤ R) (hQ : Q ≤ R) (hA : (alphabet S).length ≤ R) :
    Q * ((16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) +
      acceptanceBits (R ^ 100) + N * spinBits S (R ^ 100)) ≤ R ^ 10000 := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hstep : 16 * 2048 ^ 2 * R ^ 12 ≤ R ^ 13 := by
    calc
      _ ≤ R * R ^ 12 := Nat.mul_le_mul_right _ (by norm_num at hR ⊢; omega)
      _ = _ := (pow_succ' R 12).symm
  have hnoise := (gaussian_numeric_bounds R hR).2.2.2.2.2
  have hspin : spinBits S (R ^ 100) ≤ R ^ 102 := finite_table_bits_budget R _ hR hA
  have hacc : acceptanceBits (R ^ 100) ≤ R ^ 102 := finite_table_bits_budget R 2 hR (by norm_num at hR; omega)
  have heuler : (16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) ≤ R ^ 1218 := by
    calc
      _ ≤ R ^ 13 * R * R ^ 1204 := by gcongr
      _ = _ := by rw [← pow_succ, ← pow_add]
  have hspins : N * spinBits S (R ^ 100) ≤ R ^ 103 := by
    calc
      _ ≤ R * R ^ 102 := Nat.mul_le_mul hN hspin
      _ = _ := (pow_succ' R 102).symm
  have h103 : R ^ 103 ≤ R ^ 1218 := Nat.pow_le_pow_right hR1 (by decide)
  have h102 : R ^ 102 ≤ R ^ 1218 := Nat.pow_le_pow_right hR1 (by decide)
  have htrial : (16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) +
      acceptanceBits (R ^ 100) + N * spinBits S (R ^ 100) ≤ R ^ 1219 := by
    calc
      _ ≤ 3 * R ^ 1218 := by omega
      _ ≤ R * R ^ 1218 := Nat.mul_le_mul_right _ (by norm_num at hR; omega)
      _ = _ := (pow_succ' R 1218).symm
  calc
    _ ≤ R * R ^ 1219 := Nat.mul_le_mul hQ htrial
    _ = R ^ 1220 := (pow_succ' R 1219).symm
    _ ≤ _ := Nat.pow_le_pow_right hR1 (by decide)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

theorem gaussianMeshDen_ge_square (k : ℕ) : (k + 1) ^ 2 ≤ gaussianMeshDen k := by
  have hp : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold gaussianMeshDen
  nlinarith

theorem gaussianNoiseBits_exp_fuel (k : ℕ) :
    2 * (gaussianMeshDen k) ^ 3 + 2 ≤ gaussianNoiseBits k := by
  rw [gaussianNoiseBits_budget]
  unfold gaussianCoinBudget
  omega

theorem gaussianNoiseBits_linear (k : ℕ) : 8 * (k + 1) ≤ gaussianNoiseBits k := by
  have hden : 4 * (k + 1) ≤ gaussianMeshDen k := by
    have hp : k + 1 ≤ (k + 1) ^ 4 := Nat.le_self_pow (by decide) _
    unfold gaussianMeshDen
    nlinarith
  have hden1 : 1 ≤ gaussianMeshDen k := by omega
  have hp : gaussianMeshDen k ≤ (gaussianMeshDen k) ^ 3 := Nat.le_self_pow (by decide) _
  have hh := gaussianNoiseBits_exp_fuel k
  omega

theorem reciprocal_exp_fuel (k D F : ℕ) (hD : 0 < D)
    (hDk : D ≤ gaussianMeshDen k) (hF : gaussianNoiseBits k ≤ F) :
    2 / (((1 / (D : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (F : ℝ) := by
  have hdR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : 2 / (((1 / (D : ℚ) : ℚ) : ℝ) ^ 3) + 2 = ((2 * D ^ 3 + 2 : ℕ) : ℝ) := by
    push_cast
    field_simp [hdR]
  rw [he]
  exact_mod_cast le_trans (show 2 * D ^ 3 + 2 ≤ 2 * (gaussianMeshDen k) ^ 3 + 2 from by gcongr)
    ((gaussianNoiseBits_exp_fuel k).trans hF)

theorem global_gaussian_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    gaussianNoiseBits (R ^ 100) ≤ R ^ 10000 :=
  (gaussian_numeric_bounds R hR).2.2.2.2.2.trans
    (Nat.pow_le_pow_right (by norm_num at hR; omega) (by decide))

theorem spin_exp_fuel (C R : ℕ) (hR : 2 ^ 64 ≤ R) (hC : 0 < C) (hCR : C ≤ R) :
    2 / (spinPrecision C (R ^ 100) : ℝ) ^ 3 + 2 ≤ (R ^ 10000 : ℕ) := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hC4 : C ^ 4 ≤ R ^ 100 := (Nat.pow_le_pow_left hCR 4).trans
    (Nat.pow_le_pow_right hR1 (by decide))
  have hd : C ^ 4 * (R ^ 100 + 1) ≤ gaussianMeshDen (R ^ 100) := by
    calc
      _ ≤ (R ^ 100 + 1) * (R ^ 100 + 1) := by gcongr; omega
      _ = (R ^ 100 + 1) ^ 2 := (pow_two _).symm
      _ ≤ _ := gaussianMeshDen_ge_square _
  have he := reciprocal_exp_fuel (R ^ 100) (C ^ 4 * (R ^ 100 + 1)) (R ^ 10000)
    (by positivity) hd (global_gaussian_fuel R hR)
  simpa only [spinPrecision, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast, Rat.cast_add] using he

theorem drift_exp_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    2 / (((1 / (R ^ 100 : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (R ^ 10000 : ℕ) := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hk : 0 < R ^ 100 := by positivity
  have hd : R ^ 100 ≤ gaussianMeshDen (R ^ 100) := by
    have hh := gaussianMeshDen_ge_square (R ^ 100)
    nlinarith
  have he := reciprocal_exp_fuel (R ^ 100) (R ^ 100) (R ^ 10000) hk hd (global_gaussian_fuel R hR)
  simpa only [Nat.cast_pow] using he

theorem integral_exp_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    2 / (((1 / ((R ^ 100 : ℕ) + 1 : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (R ^ 10000 : ℕ) := by
  have hd : R ^ 100 + 1 ≤ gaussianMeshDen (R ^ 100) := by
    have hh := gaussianMeshDen_ge_square (R ^ 100)
    nlinarith
  have he := reciprocal_exp_fuel (R ^ 100) (R ^ 100 + 1) (R ^ 10000) (by omega) hd
    (global_gaussian_fuel R hR)
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using he

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
open Matrix IsingLTL.BeliefProp
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

end CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCap
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

end CritWinSpin.Implementation.PreprocessCap
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelPrecisionBudget
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral

end CritWinSpin.Implementation.KernelPrecisionBudget
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp
variable {A : Type} [Fintype A]

def wordMass (r : Option A → ℝ) {q : ℕ} (xs : Fin q → Option A) : ℝ := ∏ i, r (xs i)

open Classical in
def wordLaw (r : Option A → ℝ) (q : ℕ) (z : Option A) : ℝ :=
  ∑ xs : Fin q → Option A, if firstSome xs = z then wordMass r xs else 0

theorem wordMass_sum {r : Option A → ℝ} (hr : IsDistribution r) (q : ℕ) :
    ∑ xs : Fin q → Option A, wordMass r xs = 1 := by
  simp only [wordMass, ← Fintype.prod_sum, hr.2, Finset.prod_const_one]

theorem wordLaw_eq_retry {r : Option A → ℝ} (hr : IsDistribution r) (q : ℕ) (z : Option A) :
    wordLaw r q z = retry r q z := by
  classical
  induction q generalizing z with
  | zero => cases z <;> simp [wordLaw, firstSome, wordMass, retry]
  | succ q ih =>
    unfold wordLaw
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (q + 1) => Option A))
      (fun xs : Fin (q + 1) → Option A => if firstSome xs = z then wordMass r xs else 0)]
    simp only [Fintype.sum_prod_type]
    rw [Fintype.sum_option]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, firstSome, Fin.cons_zero, Fin.cons_succ,
      wordMass, Fin.prod_univ_succ]
    have hn : (∑ xs : Fin q → Option A,
        if firstSome xs = z then r none * ∏ i, r (xs i) else 0) = r none * retry r q z := by
      rw [← ih z]
      unfold wordLaw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs _
      split_ifs <;> simp [wordMass]
    rw [hn]
    have hs (a : A) : (∑ xs : Fin q → Option A,
        if some a = z then r (some a) * ∏ i, r (xs i) else 0) =
        if some a = z then r (some a) else 0 := by
      split_ifs with ha
      · rw [← Finset.mul_sum]
        have hh := wordMass_sum hr q
        change (∑ xs : Fin q → Option A, ∏ i, r (xs i)) = 1 at hh
        rw [hh, mul_one]
      · simp
    simp_rw [hs]
    cases z with
    | none => simp [retry, next]
    | some z => simp [retry, next]; ring

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RetryPacketDecoding
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

theorem encRat_nonempty (q : ℚ) : encRat q ≠ [] := by
  unfold encRat encInt
  split_ifs <;> simp

theorem encConfig_nonempty {S : SpinLaw} {N : ℕ} (hN : 0 < N) (x : Config S (Fin N)) : encConfig x ≠ [] := by
  cases N with
  | zero => omega
  | succ n =>
    simp only [encConfig,List.ofFn_succ,List.flatten_cons]
    intro hh
    exact encRat_nonempty _ (List.append_eq_nil_iff.mp hh).1

theorem decConfig_nil (S : SpinLaw) (N : ℕ) (hN : 0 < N) : decConfig S N [] = none := by
  classical
  unfold decConfig
  split_ifs with h
  · obtain ⟨x,hx⟩ := h
    exact False.elim (encConfig_nonempty hN x hx)
  · rfl

def packet {S : SpinLaw} {N : ℕ} : Option (Config S (Fin N)) → List Bool
  | none => []
  | some x => encConfig x

theorem decode_packet {S : SpinLaw} {N : ℕ} (hN : 0 < N) (x : Option (Config S (Fin N))) :
    decConfig S N (packet x) = x := by
  cases x with
  | none => exact decConfig_nil S N hN
  | some x => exact decConfig_encConfig x

def selectFirst (outs : List (List Bool)) : List Bool :=
  (outs[outs.findIdx (fun bs => !bs.isEmpty)]?).getD []

theorem selectFirst_cons (bs : List Bool) (outs : List (List Bool)) :
    selectFirst (bs::outs) = if bs.isEmpty then selectFirst outs else bs := by
  cases h : bs.isEmpty <;> simp [selectFirst,List.findIdx_cons,h]

def firstSomeList {A : Type} : List (Option A) → Option A
  | [] => none
  | none::xs => firstSomeList xs
  | some a::_ => some a

theorem select_packets {S : SpinLaw} {N : ℕ} (hN : 0 < N) (xs : List (Option (Config S (Fin N)))) :
    selectFirst (xs.map packet) = packet (firstSomeList xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => simpa only [List.map_cons,packet,selectFirst_cons,List.isEmpty_nil,ite_true,firstSomeList] using ih
    | some x =>
      simp only [List.map_cons,packet,selectFirst_cons,firstSomeList]
      have hx : (encConfig x).isEmpty = false := List.isEmpty_eq_false_iff.mpr (encConfig_nonempty hN x)
      rw [hx]
      rfl

theorem firstSomeList_ofFn {A : Type} {q : ℕ} (xs : Fin q → Option A) :
    firstSomeList (List.ofFn xs) = FiniteRetry.firstSome xs := by
  induction q with
  | zero => simp [firstSomeList,FiniteRetry.firstSome]
  | succ q ih =>
    rw [List.ofFn_succ]
    cases hx : xs 0 with
    | none => simpa only [hx,firstSomeList,FiniteRetry.firstSome] using ih (fun i => xs i.succ)
    | some x => simp [hx,firstSomeList,FiniteRetry.firstSome]

theorem decode_selected_packets {S : SpinLaw} {N q : ℕ} (hN : 0 < N)
    (xs : Fin q → Option (Config S (Fin N))) :
    decConfig S N (selectFirst (List.ofFn (fun i => packet (xs i)))) = FiniteRetry.firstSome xs := by
  have hl : List.ofFn (fun i => packet (xs i)) = (List.ofFn xs).map packet := by
    simp only [List.map_ofFn,Function.comp_def]
  rw [hl,select_packets hN,decode_packet hN,firstSomeList_ofFn]

theorem packet_decode {S : SpinLaw} {N : ℕ} (hN : 0 < N) (bs : List Bool)
    (hb : bs=[] ∨ ∃ x : Config S (Fin N), bs=encConfig x) : packet (decConfig S N bs) = bs := by
  rcases hb with rfl | ⟨x,rfl⟩
  · rw [decConfig_nil S N hN]; rfl
  · rw [decConfig_encConfig]; rfl

theorem decode_selected_ofFn {S : SpinLaw} {N q : ℕ} (hN : 0 < N) (outs : Fin q → List Bool)
    (hValid : ∀ i, outs i=[] ∨ ∃ x : Config S (Fin N), outs i=encConfig x) :
    decConfig S N (selectFirst (List.ofFn outs)) = FiniteRetry.firstSome (fun i => decConfig S N (outs i)) := by
  have hl : List.ofFn outs = List.ofFn (fun i => packet (decConfig S N (outs i))) := by
    congr 1
    funext i
    exact (packet_decode hN (outs i) (hValid i)).symm
  rw [hl]
  exact decode_selected_packets hN _

end CritWinSpin.Implementation.RetryPacketDecoding
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

 theorem coins_eq_radius {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) :
    criticalCoins S C (encodedInput I.1,m) = (SamplerDataFacts.radius S C I m)^10000 := by
  simp only [criticalCoins,uniformBudget,SamplerDataFacts.radius,SamplerDataFacts.base_eq]

 theorem stepCount_le_coins {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) :
    samplerStepCount S C (sampleReference I m (criticalCoins S C (encodedInput I.1,m))) ≤
      criticalCoins S C (encodedInput I.1,m) := by
  let R := SamplerDataFacts.radius S C I m
  have hb := SamplerBudgetBounds.bounds C N m (SamplerDataFacts.trials S C I m) hC hm
  change 2^64 ≤ R ∧ _ at hb
  have hR1 : 1 ≤ R := by omega
  have hc : 16*2048^2 ≤ R := by norm_num at hb; omega
  have ht := (SamplerDataFacts.parameters S C I m (criticalCoins S C (encodedInput I.1,m))).2.2.2.2.2.2.2
  rw [ht,coins_eq_radius]
  change 16*2048^2*R^12 ≤ R^10000
  calc
    _ ≤ R*R^12 := Nat.mul_le_mul_right _ hc
    _ = R^13 := by ring
    _ ≤ _ := Nat.pow_le_pow_right hR1 (by decide)

 theorem actual_drift_fuel {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    0 < D.dPhi ∧ 2/(D.dPhi:ℝ)^3+2 ≤ D.fuel.length := by
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let R := SamplerDataFacts.radius S C I m
  have hb := SamplerBudgetBounds.bounds C N m (SamplerDataFacts.trials S C I m) hC hm
  change 2^64 ≤ R ∧ _ at hb
  have hR1 : 1 ≤ R := by omega
  have hp := (SamplerDataFacts.parameters S C I m F).2.1
  change (D.dPhi:ℝ) = 1/(R:ℝ)^100 at hp
  constructor
  · have hh : (0:ℝ) < D.dPhi := by rw [hp]; positivity
    exact_mod_cast hh
  · have hh := drift_exp_fuel R hb.1
    change 2/(D.dPhi:ℝ)^3+2 ≤ (List.replicate F ()).length
    rw [List.length_replicate,show F=R^10000 from coins_eq_radius S C I m,hp]
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast] using hh

end CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

theorem unitize_eq_replicate (bits : List Bool) : unitize bits = List.replicate bits.length () := by
  simp [unitize, List.map_const']

theorem samplerRoot_same_length (C : ℕ) (p : ParsedInput) (bits bits' : List Bool)
    (h : bits.length = bits'.length) : samplerRoot C (p, bits) = samplerRoot C (p, bits') := by
  unfold samplerRoot
  rw [unitize_eq_replicate, unitize_eq_replicate, h]
  rfl

theorem samplerDriftContext_same_length (S : SpinLaw) (C : ℕ) (p : ParsedInput)
    (bits bits' : List Bool) (h : bits.length = bits'.length) :
    samplerDriftContext S C (p, bits) = samplerDriftContext S C (p, bits') := by
  unfold samplerDriftContext
  rw [samplerRoot_same_length C p bits bits' h]
  rfl

theorem samplerEulerContext_same_length (S : SpinLaw) (C : ℕ) (p : ParsedInput)
    (bits bits' : List Bool) (h : bits.length = bits'.length) :
    samplerEulerContext S C (p, bits) = samplerEulerContext S C (p, bits') := by
  unfold samplerEulerContext
  rw [samplerDriftContext_same_length S C p bits bits' h]
  have hb : samplerStateBound S C (p, bits) = samplerStateBound S C (p, bits') := by
    unfold samplerStateBound
    rw [h]
    rfl
  rw [hb, unitize_eq_replicate, unitize_eq_replicate, h]
  rfl

theorem samplerTrialOutput_block (S : SpinLaw) (C : ℕ) (p : ParsedInput)
    (bits : List Bool) (i : ℕ) :
    samplerTrialOutput S C ((p, bits), i) =
      trialOnBlock S C p bits.length
        (bitBlock ((bits, samplerTrialBits S C (p, bits)), i)) := by
  have hlen : bits.length = (List.replicate bits.length false).length := by simp
  have hc := samplerEulerContext_same_length S C p bits _ hlen
  have hd := samplerDriftContext_same_length S C p bits _ hlen
  have hf : unitize bits = unitize (List.replicate bits.length false) := by
    simp [unitize_eq_replicate]
  unfold samplerTrialOutput samplerTrialState trialOnBlock
  rw [hc, hd, hf]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section

theorem samplerTrialBits_data {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    samplerTrialBits S C (encodedSamplerInput I m []) =
      (samplerStepCount S C (sampleReference I m F))*N*
        gaussianNoiseBits (sampleEulerData S C I m F).k +
      acceptanceBits (sampleEulerData S C I m F).k + N*spinBits S (sampleEulerData S C I m F).k := by
  simp only [samplerTrialBits,encodedSamplerInput,List.length_replicate]
  rfl

theorem actual_word_budgets {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) (hqC : (alphabet S).length ≤ C) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    let Q := trials S C I m
    Q ≤ F  ∧  Q*samplerTrialBits S C (encodedSamplerInput I m []) ≤ F  ∧ 
    (0 < D.dPhi  ∧  2/(D.dPhi:ℝ)^3+2 ≤ D.fuel.length)  ∧ 
    2/(spinPrecision C D.k:ℝ)^3+2 ≤ D.fuel.length  ∧  D.k+1 ≤ D.fuel.length  ∧ 
    2/(1/((D.k:ℝ)+1))^3+2 ≤ (D.fuel.length:ℝ) := by
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let Q := trials S C I m
  let R := radius S C I m
  have hb : 2^64 ≤ R  ∧  N+1 ≤ R  ∧  Q ≤ R  ∧  2*C ≤ R  ∧  C ≤ R := SamplerBudgetBounds.bounds C N m Q hC hm
  have hR1 : 1 ≤ R := by norm_num at hb; omega
  have hFR : F=R^10000 := SamplerCappedPath.coins_eq_radius S C I m
  have hk : D.k=R^100 := by simp only [D,sampleEulerData,samplerQuality,radius_eq,R]
  have hT := (parameters S C I m F).2.2.2.2.2.2.2
  have hFu : D.fuel.length=F := by simp only [D,sampleEulerData,List.length_replicate]
  have hRF : R ≤ F := by rw [hFR]; simpa only [pow_one] using Nat.pow_le_pow_right hR1 (show 1 ≤ (10000:ℕ) by decide)
  have hbits := random_fuel_suffices S R N Q hb.1 (by omega) hb.2.2.1 (hqC.trans hb.2.2.2.2)
  have hspin := spin_exp_fuel C R hb.1 (by omega) hb.2.2.2.2
  have hint := integral_exp_fuel R hb.1
  have htake : D.k+1 ≤ D.fuel.length := by
    rw [hFu,hFR,hk]
    have hh := (gaussianNoiseBits_linear (R^100)).trans (global_gaussian_fuel R hb.1)
    omega
  refine ⟨hb.2.2.1.trans hRF,?_,SamplerCappedPath.actual_drift_fuel S C I m hC hm,?_,htake,?_⟩
  · rw [samplerTrialBits_data S C I m F,hT,hk]
    change Q*(16*2048^2*R^12*N*gaussianNoiseBits (R^100)+
      acceptanceBits (R^100)+N*spinBits S (R^100)) ≤ F
    rw [hFR]
    exact hbits
  · rw [hFu,hFR,hk]
    exact hspin
  · rw [hFu,hFR,hk]
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_add,Rat.cast_pow] using hint

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem enumeratedWeights_nonneg {α : Type} (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hρ : ∀ x, 0 ≤ ρ x) (hU : ∀ x, E x ≤ U) :
    ∀ x, 0 ≤ enumeratedWeights E ρ U d x := by
  intro x
  exact mul_nonneg (hρ x) (expNegativeApprox_error (U - E x) d
    (sub_nonneg.mpr (hU x)) hd hd1).1

theorem enumeratedWeights_pivot {α : Type} (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (xstar : α) (hstar : E xstar = U) :
    enumeratedWeights E ρ U d xstar = ρ xstar := by
  simp [enumeratedWeights, hstar, expNegativeApprox_zero d hd]

theorem enumeratedWeights_sum_positive {α : Type} [Fintype α] (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hρ : ∀ x, 0 < ρ x) (hU : ∀ x, E x ≤ U)
    (xstar : α) (hstar : E xstar = U) : 0 < ∑ x, enumeratedWeights E ρ U d x := by
  have hw := enumeratedWeights_nonneg E ρ U d hd hd1 (fun x => (hρ x).le) hU
  have hp := Finset.single_le_sum (fun x _ => hw x) (Finset.mem_univ xstar)
  rw [enumeratedWeights_pivot E ρ U d hd xstar hstar] at hp
  exact (hρ xstar).trans_le hp

theorem normalizedRational_distribution {α : Type} [Fintype α] (w : α → ℚ)
    (hw : ∀ x, 0 ≤ w x) (hW : 0 < ∑ x, w x) :
    IsDistribution (fun x => (w x : ℝ) / ∑ y, (w y : ℝ)) := by
  have hWr : (0 : ℝ) < ∑ x, (w x : ℝ) := by exact_mod_cast hW
  refine ⟨fun x => div_nonneg (by exact_mod_cast hw x) hWr.le, ?_⟩
  rw [← Finset.sum_div]
  exact div_self hWr.ne'

theorem tvDist_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (p q : β → ℝ) : tvDist (fun a => p (e a)) (fun a => q (e a)) = tvDist p q := by
  unfold tvDist
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp CritWinSpin.Implementation.EnvelopeAnalysis
noncomputable section

def spinWeightApprox (S : SpinLaw) (t d : ℚ) (a : {a : ℚ // a ∈ S.A}) : ℚ :=
  enumeratedWeights (fun b : {a : ℚ // a ∈ S.A} => t * b.1)
    (fun b => S.ρ b.1) |t| d a

theorem spin_shift_max (S : SpinLaw) (t : ℚ) (a : {a : ℚ // a ∈ S.A}) : t * a.1 ≤ |t| := by
  have ha : |a.1| ≤ 1 := abs_le.mpr (S.mem_Icc a.1 a.2)
  calc
    _ ≤ |t * a.1| := le_abs_self _
    _ = |t| * |a.1| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    _ = _ := mul_one _

theorem spin_pivot (S : SpinLaw) (t : ℚ) :
    ∃ a : {a : ℚ // a ∈ S.A}, t * a.1 = |t| ∧ S.ρ a.1 = S.ρ 1 := by
  by_cases ht : t < 0
  · refine ⟨⟨-1, S.neg_one_mem⟩, ?_, S.symm 1 S.one_mem⟩
    simp [abs_of_neg ht]
  · refine ⟨⟨1, S.one_mem⟩, ?_, rfl⟩
    simp [abs_of_nonneg (le_of_not_gt ht)]

theorem normalized_exp_eq_tilt (S : SpinLaw) (t : ℚ) :
    (fun a : {a : ℚ // a ∈ S.A} =>
      (Real.exp ((t * a.1 : ℚ) : ℝ) * (S.ρ a.1 : ℝ)) /
        ∑ b : {a : ℚ // a ∈ S.A}, Real.exp ((t * b.1 : ℚ) : ℝ) * (S.ρ b.1 : ℝ)) =
      (fun a => tilt S (t : ℝ) a.1) := by
  have hsum : (∑ b : {a : ℚ // a ∈ S.A}, Real.exp ((t * b.1 : ℚ) : ℝ) * (S.ρ b.1 : ℝ)) =
      mgf S (t : ℝ) := by
    rw [Finset.sum_coe_sort S.A (fun b : ℚ => Real.exp ((t * b : ℚ) : ℝ) * (S.ρ b : ℝ))]
    unfold mgf
    apply Finset.sum_congr rfl
    intro b _
    push_cast
    ring
  funext a
  rw [hsum]
  unfold tilt
  change Real.exp ((t * a.1 : ℚ) : ℝ) * (S.ρ a.1 : ℝ) / mgf S (t : ℝ) =
    (S.ρ a.1 : ℝ) * Real.exp ((t : ℝ) * (a.1 : ℝ) - Real.log (mgf S (t : ℝ)))
  rw [Real.exp_sub, Real.exp_log (mgf_pos S (t : ℝ))]
  push_cast
  ring

theorem spinWeightApprox_facts (S : SpinLaw) (t d : ℚ) (hd : 0 < d) (hd1 : d ≤ 1) :
    (∀ a, 0 ≤ spinWeightApprox S t d a) ∧
      (0 < ∑ a, spinWeightApprox S t d a) ∧
      tvDist (fun a => (spinWeightApprox S t d a : ℝ) / ∑ b, (spinWeightApprox S t d b : ℝ))
        (fun a => tilt S (t : ℝ) a.1) ≤
          (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  obtain ⟨a, hmax, hρa⟩ := spin_pivot S t
  let E : {a : ℚ // a ∈ S.A} → ℚ := fun a => t * a.1
  let ρ : {a : ℚ // a ∈ S.A} → ℚ := fun a => S.ρ a.1
  have hρ : ∀ a, 0 < ρ a ∧ ρ a ≤ 1 := fun a =>
    ⟨S.pos a.1 a.2, (spin_weight_bounds S a.1 a.2).2⟩
  refine ⟨enumeratedWeights_nonneg E ρ |t| d hd hd1 (fun a => (hρ a).1.le)
    (spin_shift_max S t), ?_, ?_⟩
  · exact enumeratedWeights_sum_positive E ρ |t| d hd hd1 (fun a => (hρ a).1)
      (spin_shift_max S t) a hmax
  · have hh := enumeratedWeights_tv E ρ |t| d hd hd1 hρ (spin_shift_max S t) a hmax
    rw [normalized_exp_eq_tilt S t] at hh
    simpa only [ρ, hρa, E, spinWeightApprox] using hh

theorem alphabet_positive (S : SpinLaw) : 0 < (alphabet S).length := by
  have hh : (alphabet S) ≠ [] := by
    intro he
    have hm : (1 : ℚ) ∈ alphabet S := Finset.mem_toList.mpr S.one_mem
    rw [he] at hm
    simp at hm
  cases he : alphabet S with
  | nil => exact False.elim (hh he)
  | cons a as => simp

theorem alphabet_ofFn (S : SpinLaw) :
    alphabet S = List.ofFn (fun i => ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ)) := by
  apply List.ext_getElem <;> simp [alphabetEquiv_value]

theorem spinDrawWeights_correct (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (hc : 0 < C) (bits : List Bool) (fuel : List Unit)
    (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length) :
    spinDrawWeights S C (((t, k), bits), fuel) =
      List.ofFn (fun i => spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i)) := by
  have hd : 0 < spinPrecision C k := by unfold spinPrecision; positivity
  unfold spinDrawWeights spinTable
  conv_lhs => rw [alphabet_ofFn S, List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  have habs : (if t < 0 then -t else t) = |t| := by
    by_cases ht : t < 0 <;> simp [ht, abs_of_neg, abs_of_nonneg, le_of_not_gt]
  rw [habs]
  change S.ρ ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ) *
    expWithFuel ((|t| - t * ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ), spinPrecision C k), fuel) = _
  rw [expWithFuel_eq_uniform _ _ (sub_nonneg.mpr (spin_shift_max S t (alphabetEquiv S i))) hd fuel hf]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

def indexSpinWeight (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (i : Fin (alphabet S).length) : ℚ :=
  spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i)

def indexSpinProb (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (i : Fin (alphabet S).length) : ℝ :=
  (indexSpinWeight S C t k i : ℝ) / ∑ j, (indexSpinWeight S C t k j : ℝ)

theorem spinPrecision_valid (C k : ℕ) (hC : 0 < C) :
    0 < spinPrecision C k ∧ spinPrecision C k ≤ 1 := by
  have hC1 : (1 : ℚ) ≤ C := by exact_mod_cast hC
  have hk1 : (1 : ℚ) ≤ (k : ℚ) + 1 := by have := Nat.cast_nonneg (α := ℚ) k; linarith
  have hden : 1 ≤ (C : ℚ) ^ 4 * ((k : ℚ) + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hk1
  unfold spinPrecision
  exact ⟨by positivity, (div_le_one (by positivity)).mpr hden⟩

theorem indexSpinProb_facts (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C) :
    IsDistribution (indexSpinProb S C t k) ∧
      tvDist (indexSpinProb S C t k)
        (fun i => tilt S (t : ℝ) ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ)) ≤
          ((alphabet S).length : ℝ) * spinPrecision C k / (S.ρ 1 : ℝ) := by
  obtain ⟨hd, hd1⟩ := spinPrecision_valid C k hC
  obtain ⟨hw, hW, htv⟩ := spinWeightApprox_facts S t (spinPrecision C k) hd hd1
  have hsumQ : (∑ i, indexSpinWeight S C t k i) = ∑ a, spinWeightApprox S t (spinPrecision C k) a :=
    Fintype.sum_equiv (alphabetEquiv S) _ _ (fun _ => rfl)
  have hsumR : (∑ i, (indexSpinWeight S C t k i : ℝ)) =
      ∑ a, (spinWeightApprox S t (spinPrecision C k) a : ℝ) := by exact_mod_cast hsumQ
  have hp : IsDistribution (indexSpinProb S C t k) := normalizedRational_distribution
    (indexSpinWeight S C t k) (fun i => hw (alphabetEquiv S i)) (by rw [hsumQ]; exact hW)
  refine ⟨hp, ?_⟩
  have he : indexSpinProb S C t k = fun i =>
      (spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i) : ℝ) /
        ∑ a, (spinWeightApprox S t (spinPrecision C k) a : ℝ) := by
    funext i
    rw [indexSpinProb, hsumR]
    rfl
  rw [he, tvDist_equiv (alphabetEquiv S)
    (fun a : {a : ℚ // a ∈ S.A} =>
      (spinWeightApprox S t (spinPrecision C k) a : ℝ) /
        ∑ b, (spinWeightApprox S t (spinPrecision C k) b : ℝ))
    (fun a => tilt S (t : ℝ) a.1)]
  have hc : Fintype.card {a : ℚ // a ∈ S.A} = (alphabet S).length := by simp [alphabet]
  simpa only [hc] using htv

def spinTicketCounts (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) : Fin (alphabet S).length → ℕ :=
  DyadicRounding.counts (indexSpinProb S C t k) (2 ^ spinBits S k) ⟨0, alphabet_positive S⟩

theorem spinTicketCounts_total (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C) :
    ∑ i, spinTicketCounts S C t k i = 2 ^ spinBits S k :=
  DyadicRounding.counts_total _ (indexSpinProb_facts S C t k hC).1 _ _

theorem spinDraw_ofFn (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length)
    (ω : Fin (spinBits S k) → Bool) :
    spinDraw S C (((t, k), List.ofFn ω), fuel) =
      ((alphabetEquiv S (FiniteTicket.drawIndex (spinBits S k) (spinTicketCounts S C t k)
        (spinTicketCounts_total S C t k hC) ω) : {a : ℚ // a ∈ S.A}) : ℚ) := by
  have hw := spinDrawWeights_correct S C t k hC (List.ofFn ω) fuel hf
  have hv := sampleScalarTable_ofFn
    (fun i => ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ))
    (spinBits S k) (spinTicketCounts S C t k) (spinTicketCounts_total S C t k hC) ω
  rw [← alphabet_ofFn S] at hv
  unfold spinDraw
  rw [hw]
  change sampleScalarTable ((alphabet S,
    quantizedCounts (List.ofFn (indexSpinWeight S C t k), 2 ^ spinBits S k)),
      (List.ofFn ω).take (spinBits S k)) = _
  rw [quantizedCounts_ofFn_pos (alphabet_positive S)]
  have htape : (List.ofFn ω).take (spinBits S k) = List.ofFn ω := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn ω))
  rw [htape]
  exact hv

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical
noncomputable section

theorem EulerData.kernelFields_ofFn {N : ℕ} (D : EulerData N) (z : Fin N → ℚ) (bits : List Bool) :
    kernelFields (D.kernelInput z bits) = List.ofFn (D.fields z) := by
  unfold kernelFields driftArguments EulerData.kernelInput EulerData.context EulerData.fields
  rw [matrixVector_ofFn, zip_ofFn, List.map_ofFn]
  rfl

theorem EulerData.kernelAcceptance_independent {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (z : Fin N → ℚ) (bits : List Bool) :
    kernelAcceptance S (D.kernelInput z bits) = kernelAcceptance S (D.kernelInput z []) := by
  unfold kernelAcceptance kernelIntegralSum
  rw [D.kernelFields_ofFn z bits, D.kernelFields_ofFn z []]
  rfl

def kernelPacket {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) : List Bool :=
  List.ofFn a ++ (List.ofFn (fun i => List.ofFn (w i))).flatten

theorem kernelPacket_take {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    (kernelPacket S k a w).take (acceptanceBits k) = List.ofFn a := by
  exact List.take_left' (by simp only [List.length_ofFn])

theorem kernelPacket_drop {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    (kernelPacket S k a w).drop (acceptanceBits k) =
      (List.ofFn (fun i => List.ofFn (w i))).flatten := by
  exact List.drop_left' (by simp only [List.length_ofFn])

theorem spinPacket_block {N : ℕ} (S : SpinLaw) (k : ℕ)
    (w : Fin N → Fin (spinBits S k) → Bool) (i : Fin N) :
    bitBlock (((List.ofFn (fun i => List.ofFn (w i))).flatten, spinBits S k), i.val) = List.ofFn (w i) := by
  have hr : ∀ row ∈ List.ofFn (fun i => List.ofFn (w i)), row.length = spinBits S k := by
    intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    simp only [List.length_ofFn]
  have hh := flattened_block (List.ofFn (fun i => List.ofFn (w i))) (spinBits S k) hr [] i.val
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.append_nil, List.getElem_ofFn, bitBlock] using hh

def spinTyped (S : SpinLaw) (C : ℕ) (hC : 0 < C) (t : ℚ) (k : ℕ)
    (w : Fin (spinBits S k) → Bool) : {a : ℚ // a ∈ S.A} :=
  alphabetEquiv S (FiniteTicket.drawIndex (spinBits S k) (spinTicketCounts S C t k)
    (spinTicketCounts_total S C t k hC) w)

theorem kernelSpinValues_packet {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (a : Fin (acceptanceBits D.k) → Bool) (w : Fin N → Fin (spinBits S D.k) → Bool) :
    kernelSpinValues S C (D.kernelInput z (kernelPacket S D.k a w)) =
      List.ofFn (fun i => (spinTyped S C hC (D.fields z i) D.k (w i) : ℚ)) := by
  unfold kernelSpinValues
  rw [D.kernelFields_ofFn]
  change (siteNumbers (List.replicate N ())).map (fun i => spinDraw S C
    (((((List.ofFn (D.fields z))[i]?).getD 0, D.k),
      bitBlock (((kernelPacket S D.k a w).drop (acceptanceBits D.k), spinBits S D.k), i)), D.fuel)) = _
  rw [kernelPacket_drop]
  simp only [siteNumbers, List.length_replicate]
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  rw [spinPacket_block]
  exact spinDraw_ofFn S C (D.fields z i) D.k hC D.fuel hf (w i)

theorem kernelOutput_packet {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (a : Fin (acceptanceBits D.k) → Bool) (w : Fin N → Fin (spinBits S D.k) → Bool) :
    kernelOutput S C (D.kernelInput z (kernelPacket S D.k a w)) =
      if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []), D.k), List.ofFn a) then
        encConfig (fun i => spinTyped S C hC (D.fields z i) D.k (w i)) else [] := by
  unfold kernelOutput
  rw [D.kernelAcceptance_independent S z, kernelSpinValues_packet S C hC D z hf a w]
  change (if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []), D.k),
    (kernelPacket S D.k a w).take (acceptanceBits D.k)) then _ else _) = _
  rw [kernelPacket_take, ofFn_flatMap]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

def joinNoiseWords {B : ℕ} (words : List (Fin B → Bool)) : List Bool := words.flatMap List.ofFn

theorem eulerFold_of_words {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (words : List (Fin (N * gaussianNoiseBits D.k) → Bool)) (z : Fin N → ℚ) (tail : List Bool) :
    (List.replicate words.length ()).foldl (fun st _ => eulerStep S st)
      (D.context, (List.ofFn z, joinNoiseWords words ++ tail)) =
        (D.context, (List.ofFn (words.foldl (D.cappedNext S) z), tail)) := by
  induction words generalizing z with
  | nil => simp [joinNoiseWords]
  | cons w words ih =>
      simp only [List.length_cons, List.replicate_succ, List.foldl_cons,
        joinNoiseWords, List.flatMap_cons, List.append_assoc]
      rw [eulerStep_ofFn S D hd hf]
      exact ih (D.cappedNext S z w)

theorem take_unitize (bits : List Bool) (T : ℕ) (hT : T ≤ bits.length) :
    (unitize bits).take T = List.replicate T () := by
  rw [show unitize bits = List.replicate bits.length () by simp [unitize, List.map_const']]
  simp only [List.take_replicate, Nat.min_eq_left hT]

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

theorem EulerData.trialCode_of_words {N : ℕ} (D : EulerData N) (S : SpinLaw) (C T : ℕ)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ)^3 + 2 ≤ D.fuel.length)
    (words : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    D.trialCode S C T (joinNoiseWords (List.ofFn words) ++ tail) =
      kernelOutput S C (D.kernelInput ((List.ofFn words).foldl (D.cappedNext S) (fun _ => 0)) tail) := by
  unfold EulerData.trialCode
  have he := eulerFold_of_words S D hd hf (List.ofFn words) (fun _ => 0) tail
  simp only [List.length_ofFn] at he
  rw [he]
  rfl

theorem trialOnBlock_data {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ)
    (hT : samplerStepCount S C (sampleReference I m F) ≤ F) (bits : List Bool) :
    trialOnBlock S C (encodedSamplerInput I m []).1 F bits =
      (sampleEulerData S C I m F).trialCode S C
        (samplerStepCount S C (sampleReference I m F)) bits := by
  let D := sampleEulerData S C I m F
  have hctx := sampleEulerData_context S C I m F
  have hdc : D.context.1 = samplerDriftContext S C (sampleReference I m F) := congrArg Prod.fst hctx
  have hzero : ((encodedSamplerInput I m []).1.1.2.map (fun _ => (0 : ℚ))) =
      List.ofFn (fun _ : Fin N => (0 : ℚ)) := by
    simp only [encodedSamplerInput, instanceListModel, List.map_ofFn, Function.comp_def, List.map_replicate, List.ofFn_const]
  have hbuf : unitize (sampleReference I m F).2 = List.replicate F () := by
    simp only [sampleReference, encodedSamplerInput, unitize, List.map_replicate]
  have htake : (unitize (sampleReference I m F).2).take
      (samplerStepCount S C (sampleReference I m F)) =
      List.replicate (samplerStepCount S C (sampleReference I m F)) () := by
    rw [hbuf, List.take_replicate, Nat.min_eq_left hT]
  have hfold : (((unitize (sampleReference I m F).2).take
      (samplerStepCount S C (sampleReference I m F))).foldl (fun st _ => eulerStep S st)
      (samplerEulerContext S C (sampleReference I m F),
        ((encodedSamplerInput I m []).1.1.2.map (fun _ => (0 : ℚ)),bits))) =
      (List.replicate (samplerStepCount S C (sampleReference I m F)) ()).foldl
        (fun st _ => eulerStep S st) (D.context,(List.ofFn (fun _ : Fin N => (0:ℚ)),bits)) := by
    rw [htake,hzero,← hctx]
  unfold trialOnBlock EulerData.trialCode
  apply congrArg (kernelOutput S C)
  rw [show ((encodedSamplerInput I m []).1,List.replicate F false) = sampleReference I m F from rfl]
  rw [hfold,hbuf,← hdc]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open IsingLTL.BeliefProp Classical
noncomputable section

theorem expectation {W A : Type} [Fintype W] [Fintype A] (draw : W → A) (f : A → ℝ) :
    (1 / (Fintype.card W : ℝ)) * ∑ w, f (draw w) = ∑ a, f a * law draw a := by
  have hp (w : W) : f (draw w) = ∑ a, f a * if draw w = a then (1 : ℝ) else 0 := by simp
  simp_rw [hp]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  unfold law
  ring

theorem distribution {W A : Type} [Fintype W] [Nonempty W] [Fintype A] (draw : W → A) :
    IsDistribution (law draw) := by
  have hc : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card W ≠ 0)
  refine ⟨fun a => by unfold law; positivity, ?_⟩
  have he := expectation draw (fun _ => (1 : ℝ))
  simpa [hc] using he.symm

theorem compose {W A B : Type} [Fintype W] [Fintype A] [Fintype B]
    (draw : W → A) (f : A → B) (b : B) :
    law (f ∘ draw) b = ∑ a, if f a = b then law draw a else 0 := by
  have he := expectation draw (fun a => if f a = b then (1 : ℝ) else 0)
  simpa [law, Function.comp_def, ite_mul] using he

theorem product {I W A : Type} [Fintype I] [DecidableEq I] [Fintype W] [Fintype A]
    (draw : I → W → A) (a : I → A) :
    law (fun ω : I → W => fun i => draw i (ω i)) a = ∏ i, law (draw i) (a i) := by
  have hp (ω : I → W) :
      (@ite ℝ ((fun i => draw i (ω i)) = a) (Classical.propDecidable _) 1 0) =
        ∏ i, if draw i (ω i) = a i then (1 : ℝ) else 0 := by
    by_cases h : ∀ i, draw i (ω i) = a i
    · have he : (fun i => draw i (ω i)) = a := funext h
      simp [he, h]
    · have he : (fun i => draw i (ω i)) ≠ a := by intro he; apply h; intro i; exact congrFun he i
      rw [if_neg he]
      symm
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold law
  have hs : (∑ ω : I → W, @ite ℝ ((fun i => draw i (ω i)) = a) (Classical.propDecidable _) 1 0) =
      ∑ ω : I → W, ∏ i, if draw i (ω i) = a i then (1 : ℝ) else 0 :=
    Finset.sum_congr rfl (fun ω _ => hp ω)
  rw [hs, ← Fintype.prod_sum (fun i (w : W) => if draw i w = a i then (1 : ℝ) else 0)]
  simp only [Fintype.card_fun, Nat.cast_pow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, one_div, inv_pow]

theorem retry {W A : Type} [Fintype W] [Nonempty W] [Fintype A]
    (draw : W → Option A) (Q : ℕ) :
    law (fun ω : Fin Q → W => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (ω i))) = CritWinSpin.Implementation.FiniteRetry.retry (law draw) Q := by
  funext a
  rw [show (fun ω : Fin Q → W => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (ω i))) = CritWinSpin.Implementation.FiniteRetry.firstSome ∘
        (fun ω : Fin Q → W => fun i => draw (ω i)) by rfl, compose]
  have hh : (∑ xs : Fin Q → Option A, @ite ℝ (CritWinSpin.Implementation.FiniteRetry.firstSome xs = a)
      (Classical.propDecidable _) (law (fun ω : Fin Q → W => fun i => draw (ω i)) xs) 0) =
      CritWinSpin.Implementation.FiniteRetry.wordLaw (law draw) Q a := by
    unfold CritWinSpin.Implementation.FiniteRetry.wordLaw CritWinSpin.Implementation.FiniteRetry.wordMass
    apply Finset.sum_congr rfl
    intro xs _
    split_ifs
    · exact product (fun _ : Fin Q => draw) xs
    · rfl
  exact hh.trans (CritWinSpin.Implementation.FiniteRetry.wordLaw_eq_retry (distribution draw) Q a)

theorem source_equiv {U W A : Type} [Fintype U] [Fintype W] [Fintype A]
    (e : U ≃ W) (draw : W → A) : law (draw ∘ e) = law draw := by
  funext a
  unfold law
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
noncomputable section
open IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteKernelTV
variable {A : Type} [Fintype A]

end CritWinSpin.Implementation.FiniteKernelTV
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelAcceptance
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral

end CritWinSpin.Implementation.KernelAcceptance
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
noncomputable section

def kernelPacketEquiv (S : SpinLaw) (N k : ℕ) :
    ((Fin (acceptanceBits k) → Bool) × (Fin N → Fin (spinBits S k) → Bool)) ≃
      (Fin (acceptanceBits k + N * spinBits S k) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (splitBitEquiv N (spinBits S k)).symm).trans
    (Fin.appendEquiv (acceptanceBits k) (N * spinBits S k))

theorem kernelPacketEquiv_list {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    List.ofFn (kernelPacketEquiv S N k (a,w)) = kernelPacket S k a w := by
  change List.ofFn (Fin.append a ((splitBitEquiv N (spinBits S k)).symm w)) = _
  rw [List.ofFn_fin_append, List.ofFn_mul]
  unfold kernelPacket
  apply congrArg (fun rows : List (List Bool) => List.ofFn a ++ rows.flatten)
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hh := congrFun (congrFun ((splitBitEquiv N (spinBits S k)).apply_symm_apply w) i) j
  simpa only [splitBitEquiv_apply, blockIndex] using hh

theorem kernelOutput_valid_ofFn {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (w : Fin (acceptanceBits D.k+N*spinBits S D.k) → Bool) :
    kernelOutput S C (D.kernelInput z (List.ofFn w)) = [] ∨
      ∃ x : Config S (Fin N), kernelOutput S C (D.kernelInput z (List.ofFn w)) = encConfig x := by
  let aw := (kernelPacketEquiv S N D.k).symm w
  have hw : List.ofFn w = kernelPacket S D.k aw.1 aw.2 := by
    simpa only [aw, Prod.mk.eta, Equiv.apply_symm_apply] using kernelPacketEquiv_list S D.k aw.1 aw.2
  rw [hw,kernelOutput_packet S C hC D z hf aw.1 aw.2]
  split_ifs
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open Classical IsingLTL.BeliefProp
noncomputable section

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

def packet (T B A : ℕ) :
    ((Fin T → Fin B → Bool) × (Fin A → Bool)) ≃ (Fin (T*B+A) → Bool) :=
  (Equiv.prodCongr (splitBitEquiv T B).symm (Equiv.refl _)).trans
    (Fin.appendEquiv (T*B) A)

theorem packet_apply {T B A : ℕ} (w : Fin T → Fin B → Bool) (v : Fin A → Bool) :
    packet T B A (w,v) = Fin.append ((splitBitEquiv T B).symm w) v := by
  rfl

theorem split_list {T B : ℕ} (w : Fin T → Fin B → Bool) :
    List.ofFn ((splitBitEquiv T B).symm w) = joinNoiseWords (List.ofFn w) := by
  rw [List.ofFn_mul]
  unfold joinNoiseWords
  rw [ofFn_flatMap]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  have hh := congrFun (congrFun ((splitBitEquiv T B).apply_symm_apply w) i) j
  simpa only [splitBitEquiv_apply,blockIndex] using hh

theorem packet_list {T B A : ℕ} (w : Fin T → Fin B → Bool) (v : Fin A → Bool) :
    List.ofFn (packet T B A (w,v)) = joinNoiseWords (List.ofFn w) ++ List.ofFn v := by
  have h1 := congrArg (fun f : Fin (T*B+A) → Bool => List.ofFn f) (packet_apply w v)
  have h2 := List.ofFn_fin_append ((splitBitEquiv T B).symm w) v
  have h3 := congrArg (fun xs : List Bool => xs ++ List.ofFn v) (split_list w)
  exact h1.trans (h2.trans h3)

end CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
noncomputable section
attribute [local irreducible] EulerData.trialCode kernelOutput

def trialPacketEquiv {N : ℕ} (S : SpinLaw) (D : EulerData N) (T : ℕ) :
    ((Fin T → Fin (N * gaussianNoiseBits D.k) → Bool) ×
      (Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool)) ≃
    (Fin (T * (N * gaussianNoiseBits D.k) + (acceptanceBits D.k + N * spinBits S D.k)) → Bool) :=
  GenericPacketLaw.packet T (N*gaussianNoiseBits D.k) (acceptanceBits D.k+N*spinBits S D.k)

theorem trialPacketEquiv_list {N : ℕ} (S : SpinLaw) (D : EulerData N) (T : ℕ)
    (w : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool)
    (v : Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool) :
    List.ofFn (trialPacketEquiv S D T (w,v)) = joinNoiseWords (List.ofFn w) ++ List.ofFn v := by
  exact GenericPacketLaw.packet_list w v

theorem EulerData.trialCode_valid {N : ℕ} (D : EulerData N) (S : SpinLaw) (C T : ℕ) (hC : 0<C)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi:ℝ)^3+2 ≤ D.fuel.length)
    (hfSpin : 2 / (spinPrecision C D.k:ℝ)^3+2 ≤ D.fuel.length)
    (w : Fin (T*(N*gaussianNoiseBits D.k)+(acceptanceBits D.k+N*spinBits S D.k)) → Bool) :
    D.trialCode S C T (List.ofFn w) = [] ∨
      ∃ x : Config S (Fin N), D.trialCode S C T (List.ofFn w) = encConfig x := by
  let wv := (trialPacketEquiv S D T).symm w
  have hw : List.ofFn w = joinNoiseWords (List.ofFn wv.1) ++ List.ofFn wv.2 := by
    simpa only [wv,Prod.mk.eta,Equiv.apply_symm_apply] using trialPacketEquiv_list S D T wv.1 wv.2
  rw [hw,D.trialCode_of_words S C T hd hf]
  exact kernelOutput_valid_ofFn S C hC D _ hfSpin wv.2

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open CritWinSpin.Implementation
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Classical
noncomputable section

namespace FiniteDraw

theorem law_bits_length {A : Type} [Fintype A] {L M : ℕ} (h : L=M) (draw : List Bool → A) :
    law (fun w : Fin L → Bool => draw (List.ofFn w)) =
      law (fun w : Fin M → Bool => draw (List.ofFn w)) := by
  cases h
  rfl

theorem law_prefix {A : Type} [Fintype A] (L R : ℕ) (draw : (Fin L → Bool) → A) :
    law (fun w : Fin (L+R) → Bool => draw (fun i => w (Fin.castAdd R i))) = law draw := by
  funext a
  unfold law
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  exact FiniteTicket.unused_bits_expectation L R (fun w =>
    @ite ℝ (draw w = a) (Classical.propDecidable _) 1 0)

theorem retry_bits {A : Type} [Fintype A] (Q L : ℕ)
    (draw : (Fin L → Bool) → Option A) :
    law (fun w : Fin (Q*L) → Bool => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (Compiled.splitBitEquiv Q L w i))) =
        CritWinSpin.Implementation.FiniteRetry.retry (law draw) Q := by
  have he := source_equiv (Compiled.splitBitEquiv Q L)
    (fun w : Fin Q → Fin L → Bool => CritWinSpin.Implementation.FiniteRetry.firstSome (fun i => draw (w i)))
  exact he.trans (retry draw Q)

end FiniteDraw

namespace Compiled

theorem samplerTrialBits_independent (S : SpinLaw) (C : ℕ) (p : ParsedInput) (bs : List Bool) :
    samplerTrialBits S C (p,bs) = samplerTrialBits S C (p,[]) := rfl

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.criticalWindowMachine CritWinSpin.LocalTM2.Compiled.kernelOutput CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.trialOnBlock CritWinSpin.LocalTM2.Compiled.samplerRetryOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot CritWinSpin.Implementation.FiniteRetry.retry CritWinSpin.LocalTM2.FiniteDraw.law

theorem samplerTrialOutputs_ofFn (S : SpinLaw) (C : ℕ) (p : ParsedInput) (F : ℕ)
    (Q : ℕ) (hQ : retryCount S C (samplerPre (p,[]),p.2) = Q)
    (hQF : Q ≤ F) (w : Fin F → Bool) :
    samplerTrialOutputs S C (p,List.ofFn w) = List.ofFn (fun i : Fin Q =>
      trialOnBlock S C p F (bitBlock ((List.ofFn w,samplerTrialBits S C (p,[])),i.val))) := by
  let bits := List.ofFn w
  have hTake : (unitize bits).take (retryCount S C (samplerPre (p,[]),p.2)) = List.replicate Q () :=
    (congrArg (fun n : ℕ => (unitize bits).take n) hQ).trans
      (take_unitize bits Q (by simpa only [bits,List.length_ofFn] using hQF))
  have hIndex : siteNumbers ((unitize bits).take (retryCount S C (samplerPre (p,[]),p.2))) =
      List.range Q := (congrArg siteNumbers hTake).trans (by simp only [siteNumbers,List.length_replicate])
  have hPoint (i : Fin Q) : samplerTrialOutput S C ((p,bits),i.val) =
      trialOnBlock S C p F (bitBlock ((bits,samplerTrialBits S C (p,[])),i.val)) := by
    have hLength : bits.length=F := List.length_ofFn
    have hBlock : bitBlock ((bits,samplerTrialBits S C (p,bits)),i.val) =
        bitBlock ((bits,samplerTrialBits S C (p,[])),i.val) :=
      congrArg (fun n : ℕ => bitBlock ((bits,n),i.val)) (samplerTrialBits_independent S C p bits)
    exact (samplerTrialOutput_block S C p bits i.val).trans
      (congrArg₂ (fun (fuel : ℕ) (bs : List Bool) => trialOnBlock S C p fuel bs) hLength hBlock)
  calc
    samplerTrialOutputs S C (p,List.ofFn w) =
        (List.range Q).map (fun i => samplerTrialOutput S C ((p,bits),i)) := by
      unfold samplerTrialOutputs
      exact congrArg (fun ids : List ℕ => ids.map (fun i => samplerTrialOutput S C ((p,bits),i))) hIndex
    _ = List.ofFn (fun i : Fin Q => samplerTrialOutput S C ((p,bits),i.val)) :=
      map_range_eq_ofFn Q (fun i => samplerTrialOutput S C ((p,bits),i))
    _ = _ := congrArg List.ofFn (funext hPoint)
end

theorem samplerRetryOutput_decoded {N : ℕ} (S : SpinLaw) (C : ℕ) (p : ParsedInput)
    (F Q : ℕ) (hN : 0 < N) (hQ : retryCount S C (samplerPre (p,[]),p.2) = Q)
    (hQF : Q ≤ F) (w : Fin F → Bool)
    (hValid : ∀ i : Fin Q, trialOnBlock S C p F
      (bitBlock ((List.ofFn w,samplerTrialBits S C (p,[])),i.val)) = [] ∨
        ∃ x : Config S (Fin N), trialOnBlock S C p F
          (bitBlock ((List.ofFn w,samplerTrialBits S C (p,[])),i.val)) = encConfig x) :
    decConfig S N (samplerRetryOutput S C (p,List.ofFn w)) =
      CritWinSpin.Implementation.FiniteRetry.firstSome (fun i : Fin Q => decConfig S N
        (trialOnBlock S C p F (bitBlock ((List.ofFn w,samplerTrialBits S C (p,[])),i.val)))) := by
  unfold samplerRetryOutput
  rw [samplerTrialOutputs_ofFn S C p F Q hQ hQF w]
  exact CritWinSpin.Implementation.RetryPacketDecoding.decode_selected_ofFn hN _ hValid

theorem bitBlock_ofFn_prefix {Q L F : ℕ} (w : Fin F → Bool) (i : Fin Q) (hF : Q*L ≤ F) :
    bitBlock ((List.ofFn w,L),i.val) = List.ofFn (fun j : Fin L =>
      w ⟨i.val*L+j.val,(blockIndex_lt i j).trans_le hF⟩) := by
  apply List.ext_getElem
  · simp only [bitBlock,List.length_take,List.length_drop,List.length_ofFn]
    have hm : i.val*L+L ≤ F := by
      simpa only [Nat.succ_mul] using (Nat.mul_le_mul_right L (Nat.succ_le_of_lt i.isLt)).trans hF
    omega
  · intro j hj hj'
    simp only [bitBlock,List.getElem_take,List.getElem_drop,List.getElem_ofFn]

theorem samplerRetryOutput_law {N : ℕ} (S : SpinLaw) (C : ℕ) (p : ParsedInput)
    (F Q : ℕ) (hN : 0 < N) (hQ : retryCount S C (samplerPre (p,[]),p.2) = Q)
    (hQF : Q ≤ F) (hBits : Q * samplerTrialBits S C (p,[]) ≤ F)
    (hValid : ∀ w : Fin (samplerTrialBits S C (p,[])) → Bool,
      trialOnBlock S C p F (List.ofFn w) = [] ∨
        ∃ x : Config S (Fin N), trialOnBlock S C p F (List.ofFn w) = encConfig x) :
    FiniteDraw.law (fun w : Fin F → Bool => decConfig S N
      (samplerRetryOutput S C (p,List.ofFn w))) =
      CritWinSpin.Implementation.FiniteRetry.retry
        (FiniteDraw.law (fun w : Fin (samplerTrialBits S C (p,[])) → Bool =>
          decConfig S N (trialOnBlock S C p F (List.ofFn w)))) Q := by
  obtain ⟨R,hFR⟩ := Nat.exists_eq_add_of_le hBits
  subst F
  let L := samplerTrialBits S C (p,[])
  let draw := fun w : Fin L → Bool => decConfig S N (trialOnBlock S C p (Q*L+R) (List.ofFn w))
  have hb (w : Fin (Q*L+R) → Bool) (i : Fin Q) :
      bitBlock ((List.ofFn w,L),i.val) = List.ofFn
        (splitBitEquiv Q L (fun j => w (Fin.castAdd R j)) i) := by
    rw [bitBlock_ofFn_prefix w i (Nat.le_add_right _ _)]
    congr 1
    funext j
    rw [splitBitEquiv_apply]
    rfl
  have hp (w : Fin (Q*L+R) → Bool) :
      decConfig S N (samplerRetryOutput S C (p,List.ofFn w)) =
        CritWinSpin.Implementation.FiniteRetry.firstSome
          (fun i => draw (splitBitEquiv Q L (fun j => w (Fin.castAdd R j)) i)) := by
    have hv (i : Fin Q) : trialOnBlock S C p (Q*L+R)
        (bitBlock ((List.ofFn w,L),i.val)) = [] ∨ ∃ x : Config S (Fin N),
        trialOnBlock S C p (Q*L+R) (bitBlock ((List.ofFn w,L),i.val)) = encConfig x := by
      rw [hb]
      exact hValid _
    rw [samplerRetryOutput_decoded S C p (Q*L+R) Q hN hQ hQF w hv]
    apply congrArg (CritWinSpin.Implementation.FiniteRetry.firstSome (q := Q))
    funext i
    change decConfig S N (trialOnBlock S C p (Q*L+R) (bitBlock ((List.ofFn w,L),i.val))) =
      decConfig S N (trialOnBlock S C p (Q*L+R)
        (List.ofFn (splitBitEquiv Q L (fun j => w (Fin.castAdd R j)) i)))
    rw [hb]
  have hfun : (fun w : Fin (Q*L+R) → Bool => decConfig S N
      (samplerRetryOutput S C (p,List.ofFn w))) =
      fun w => CritWinSpin.Implementation.FiniteRetry.firstSome
        (fun i => draw (splitBitEquiv Q L (fun j => w (Fin.castAdd R j)) i)) := funext hp
  change FiniteDraw.law (fun w : Fin (Q*L+R) → Bool => decConfig S N
    (samplerRetryOutput S C (p,List.ofFn w))) = _
  have hprefix := FiniteDraw.law_prefix (Q*L) R
    (fun w : Fin (Q*L) → Bool => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (splitBitEquiv Q L w i)))
  exact (congrArg FiniteDraw.law hfun).trans (hprefix.trans (FiniteDraw.retry_bits Q L draw))

end Compiled
end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section
attribute [local irreducible] criticalWindowMachine kernelOutput EulerData.trialCode
  trialOnBlock samplerRetryOutput FiniteRetry.retry FiniteDraw.law

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot

theorem trialOnBlock_law_data {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ)
    (hT : samplerStepCount S C (sampleReference I m F) ≤ F) :
    FiniteDraw.law (fun w : Fin (samplerTrialBits S C (encodedSamplerInput I m [])) → Bool =>
      decConfig S N (trialOnBlock S C (encodedSamplerInput I m []).1 F (List.ofFn w))) =
      trialWordLaw S C (sampleEulerData S C I m F) (samplerStepCount S C (sampleReference I m F)) := by
  let D := sampleEulerData S C I m F
  let T := samplerStepCount S C (sampleReference I m F)
  have hL : samplerTrialBits S C (encodedSamplerInput I m []) =
      T*(N*gaussianNoiseBits D.k)+(acceptanceBits D.k+N*spinBits S D.k) :=
    (samplerTrialBits_data S C I m F).trans
      ((congrArg (fun n : ℕ => n+acceptanceBits D.k+N*spinBits S D.k)
        (Nat.mul_assoc T N (gaussianNoiseBits D.k))).trans
        (Nat.add_assoc (T*(N*gaussianNoiseBits D.k)) (acceptanceBits D.k) (N*spinBits S D.k)))
  have hfun : (fun w : Fin (samplerTrialBits S C (encodedSamplerInput I m [])) → Bool =>
      decConfig S N (trialOnBlock S C (encodedSamplerInput I m []).1 F (List.ofFn w))) =
      fun w => decConfig S N (D.trialCode S C T (List.ofFn w)) :=
    funext (fun w => congrArg (decConfig S N) (trialOnBlock_data S C I m F hT (List.ofFn w)))
  exact (congrArg
    (fun draw : (Fin (samplerTrialBits S C (encodedSamplerInput I m [])) → Bool) →
      Option (Config S (Fin N)) => FiniteDraw.law draw) hfun).trans
    (FiniteDraw.law_bits_length hL (fun bits => decConfig S N (D.trialCode S C T bits)))
end

theorem trialOnBlock_valid {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C) (I : Inst N) (m F : ℕ)
    (hT : samplerStepCount S C (sampleReference I m F) ≤ F)
    (hd : 0 < (sampleEulerData S C I m F).dPhi)
    (hf : 2/((sampleEulerData S C I m F).dPhi:ℝ)^3+2 ≤ (sampleEulerData S C I m F).fuel.length)
    (hfSpin : 2/(spinPrecision C (sampleEulerData S C I m F).k:ℝ)^3+2 ≤ (sampleEulerData S C I m F).fuel.length)
    (w : Fin (samplerTrialBits S C (encodedSamplerInput I m [])) → Bool) :
    trialOnBlock S C (encodedSamplerInput I m []).1 F (List.ofFn w) = [] ∨
      ∃ x : Config S (Fin N), trialOnBlock S C (encodedSamplerInput I m []).1 F (List.ofFn w) = encConfig x := by
  let D := sampleEulerData S C I m F
  let T := samplerStepCount S C (sampleReference I m F)
  have hL : samplerTrialBits S C (encodedSamplerInput I m []) =
      T*(N*gaussianNoiseBits D.k)+(acceptanceBits D.k+N*spinBits S D.k) := by
    rw [samplerTrialBits_data S C I m F]
    dsimp only [T,D]
    ring
  have hv : ∀ n : ℕ, n=T*(N*gaussianNoiseBits D.k)+(acceptanceBits D.k+N*spinBits S D.k) →
      ∀ w : Fin n → Bool, D.trialCode S C T (List.ofFn w)=[] ∨
        ∃ x : Config S (Fin N), D.trialCode S C T (List.ofFn w)=encConfig x := by
    intro n hn
    subst n
    exact D.trialCode_valid S C T hC hd hf hfSpin
  rw [trialOnBlock_data S C I m F hT]
  exact hv _ hL w

theorem inside_outLaw {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hN : 0 < N) (hin : preInside S C (encodedInput I.1)=true) :
    let F := criticalCoins S C (encodedInput I.1,m)
    outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N) =
      FiniteDraw.law (fun w : Fin F → Bool =>
        decConfig S N (samplerRetryOutput S C (encodedSamplerInput I m (List.ofFn w)))) := by
  dsimp only
  let F := criticalCoins S C (encodedInput I.1,m)
  have hempty : (List.replicate N ()).isEmpty=false := by cases N <;> simp_all
  have hin' : preInside S C ((instanceListModel I).1,List.replicate N ()) = true := hin
  have hc : (criticalWindowMachine S C).coins (tupleCode [encInst I,encBin m])=F := by
    rw [criticalWindowMachine_coins_encoded,hempty]
    change (if preInside S C (encodedInput I.1) then _ else _)=F
    rw [hin]
    rfl
  funext y
  rw [outLaw_reclock _ _ _ y F hc]
  unfold FiniteDraw.law
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  apply congrArg (fun t : ℝ => (1/(2:ℝ)^F)*t)
  apply Finset.sum_congr rfl
  intro w _
  rw [criticalWindowMachine_run_encoded,hempty]
  simp only [Bool.false_eq_true,if_false,hin',if_true]
  by_cases hy : decConfig S N (samplerRetryOutput S C (encodedSamplerInput I m (List.ofFn w))) = y
  · simp only [if_pos hy]
  · simp only [if_neg hy]

theorem _root_.solution {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) (hqC : (alphabet S).length ≤ C)
    (hN : 0 < N) (hin : preInside S C (encodedInput I.1)=true) :
    let F := criticalCoins S C (encodedInput I.1,m)
    outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N) =
      FiniteRetry.retry (trialWordLaw S C (sampleEulerData S C I m F)
        (samplerStepCount S C (sampleReference I m F))) (trials S C I m) := by
  let F := criticalCoins S C (encodedInput I.1,m)
  have hb := actual_word_budgets S C I m hC hm hqC
  have hT := SamplerCappedPath.stepCount_le_coins S C I m hC hm
  rw [inside_outLaw S C I m hN hin]
  have hlaw := samplerRetryOutput_law S C (encodedSamplerInput I m []).1 F (trials S C I m)
    hN rfl hb.1 hb.2.1 (trialOnBlock_valid S C (by omega) I m F hT hb.2.2.1.1 hb.2.2.1.2 hb.2.2.2.1)
  exact hlaw.trans (congrArg
    (fun r : Option (Config S (Fin N)) → ℝ => FiniteRetry.retry r (trials S C I m))
    (trialOnBlock_law_data S C I m F hT))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.EnumerationProof
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp
open scoped BigOperators
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.EnumerationProof

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC IsingLTL.BeliefProp

end CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RuntimeArithmetic

end CritWinSpin.Implementation.RuntimeArithmetic
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCriticalLevel
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches

end CritWinSpin.Implementation.PreprocessCriticalLevel
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.CriticalCapBudget
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessCriticalLevel PreprocessIntegral PreprocessCap

end CritWinSpin.Implementation.CriticalCapBudget
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerRuntime
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessBranches PreprocessIntegral PreprocessCap RuntimeArithmetic

end CritWinSpin.Implementation.SamplerRuntime
end

end

section

set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.SamplerConstantChoice
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

end CritWinSpin.Implementation.SamplerConstantChoice
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory IsingLTL.BeliefProp CritWinSpin
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

end

end
