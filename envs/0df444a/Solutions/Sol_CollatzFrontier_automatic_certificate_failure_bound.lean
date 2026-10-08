-- Prove2me | solution 1 for CollatzFrontier.automatic_certificate_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-05T17:56:41.8401+00:00
-- url     : https://prove2.me/submissions/74904ec6-5e17-457d-bae0-f26281ffe51c

import Definitions.Def_collatzFrontierCoverage
import Theorems.Thm_CollatzFrontier_bounded_descent_generated
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field

open CollatzFrontier
open scoped BigOperators

namespace CollatzFrontierAux

/-! Helper lemmas, transcribed from the M46-free, purely combinatorial route through
`UniformDescent.lean`, `CertificateDensity.lean`, `UnconditionalCertificateDensity.lean`,
`OddUniformResidueLaw.lean`, `FiniteLawTransfer.lean`, `GeometricLowerTail.lean`,
`CylinderCounting.lean`, `ValuationDescent.lean`, and `ExecutableCertificateCoverage.lean`
(research/certificate-density-20261002 @ 61e6b54 and
research/executable-coverage-20261002 @ 3835de1). None of these lemmas ever instantiate
or use `SyracuseJointGeometricBound` ("M46"); the finite-cylinder counting below is
unconditional. -/

theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  apply Nat.odd_iff.mpr
  have hnot : ¬ 2 ∣ syracuseStep n :=
    Nat.not_dvd_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  have hne : syracuseStep n % 2 ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hlt := Nat.mod_lt (syracuseStep n) (show 0 < 2 by decide)
  omega

theorem syracuse_iterate_odd (n : ℕ) (hn : Odd n) (i : ℕ) :
    Odd (syracuseStep^[i] n) := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_odd _

/-- The exact valuation vector of the odd input indexed by `i`. -/
def indexValuations (t i : ℕ) : Fin t → ℕ :=
  fun j => (3 * syracuseStep^[j.val] (2 * i + 1) + 1).factorization 2

theorem indexValuations_sum (t i : ℕ) :
    (∑ j, indexValuations t i j) =
      ∑ j ∈ Finset.range t, (3 * syracuseStep^[j] (2 * i + 1) + 1).factorization 2 := by
  exact (Finset.sum_range (fun j => (3 * syracuseStep^[j] (2 * i + 1) + 1).factorization 2)).symm

/-- Actual positive-odd Syracuse inputs have positive valuation coordinates. -/
theorem indexValuations_pos (t i : ℕ) (j : Fin t) : 0 < indexValuations t i j := by
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega)
  obtain ⟨u, hu⟩ := syracuse_iterate_odd (2 * i + 1) ⟨i, by omega⟩ j.val
  exact ⟨3 * u + 2, by omega⟩

/-- Backwards propagation of a terminal congruence through two common dyadic chains. -/
theorem dyadic_chain_modEq_backwards (a b c : ℕ → ℕ) (t e : ℕ)
    (hb : ∀ i < t, 2 ^ (a i) * b (i + 1) = 3 * b i + 1)
    (hc : ∀ i < t, 2 ^ (a i) * c (i + 1) = 3 * c i + 1)
    (hfinal : b t ≡ c t [MOD 2 ^ e]) :
    b 0 ≡ c 0 [MOD 2 ^ ((∑ i ∈ Finset.range t, a i) + e)] := by
  induction t generalizing a b c with
  | zero => simpa using hfinal
  | succ t ih =>
      have htail := ih (fun i => a (i + 1)) (fun i => b (i + 1)) (fun i => c (i + 1))
        (fun i hi => hb (i + 1) (by omega)) (fun i hi => hc (i + 1) (by omega)) hfinal
      have hmul := htail.mul_left' (2 ^ (a 0))
      rw [hb 0 (by omega), hc 0 (by omega)] at hmul
      have hmod : 3 * b 0 + 1 ≡ 3 * c 0 + 1
          [MOD 2 ^ ((∑ i ∈ Finset.range (t + 1), a i) + e)] := by
        simpa [Finset.sum_range_succ', pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have hcoprime : Nat.Coprime (2 ^ ((∑ i ∈ Finset.range (t + 1), a i) + e)) 3 := by
        exact (show Nat.Coprime 2 3 by decide).pow_left _
      exact Nat.ModEq.cancel_left_of_coprime hcoprime (hmod.add_right_cancel' 1)

/-- A complete exact valuation vector forces one index residue class, including
its final parity bit. -/
theorem indexValuations_residue (t i j : ℕ) (h : indexValuations t i = indexValuations t j) :
    i ≡ j [MOD 2 ^ (∑ k, indexValuations t i k)] := by
  let b := fun k : ℕ => syracuseStep^[k] (2 * i + 1)
  let c := fun k : ℕ => syracuseStep^[k] (2 * j + 1)
  let a := fun k : ℕ => (3 * b k + 1).factorization 2
  have hb (k : ℕ) : 2 ^ (a k) * b (k + 1) = 3 * b k + 1 := by
    change 2 ^ ((3 * syracuseStep^[k] (2 * i + 1) + 1).factorization 2) *
      syracuseStep^[k + 1] (2 * i + 1) = 3 * syracuseStep^[k] (2 * i + 1) + 1
    rw [Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self _ 2
  have hc (k : ℕ) (hk : k < t) : 2 ^ (a k) * c (k + 1) = 3 * c k + 1 := by
    have he := congrFun h ⟨k, hk⟩
    change a k = (3 * c k + 1).factorization 2 at he
    rw [he]
    change 2 ^ ((3 * syracuseStep^[k] (2 * j + 1) + 1).factorization 2) *
      syracuseStep^[k + 1] (2 * j + 1) = 3 * syracuseStep^[k] (2 * j + 1) + 1
    rw [Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self _ 2
  have hfinal : b t ≡ c t [MOD 2 ^ 1] := by
    have hbi := Nat.odd_iff.mp (syracuse_iterate_odd (2 * i + 1) ⟨i, by omega⟩ t)
    have hcj := Nat.odd_iff.mp (syracuse_iterate_odd (2 * j + 1) ⟨j, by omega⟩ t)
    change b t % 2 = c t % 2
    exact hbi.trans hcj.symm
  have hstart := dyadic_chain_modEq_backwards a b c t 1 (fun k _ => hb k) hc hfinal
  have htwice : 2 * i ≡ 2 * j [MOD 2 * 2 ^ (∑ k ∈ Finset.range t, a k)] := by
    simpa [b, c, pow_succ, Nat.mul_comm] using hstart.add_right_cancel' 1
  rw [indexValuations_sum]
  exact Nat.ModEq.mul_left_cancel' (by decide : 2 ≠ 0) htwice

/-- Exact frequencies of residues of an initial interval; reuses Mathlib's count theorem. -/
theorem initial_residue_count (R H r : ℕ) (hH : 0 < H) (hr : r < H) :
    ((Finset.range R).filter (fun i => i % H = r)).card =
      R / H + if r < R % H then 1 else 0 := by
  simpa [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt hr] using
    Nat.count_modEq_card R hH r

/-- Atom of the image of a uniformly chosen index in `[0, R)`. -/
noncomputable def indexAtom {α : Type*} [DecidableEq α] (R : ℕ) (f : ℕ → α) (a : α) : ℝ :=
  (((Finset.range R).filter (fun i => f i = a)).card : ℝ) / R

/-- Fiberwise counting identifies a finite image event with its atom sum. -/
theorem index_event_mass {α : Type*} [DecidableEq α]
    (R : ℕ) (f : ℕ → α) (s : Finset α) :
    (((Finset.range R).filter (fun i => f i ∈ s)).card : ℝ) / R =
      ∑ a ∈ s, indexAtom R f a := by
  unfold indexAtom
  rw [← Finset.sum_div, ← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]

/-- Each finite-prefix atom has its geometric cylinder mass plus at most one
incomplete-block contribution. -/
theorem indexValuations_atom_le (R t : ℕ) (hR : 0 < R) (a : Fin t → ℕ) :
    indexAtom R (indexValuations t) a ≤ 1 / (2 : ℝ) ^ (∑ k, a k) + 1 / R := by
  classical
  let fiber := (Finset.range R).filter (fun i => indexValuations t i = a)
  let H := 2 ^ (∑ k, a k)
  have hH : 0 < H := by dsimp [H]; positivity
  by_cases hne : fiber.Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hja := (Finset.mem_filter.mp hj).2
    have hsub : fiber ⊆ (Finset.range R).filter (fun i => i % H = j % H) := by
      intro i hi
      obtain ⟨hiR, hia⟩ := Finset.mem_filter.mp hi
      have hm := indexValuations_residue t i j (hia.trans hja.symm)
      rw [hia] at hm
      exact Finset.mem_filter.mpr ⟨hiR, hm⟩
    have hcount : fiber.card ≤ R / H + 1 := by
      have hb := Finset.card_le_card hsub
      rw [initial_residue_count R H (j % H) hH (Nat.mod_lt j hH)] at hb
      split_ifs at hb <;> omega
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have hH' : (0 : ℝ) < H := by exact_mod_cast hH
    have hcount' : (fiber.card : ℝ) ≤ (R / H : ℕ) + 1 := by exact_mod_cast hcount
    have hquot : ((R / H : ℕ) : ℝ) * H ≤ R := by
      have hnat : (R / H) * H ≤ R := Nat.div_mul_le_self R H
      exact_mod_cast hnat
    change (fiber.card : ℝ) / R ≤ _
    calc
      _ ≤ (((R / H : ℕ) : ℝ) + 1) / R := div_le_div_of_nonneg_right hcount' hR'.le
      _ = ((R / H : ℕ) : ℝ) / R + 1 / R := add_div _ _ _
      _ ≤ 1 / (H : ℝ) + 1 / R := add_le_add ((div_le_div_iff₀ hR' hH').mpr (by simpa using hquot)) le_rfl
      _ = _ := by dsimp [H]; norm_cast
  · have hf : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (fiber.card : ℝ) / R ≤ _
    rw [hf]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Appending positive slack embeds every such vector into Composition(L+1). -/
theorem positive_vector_card_le (t L : ℕ) (s : Finset (Fin t → ℕ))
    (hpos : ∀ a ∈ s, ∀ i, 0 < a i) (hsum : ∀ a ∈ s, (∑ i, a i) ≤ L) :
    s.card ≤ 2 ^ L := by
  classical
  let f : s → Composition (L + 1) := fun a =>
    { blocks := List.ofFn a.val ++ [L + 1 - ∑ i, a.val i]
      blocks_pos := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          exact hpos a.val a.property i
        · have hx' : x = L + 1 - ∑ i, a.val i := by simpa using hx
          have hh := hsum a.val a.property
          omega
      blocks_sum := by
        have hh := hsum a.val a.property
        simp only [List.sum_append, List.sum_ofFn, List.sum_cons, List.sum_nil, add_zero]
        omega }
  have hinj : Function.Injective f := by
    intro a b hab
    have he := congrArg (fun c : Composition (L + 1) => c.blocks.take t) hab
    have he' : List.ofFn a.val = List.ofFn b.val := by
      simpa [f, List.take_append, List.length_ofFn] using he
    exact Subtype.ext (List.ofFn_injective he')
  have hc := Fintype.card_le_of_injective f hinj
  simpa [composition_card] using hc

/-- Positive-coordinate geometric power weight; a zero coordinate has zero weight. -/
noncomputable def positivePowerWeight (r : ℝ) (t : ℕ) (a : Fin t → ℕ) : ℝ :=
  ∏ i, if a i = 0 then 0 else r ^ (a i)

theorem positivePowerWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (t : ℕ) (a : Fin t → ℕ) :
    0 ≤ positivePowerWeight r t a := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> positivity

/-- Truncated positive geometric series, bounded using the standard scalar series. -/
theorem positive_geometric_partial_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (B : ℕ) :
    (∑ b ∈ Finset.range B, if b = 0 then 0 else r ^ b) ≤ r / (1 - r) := by
  cases B with
  | zero => simp; positivity
  | succ B =>
      rw [Finset.sum_range_succ']
      simp only [ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      have hs := (hasSum_geometric_of_lt_one hr hr1).mul_left r
      have hb := hs.summable.sum_le_tsum (Finset.range B) (fun _ _ => by positivity)
      rw [hs.tsum_eq] at hb
      simpa [pow_succ, div_eq_mul_inv, mul_comm] using hb

/-- Uniform finite-family bound from product expansion over one finite coordinate box. -/
theorem positivePowerWeight_finite_sum_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (t : ℕ) (s : Finset (Fin t → ℕ)) :
    (∑ a ∈ s, positivePowerWeight r t a) ≤ (r / (1 - r)) ^ t := by
  classical
  let B := s.sup (fun a => ∑ i, a i) + 1
  let box := Fintype.piFinset (fun _ : Fin t => Finset.range B)
  have hsub : s ⊆ box := by
    intro a ha
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_range.mpr
    have hai : a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hs := Finset.le_sup (f := fun a : Fin t → ℕ => ∑ i, a i) ha
    dsimp [B]
    omega
  calc
    _ ≤ ∑ a ∈ box, positivePowerWeight r t a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => positivePowerWeight_nonneg hr t a)
    _ = (∑ b ∈ Finset.range B, if b = 0 then 0 else r ^ b) ^ t := by
      dsimp [box, positivePowerWeight]
      simpa using Finset.sum_prod_piFinset (ι := Fin t) (Finset.range B)
        (fun (_ : Fin t) b => if b = 0 then (0 : ℝ) else r ^ b)
    _ ≤ _ := by
      apply pow_le_pow_left₀
      · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
      · exact positive_geometric_partial_le r hr hr1 B

/-- The source model atom, rewritten as a finite product. -/
theorem positivePowerWeight_half (t : ℕ) (a : Fin t → ℕ) :
    positivePowerWeight (1 / 2) t a =
      if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0 := by
  classical
  by_cases ha : ∀ i : Fin t, 0 < a i
  · rw [if_pos ha]
    unfold positivePowerWeight
    have h (i : Fin t) : ¬ a i = 0 := by have := ha i; omega
    simp only [h, ite_false]
    rw [Finset.prod_pow_eq_pow_sum, one_div_pow]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    have hi0 : a i = 0 := by omega
    unfold positivePowerWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi0]

/-- Exponential tilting identity for the chosen lower-tail parameter `z = 3/4`. -/
theorem positivePowerWeight_tilt (t : ℕ) (a : Fin t → ℕ) :
    positivePowerWeight (1 / 2) t a * (3 / 4 : ℝ) ^ (∑ i, a i) =
      positivePowerWeight (3 / 8) t a := by
  unfold positivePowerWeight
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : a i = 0
  · simp [hi]
  · simp only [hi, ite_false]
    rw [← mul_pow]
    norm_num

/-- A finite lower-tail event under the positive-geometric model. -/
theorem geometric_lower_tail_finite (t L : ℕ) (s : Finset (Fin t → ℕ))
    (hsmall : ∀ a ∈ s, (∑ i, a i) ≤ L) :
    (∑ a ∈ s, positivePowerWeight (1 / 2) t a) ≤
      (4 / 3 : ℝ) ^ L * (3 / 5 : ℝ) ^ t := by
  have htilt : (∑ a ∈ s, positivePowerWeight (1 / 2) t a) * (3 / 4 : ℝ) ^ L ≤
      ∑ a ∈ s, positivePowerWeight (3 / 8) t a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    rw [← positivePowerWeight_tilt]
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hsmall a ha)
    · exact positivePowerWeight_nonneg (by norm_num) t a
  have hsum : (∑ a ∈ s, positivePowerWeight (3 / 8) t a) ≤ (3 / 5 : ℝ) ^ t := by
    convert positivePowerWeight_finite_sum_le (3 / 8) (by norm_num) (by norm_num) t s using 1; norm_num
  have hz : (0 : ℝ) < (3 / 4 : ℝ) ^ L := by positivity
  apply (le_of_mul_le_mul_right ?_ hz)
  calc
    _ ≤ (3 / 5 : ℝ) ^ t := htilt.trans hsum
    _ = ((4 / 3 : ℝ) ^ L * (3 / 5 : ℝ) ^ t) * (3 / 4 : ℝ) ^ L := by
      have hi : (4 / 3 : ℝ) ^ L * (3 / 4 : ℝ) ^ L = 1 := by rw [← mul_pow]; norm_num
      symm
      calc
        _ = ((4 / 3 : ℝ) ^ L * (3 / 4 : ℝ) ^ L) * (3 / 5 : ℝ) ^ t := by ring
        _ = _ := by rw [hi, one_mul]

/-- An exact rational exponential rate for the `(4m, 7m)` lower-tail threshold. -/
theorem geometric_lower_tail_four_seven (m : ℕ) (s : Finset (Fin (4 * m) → ℕ))
    (hsmall : ∀ a ∈ s, (∑ i, a i) ≤ 7 * m) :
    (∑ a ∈ s, positivePowerWeight (1 / 2) (4 * m) a) ≤
      (16384 / 16875 : ℝ) ^ m := by
  have h := geometric_lower_tail_finite (4 * m) (7 * m) s hsmall
  rw [pow_mul, pow_mul, ← mul_pow] at h
  norm_num at h
  exact h

/-- Direct finite cylinder counting gives the needed lower tail, with an explicit
incomplete-block error, without any joint-law theorem or probabilistic premise. -/
theorem small_valuation_count_direct (R m : ℕ) (hR : 0 < R) :
    (((Finset.range R).filter (fun i => (∑ j, indexValuations (4 * m) i j) ≤ 7 * m)).card : ℝ) / R ≤
      (16384 / 16875 : ℝ) ^ m + (2 : ℝ) ^ (7 * m) / R := by
  let f := indexValuations (4 * m)
  let bad := (Finset.range R).filter (fun i => (∑ j, f i j) ≤ 7 * m)
  let s := bad.image f
  have hsmall : ∀ a ∈ s, (∑ j, a j) ≤ 7 * m := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  have hpos : ∀ a ∈ s, ∀ j, 0 < a j := by
    intro a ha j
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact indexValuations_pos (4 * m) i j
  have heq : (Finset.range R).filter (fun i => f i ∈ s) = bad := by
    apply Finset.filter_congr
    intro i hi
    constructor
    · exact fun hs => hsmall (f i) hs
    · intro hsmalli
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hsmalli⟩, rfl⟩
  have hmass := index_event_mass R f s
  rw [heq] at hmass
  have hcard : (s.card : ℝ) ≤ (2 : ℝ) ^ (7 * m) := by
    exact_mod_cast positive_vector_card_le (4 * m) (7 * m) s hpos hsmall
  change (bad.card : ℝ) / R ≤ _
  rw [hmass]
  calc
    _ ≤ ∑ a ∈ s, (positivePowerWeight (1 / 2) (4 * m) a + 1 / R) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [positivePowerWeight_half, if_pos (hpos a ha)]
      exact indexValuations_atom_le R (4 * m) hR a
    _ = (∑ a ∈ s, positivePowerWeight (1 / 2) (4 * m) a) + (s.card : ℝ) / R := by
      rw [Finset.sum_add_distrib]
      simp [div_eq_mul_inv]
    _ ≤ (16384 / 16875 : ℝ) ^ m + (2 : ℝ) ^ (7 * m) / R :=
      add_le_add (geometric_lower_tail_four_seven m s hsmall)
        (div_le_div_of_nonneg_right hcard (by positivity))

/-- Positive dyadic divisors give an explicit uniform bound on the affine offset. -/
theorem dyadic_chain_offset_bound (a b : ℕ → ℕ) (t : ℕ)
    (hpos : ∀ i < t, 0 < a i)
    (hstep : ∀ i < t, 3 * b i + 1 = 2 ^ (a i) * b (i + 1)) :
    (2 : ℚ) ^ (∑ i ∈ Finset.range t, a i) * ((b t : ℚ) + 1) ≤
      3 ^ t * (b 0 : ℚ) + 2 ^ (∑ i ∈ Finset.range t, a i) * (3 / 2 : ℚ) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hp := ih (fun i hi => hpos i (by omega)) (fun i hi => hstep i (by omega))
      let S := ∑ i ∈ Finset.range t, a i
      have hrow : (2 : ℚ) ^ (a t) * (b (t + 1) : ℚ) = 3 * (b t : ℚ) + 1 := by
        exact_mod_cast (hstep t (by omega)).symm
      have he : (2 : ℚ) ≤ 2 ^ (a t) := by
        exact_mod_cast (Nat.pow_le_pow_right (n := 2) (i := 1) (j := a t)
          (by decide) (hpos t (by omega)))
      have hr : (1 : ℚ) ≤ (3 / 2 : ℚ) ^ t := one_le_pow₀ (by norm_num)
      have hS : (0 : ℚ) < 2 ^ S := by positivity
      have hgap : 0 ≤ 2 ^ S * ((2 : ℚ) ^ (a t) - 2) *
          (3 * (3 / 2 : ℚ) ^ t - 2) := by
        exact mul_nonneg (mul_nonneg hS.le (by linarith)) (by linarith)
      have hscale := congrArg (fun z : ℚ => 2 ^ S * z) hrow
      change 2 ^ S * ((b t : ℚ) + 1) ≤ 3 ^ t * (b 0 : ℚ) + 2 ^ S * (3 / 2 : ℚ) ^ t at hp
      rw [Finset.sum_range_succ, pow_add, pow_succ, pow_succ]
      change 2 ^ S * (2 : ℚ) ^ (a t) * ((b (t + 1) : ℚ) + 1) ≤
        (3 ^ t * 3) * (b 0 : ℚ) + (2 ^ S * 2 ^ (a t)) * ((3 / 2 : ℚ) ^ t * (3 / 2))
      nlinarith

/-- A factor-of-two main-term contraction and an explicit input threshold force descent. -/
theorem dyadic_chain_descends_of_half_contraction (a b : ℕ → ℕ) (t : ℕ)
    (hpos : ∀ i < t, 0 < a i)
    (hstep : ∀ i < t, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hcontract : 2 * 3 ^ t ≤ 2 ^ (∑ i ∈ Finset.range t, a i))
    (hlarge : 2 * 3 ^ t ≤ b 0) : b t < b 0 := by
  let S := ∑ i ∈ Finset.range t, a i
  have hb := dyadic_chain_offset_bound a b t hpos hstep
  have hS : (0 : ℚ) < 2 ^ S := by positivity
  have hn : (0 : ℚ) ≤ b 0 := by positivity
  have hc : (2 : ℚ) * 3 ^ t ≤ 2 ^ S := by exact_mod_cast hcontract
  have hl : (2 : ℚ) * 3 ^ t ≤ b 0 := by exact_mod_cast hlarge
  have hr : (3 / 2 : ℚ) ^ t ≤ 3 ^ t := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hm := mul_nonneg hn (show (0 : ℚ) ≤ 2 ^ S - 2 * 3 ^ t by linarith)
  have hm' := mul_nonneg hS.le (show (0 : ℚ) ≤ (b 0 : ℚ) - 2 * (3 / 2 : ℚ) ^ t by linarith)
  have hout : (b t : ℚ) + 1 ≤ b 0 := by
    change 2 ^ S * ((b t : ℚ) + 1) ≤ 3 ^ t * (b 0 : ℚ) + 2 ^ S * (3 / 2 : ℚ) ^ t at hb
    nlinarith
  have : b t + 1 ≤ b 0 := by exact_mod_cast hout
  omega

/-- The rational gap `7/4 > log_2(3)`, quantified without logarithms. -/
theorem seven_four_halving_margin (m : ℕ) (hm : 2 ≤ m) : 2 * 3 ^ (4 * m) ≤ 2 ^ (7 * m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : (81 : ℕ) ^ k ≤ 128 ^ k := Nat.pow_le_pow_left (by decide) k
  have hp := Nat.mul_le_mul_left (2 * 81 ^ 2) hk
  have hb := Nat.mul_le_mul_right (128 ^ k) (show (2 : ℕ) * 81 ^ 2 ≤ 128 ^ 2 by decide)
  rw [pow_mul, pow_mul]
  norm_num only [show (3 : ℕ) ^ 4 = 81 by decide, show (2 : ℕ) ^ 7 = 128 by decide]
  rw [pow_add, pow_add]
  nlinarith

/-- A source-shaped deterministic input to a quantitative stopping-time estimate. -/
theorem syracuse_descent_of_valuation_sum (n m : ℕ) (hodd : Odd n) (hm : 2 ≤ m)
    (hlarge : 2 * 3 ^ (4 * m) ≤ n)
    (hsum : 7 * m ≤ ∑ i ∈ Finset.range (4 * m),
      (3 * syracuseStep^[i] n + 1).factorization 2) :
    syracuseStep^[4 * m] n < n := by
  let b := fun i : ℕ => syracuseStep^[i] n
  let a := fun i : ℕ => (3 * b i + 1).factorization 2
  have ha (i : ℕ) : 0 < a i := by
    apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega)
    obtain ⟨u, hu⟩ := syracuse_iterate_odd n hodd i
    exact ⟨3 * u + 2, by dsimp [b]; omega⟩
  have hstep (i : ℕ) : 3 * b i + 1 = 2 ^ (a i) * b (i + 1) := by
    change 3 * syracuseStep^[i] n + 1 =
      2 ^ ((3 * syracuseStep^[i] n + 1).factorization 2) * syracuseStep^[i + 1] n
    rw [Function.iterate_succ_apply']
    exact (Nat.ordProj_mul_ordCompl_eq_self (3 * syracuseStep^[i] n + 1) 2).symm
  exact dyadic_chain_descends_of_half_contraction a b (4 * m)
    (fun i _ => ha i) (fun i _ => hstep i)
    (le_trans (seven_four_halving_margin m hm) (Nat.pow_le_pow_right (by decide) hsum)) hlarge

/-- The same direct counting bound now applies to actual bounded checker rejection. -/
theorem bounded_certificate_failure_count_direct (R L m : ℕ) (hR : 0 < R) (hm : 2 ≤ m)
    (hsize : 2 * R ≤ 2 ^ L) :
    (boundedCertificateFailureCount R L m : ℝ) / R ≤
      (3 : ℝ) ^ (4 * m) / R + (16384 / 16875 : ℝ) ^ m + (2 : ℝ) ^ (7 * m) / R := by
  let bad := (Finset.range R).filter (fun i => boundedCertificateTest L m (2 * i + 1) = false)
  let smallInput := (Finset.range R).filter (fun i => 2 * i + 1 < 2 * 3 ^ (4 * m))
  let smallSum := (Finset.range R).filter (fun i => (∑ j, indexValuations (4 * m) i j) ≤ 7 * m)
  have hsub : bad ⊆ smallInput ∪ smallSum := by
    intro i hi
    obtain ⟨hiR, hibad⟩ := Finset.mem_filter.mp hi
    by_cases hlarge : 2 * 3 ^ (4 * m) ≤ 2 * i + 1
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hiR, ?_⟩
      by_contra hnot
      have hs : 7 * m ≤ ∑ j ∈ Finset.range (4 * m),
          (3 * syracuseStep^[j] (2 * i + 1) + 1).factorization 2 := by
        rw [← indexValuations_sum]
        omega
      have hiR' := Finset.mem_range.mp hiR
      have hnsize : 2 * i + 1 < 2 ^ L := lt_of_lt_of_le (by omega) hsize
      have hdesc := syracuse_descent_of_valuation_sum (2 * i + 1) m ⟨i, by omega⟩ hm hlarge hs
      have haccept : boundedCertificateTest L m (2 * i + 1) = true := by
        rw [boundedCertificateTest, if_neg (by omega : m ≠ 0)]
        exact CollatzFrontier.bounded_descent_generated (2 * i + 1) L (4 * m)
          (by omega) ⟨i, by omega⟩ hnsize hdesc
      simp [haccept] at hibad
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiR, by omega⟩)
  have hsmallInput : smallInput.card ≤ 3 ^ (4 * m) := by
    have hsub' : smallInput ⊆ Finset.range (3 ^ (4 * m)) := by
      intro i hi
      have hx := (Finset.mem_filter.mp hi).2
      exact Finset.mem_range.mpr (by omega)
    simpa using Finset.card_le_card hsub'
  have hcard : bad.card ≤ smallInput.card + smallSum.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (bad.card : ℝ) ≤ smallInput.card + smallSum.card := by exact_mod_cast hcard
  have hsmallInput' : (smallInput.card : ℝ) ≤ (3 : ℝ) ^ (4 * m) := by exact_mod_cast hsmallInput
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have hsmallSum := small_valuation_count_direct R m hR
  change (bad.card : ℝ) / R ≤ _
  calc
    _ ≤ ((smallInput.card : ℝ) + smallSum.card) / R := div_le_div_of_nonneg_right hcard' hR'
    _ = (smallInput.card : ℝ) / R + (smallSum.card : ℝ) / R := add_div _ _ _
    _ ≤ (3 : ℝ) ^ (4 * m) / R + ((16384 / 16875 : ℝ) ^ m + (2 : ℝ) ^ (7 * m) / R) :=
      add_le_add (div_le_div_of_nonneg_right hsmallInput' hR') hsmallSum
    _ = _ := by ring

/-- Explicit density estimate for one fully specified, finite checker call per input. -/
theorem bounded_certificate_failure_count_explicit (R L m : ℕ) (hm : 2 ≤ m)
    (hlarge : 2 ^ (24 * m) ≤ R) (hsize : 2 * R ≤ 2 ^ L) :
    (boundedCertificateFailureCount R L m : ℝ) / R ≤
      (81 / 16777216 : ℝ) ^ m + (16384 / 16875 : ℝ) ^ m + (1 / 131072 : ℝ) ^ m := by
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hlarge
  have h := bounded_certificate_failure_count_direct R L m hR hm hsize
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hp : (0 : ℝ) < 2 ^ (24 * m) := by positivity
  have hlarge' : (2 : ℝ) ^ (24 * m) ≤ R := by exact_mod_cast hlarge
  have hsmall : (3 : ℝ) ^ (4 * m) / R ≤ (81 / 16777216 : ℝ) ^ m := by
    calc
      _ ≤ (3 : ℝ) ^ (4 * m) / 2 ^ (24 * m) :=
        (div_le_div_iff₀ hR' hp).mpr (mul_le_mul_of_nonneg_left hlarge' (by positivity))
      _ = _ := by rw [pow_mul, pow_mul, ← div_pow]; norm_num
  have hround : (2 : ℝ) ^ (7 * m) / R ≤ (1 / 131072 : ℝ) ^ m := by
    calc
      _ ≤ (2 : ℝ) ^ (7 * m) / 2 ^ (24 * m) :=
        (div_le_div_iff₀ hR' hp).mpr (mul_le_mul_of_nonneg_left hlarge' (by positivity))
      _ = _ := by rw [pow_mul, pow_mul, ← div_pow]; norm_num
  linarith

end CollatzFrontierAux

open CollatzFrontierAux

/-- Explicit, unconditional failure-rate bound for the executable automatic descent-certificate
checker. Transcribed verbatim from `CollatzFrontier.automatic_certificate_failure_bound`
(research/executable-coverage-20261002 @ 3835de1), reducing to the imported
`bounded_descent_generated` platform theorem for its one checker-acceptance step. -/
theorem solution (R m : ℕ) (hm : 2 ≤ m)
    (hlarge : 2 ^ (24 * m) ≤ R) :
    (automaticCertificateFailureCount R m : ℝ) / R ≤
      (81 / 16777216 : ℝ) ^ m + (16384 / 16875 : ℝ) ^ m + (1 / 131072 : ℝ) ^ m := by
  exact bounded_certificate_failure_count_explicit R (Nat.clog 2 (2 * R)) m hm hlarge
    (Nat.le_pow_clog (by decide) (2 * R))
