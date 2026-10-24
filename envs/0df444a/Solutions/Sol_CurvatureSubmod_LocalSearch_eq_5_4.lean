-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.eq_5_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T06:20:50.180759+00:00
-- url     : https://prove2.me/submissions/8b0b5c44-ec85-4a3d-96c9-dd884e70f58b

/-
Complete Filmus-Ward exchange-potential inequality, 23 October 2026.
Original mathematics: Yuval Filmus and Justin Ward, Monotone Submodular
Maximization over a Matroid via Non-Oblivious Local Search, arXiv:1204.4526v4
(upload19November2013; manuscript20November2013), Theorem1 and Lemmas1,6-8,
pp.8,11-13, specialized to curvature one. Journal DOI10.1137/130920277.
PDF SHA256 e7b1b8d63c7522835ac75fa71c8f0e2c0462cb7d6dfcaef801b6a0d1b8bc49bb.
The platform target is Equation(5.4), p.7, of Maxim Sviridenko, Jan Vondrak and
Justin Ward, Optimal approximation for submodular and supermodular optimization
with bounded curvature, SODA2015 version9October2014.
mikedeng1 supplied the platform statement and definitions. This proof retains
our earlier checked coefficient and normalization body, with its former solution
renamed previous_potential_support. The new part proves the exact potential
marginal formula, expectation monotonicity, exchange and coverage bounds, and
the finite deletion identity. Normalization restores g(empty)>=0; no hidden
zero-empty-set assumption remains. The supplied bijection is used as a
hypothesis, so our separate accepted Brualdi proof is not imported here.
Lean/Mathlib contributors supply finite sums, calculus and matroid foundations.
Alexander Richard Towell directed the campaign and verification requirements;
OpenAI Codex constructed, integrated and checked this proof. No mathematical
novelty or independent human proof review is claimed.
-/
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting
import Mathlib

/-
Integral coefficients for the non-oblivious potential, specializing Filmus and
Ward, SIAM J. Comput. 43 (2014), DOI 10.1137/130920277, to curvature one.
Formalization by Alexander Richard Towell (queelius), with substantial OpenAI
Codex assistance. These coefficient and normalization lemmas are reused below in the full Equation5.4 proof.
-/
open MeasureTheory
noncomputable section
namespace PotentialCoefficients

def kernel (k j : ℕ) (p : ℝ) : ℝ :=
  Real.exp p / (Real.exp 1 - 1) * p ^ k * (1 - p) ^ j

def weight (k j : ℕ) : ℝ := ∫ p in (0 : ℝ)..1, kernel k j p

theorem denom_pos : 0 < Real.exp 1 - 1 := by
  have h : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  linarith

theorem kernel_continuous (k j : ℕ) : Continuous (kernel k j) := by
  unfold kernel
  fun_prop

theorem kernel_integrable (k j : ℕ) :
    IntervalIntegrable (kernel k j) volume (0 : ℝ) 1 :=
  (kernel_continuous k j).intervalIntegrable _ _

theorem weight_nonneg (k j : ℕ) : 0 ≤ weight k j := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro p hp
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos p).le denom_pos.le)
    (pow_nonneg hp.1 k)) (pow_nonneg (sub_nonneg.mpr hp.2) j)

theorem weight_zero_zero : weight 0 0 = 1 := by
  simp only [weight, kernel, pow_zero, mul_one]
  rw [intervalIntegral.integral_div]
  simp only [integral_exp, Real.exp_zero]
  exact div_self (ne_of_gt denom_pos)

theorem weight_pascal (k j : ℕ) : weight k j = weight (k + 1) j + weight k (j + 1) := by
  rw [weight, weight, weight, ← intervalIntegral.integral_add (kernel_integrable _ _)
    (kernel_integrable _ _)]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [kernel, pow_succ]
  ring

theorem kernel_derivative (k j : ℕ) (p : ℝ) :
    HasDerivAt (kernel k j)
      (kernel k j p + (k : ℝ) * kernel (k - 1) j p - (j : ℝ) * kernel k (j - 1) p) p := by
  have h := (((Real.hasDerivAt_exp p).div_const (Real.exp 1 - 1)).mul
    ((hasDerivAt_id p).pow k)).mul
    (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).pow j)
  exact h.congr_deriv (by dsimp [kernel]; ring)

theorem weight_recurrence (k j : ℕ) :
    weight k j + (k : ℝ) * weight (k - 1) j - (j : ℝ) * weight k (j - 1) =
    (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
    (if k = 0 then 1 / (Real.exp 1 - 1) else 0) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun p _ => kernel_derivative k j p)
    (((kernel_integrable k j).add ((kernel_integrable (k-1) j).const_mul (k : ℝ))).sub
      ((kernel_integrable k (j-1)).const_mul (j : ℝ)))
  rw [intervalIntegral.integral_sub ((kernel_integrable k j).add
    ((kernel_integrable (k-1) j).const_mul (k : ℝ)))
    ((kernel_integrable k (j-1)).const_mul (j : ℝ)),
    intervalIntegral.integral_add (kernel_integrable k j)
      ((kernel_integrable (k-1) j).const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  change weight k j + (k : ℝ) * weight (k-1) j - (j : ℝ) * weight k (j-1) = _ at h
  rw [h]
  by_cases hk : k = 0 <;> by_cases hj : j = 0 <;> simp [kernel, hk, hj]

end PotentialCoefficients

namespace PotentialNormalization
open CurvatureSubmod.LocalSearch PotentialCoefficients
variable {X : Type} [Fintype X] [DecidableEq X]

theorem hPot_one_card (A : Finset X) :
    hPot (fun _ : Finset X => (1 : ℝ)) A =
      ∑ k ∈ Finset.range (A.card + 1), (A.card.choose k : ℝ) *
        (if k = 0 then 0 else weight (k - 1) (A.card - k)) := by
  unfold hPot
  rw [Finset.sum_filter]
  trans ∑ B ∈ A.powerset, if B.card = 0 then 0 else weight (B.card - 1) (A.card - B.card)
  · apply Finset.sum_congr rfl
    intro B _
    by_cases hB : B.Nonempty
    · have hcard : B.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hB)
      simp [hB, hcard, weight, kernel]
    · have hcard : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB)
      simp [hB, hcard]
  · rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_powersetCard k A (fun i => if i = 0 then (0 : ℝ) else weight (i-1) (A.card-i))]
    simp [nsmul_eq_mul]

theorem hPot_one_eq_of_card_eq (A B : Finset X) (h : A.card = B.card) :
    hPot (fun _ : Finset X => (1 : ℝ)) A = hPot (fun _ : Finset X => (1 : ℝ)) B := by
  rw [hPot_one_card, hPot_one_card, h]

theorem hPot_sub_const (g : Finset X → ℝ) (c : ℝ) (A : Finset X) :
    hPot (fun B => g B - c) A = hPot g A - c * hPot (fun _ => 1) A := by
  simp only [hPot, sub_mul, Finset.sum_sub_distrib, one_mul, Finset.mul_sum]

theorem hPot_shift_difference (g : Finset X → ℝ) (c : ℝ)
    (A B : Finset X) (h : A.card = B.card) :
    hPot (fun C => g C - c) A - hPot (fun C => g C - c) B = hPot g A - hPot g B := by
  rw [hPot_sub_const, hPot_sub_const, hPot_one_eq_of_card_eq A B h]
  ring

theorem normalized_properties (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) :
    (∀ A, 0 ≤ g A - g ∅) ∧ (g ∅ - g ∅ = 0) ∧
    MonoInc (fun A => g A - g ∅) ∧
    NonmonotoneSubmod.Shared.Submodular (fun A => g A - g ∅) := by
  refine ⟨?_, sub_self _, ?_, ?_⟩
  · intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert a A ha ih =>
      have h := hm A a
      unfold marg at h
      linarith
  · intro A a
    have h := hm A a
    unfold marg at h ⊢
    linarith
  · intro A B
    have h := hs A B
    linarith

theorem normalization_transfer (g : Finset X → ℝ) (hzero : 0 ≤ g ∅)
    (A B : Finset X) (T : X → Finset X) (hcard : ∀ a ∈ A, A.card = (T a).card)
    (hbound : (g B - g ∅) + ∑ a ∈ A,
      (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a)) ≤
      Real.exp 1 / (Real.exp 1 - 1) * (g A - g ∅)) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (T a)) ≤
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hsum : (∑ a ∈ A,
      (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a))) =
      ∑ a ∈ A, (hPot g A - hPot g (T a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hPot_shift_difference g (g ∅) A (T a) (hcard a ha)
  rw [hsum] at hbound
  have hfactor : (1 : ℝ) ≤ Real.exp 1 / (Real.exp 1 - 1) := by
    apply (le_div_iff₀ denom_pos).mpr
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hzero]

theorem coefficient_balance (g : Finset X → ℝ) (A : Finset X) :
    (∑ B ∈ A.powerset, g B *
      (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1))) =
      Real.exp 1 / (Real.exp 1 - 1) * g A - 1 / (Real.exp 1 - 1) * g ∅ := by
  trans ∑ B ∈ A.powerset,
    ((if B = A then Real.exp 1 / (Real.exp 1 - 1) * g A else 0) -
      (if B = ∅ then 1 / (Real.exp 1 - 1) * g ∅ else 0))
  · apply Finset.sum_congr rfl
    intro B hB
    have hsub : B ⊆ A := Finset.mem_powerset.mp hB
    have hcard : A.card - B.card = 0 ↔ B = A := by
      constructor
      · intro h
        exact Finset.eq_of_subset_of_card_le hsub (Nat.sub_eq_zero_iff_le.mp h)
      · rintro rfl
        simp
    rw [weight_recurrence]
    simp only [hcard, Finset.card_eq_zero]
    split_ifs <;> simp_all <;> ring
  · rw [Finset.sum_sub_distrib]
    simp

end PotentialNormalization

theorem coefficient_identities :
    (∀ k j : ℕ, 0 ≤ PotentialCoefficients.weight k j) ∧
    PotentialCoefficients.weight 0 0 = 1 ∧
    (∀ k j : ℕ, PotentialCoefficients.weight k j =
      PotentialCoefficients.weight (k+1) j + PotentialCoefficients.weight k (j+1)) ∧
    (∀ k j : ℕ, PotentialCoefficients.weight k j +
      (k : ℝ) * PotentialCoefficients.weight (k-1) j -
      (j : ℝ) * PotentialCoefficients.weight k (j-1) =
      (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
      (if k = 0 then 1 / (Real.exp 1 - 1) else 0)) :=
  ⟨PotentialCoefficients.weight_nonneg, PotentialCoefficients.weight_zero_zero,
    PotentialCoefficients.weight_pascal, PotentialCoefficients.weight_recurrence⟩



open CurvatureSubmod.LocalSearch PotentialCoefficients

theorem previous_potential_support {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (A : Finset X) :
    (∀ k j : ℕ, 0 ≤ weight k j) ∧
    weight 0 0 = 1 ∧
    (∀ k j : ℕ, weight k j = weight (k+1) j + weight k (j+1)) ∧
    (∀ k j : ℕ, weight k j + (k : ℝ) * weight (k-1) j - (j : ℝ) * weight k (j-1) =
      (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
      (if k = 0 then 1 / (Real.exp 1 - 1) else 0)) ∧
    ((∑ B ∈ A.powerset, g B *
      (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1))) =
      Real.exp 1 / (Real.exp 1 - 1) * g A - 1 / (Real.exp 1 - 1) * g ∅) ∧
    (∀ (c : ℝ) (B : Finset X), A.card = B.card →
      hPot (fun C => g C - c) A - hPot (fun C => g C - c) B = hPot g A - hPot g B) ∧
    (MonoInc g → NonmonotoneSubmod.Shared.Submodular g →
      (∀ B, 0 ≤ g B - g ∅) ∧ (g ∅ - g ∅ = 0) ∧
      MonoInc (fun B => g B - g ∅) ∧
      NonmonotoneSubmod.Shared.Submodular (fun B => g B - g ∅)) ∧
    (∀ (B : Finset X) (T : X → Finset X), 0 ≤ g ∅ →
      (∀ a ∈ A, A.card = (T a).card) →
      ((g B - g ∅) + ∑ a ∈ A,
        (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a)) ≤
        Real.exp 1 / (Real.exp 1 - 1) * (g A - g ∅)) →
      g B + ∑ a ∈ A, (hPot g A - hPot g (T a)) ≤
        Real.exp 1 / (Real.exp 1 - 1) * g A) := by
  refine ⟨weight_nonneg, weight_zero_zero, weight_pascal, weight_recurrence,
    PotentialNormalization.coefficient_balance g A, ?_, ?_, ?_⟩
  · intro c B h
    exact PotentialNormalization.hPot_shift_difference g c A B h
  · exact PotentialNormalization.normalized_properties g
  · intro B T hzero hcard hbound
    exact PotentialNormalization.normalization_transfer g hzero A B T hcard hbound

-- Dropping the lower endpoint term is already false for the empty-set coefficient.
theorem endpoint_control : weight 0 0 ≠ Real.exp 1 / (Real.exp 1 - 1) := by
  rw [weight_zero_zero]
  apply ne_of_lt
  apply (lt_div_iff₀ denom_pos).mpr
  linarith

#print axioms previous_potential_support
#print axioms endpoint_control

/- Further marginal representation, 23 October 2026. The preceding coefficient
and normalization proof is retained from our checked turn3 packet, SHA256
c0726137cae5c2854202215241a9c5f73c813e8ade8b583f699cbfc65a0d3104.
Source: Filmus and Ward, arXiv:1204.4526v4, Lemma1 and the exchange argument.
The following lemmas complete Equation5.4 without an open theorem dependency. -/
namespace PotentialMarginals
open CurvatureSubmod.LocalSearch PotentialCoefficients
variable {X : Type} [Fintype X] [DecidableEq X]

theorem hPot_sum (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    hPot g A = ∑ B ∈ A.powerset, g B * weight (B.card-1) (A.card-B.card) := by
  unfold hPot
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hn : B.Nonempty
  · simp [hn, weight, kernel]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    subst B
    simp [hg]

theorem marginal_representation (g : Finset X → ℝ) (hg : g ∅ = 0)
    (A : Finset X) (a : X) (ha : a ∉ A) :
    hPot g (insert a A) - hPot g A =
      ∑ B ∈ A.powerset, weight B.card (A.card-B.card) * (g (insert a B) - g B) := by
  rw [hPot_sum g hg, hPot_sum g hg, Finset.sum_powerset_insert ha,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hBA := Finset.mem_powerset.mp hB
  have hcard := Finset.card_le_card hBA
  have hab : a ∉ B := fun h => ha (hBA h)
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hab]
  have hsub : A.card + 1 - B.card = (A.card-B.card)+1 := by omega
  have hsub2 : A.card + 1 - (B.card+1) = A.card-B.card := by omega
  rw [hsub, hsub2, Nat.add_sub_cancel]
  by_cases hz : B = ∅
  · subst B
    simp [hg, mul_comm]
  · have hb : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have hpas := weight_pascal (B.card-1) (A.card-B.card)
    rw [Nat.sub_add_cancel hb] at hpas
    rw [hpas]
    ring

noncomputable def expect (A : Finset X) (f : Finset X → ℝ) : ℝ :=
  ∑ B ∈ A.powerset, weight B.card (A.card-B.card) * f B

theorem expect_insert (A : Finset X) (a : X) (ha : a ∉ A) (f : Finset X → ℝ) :
    expect (insert a A) f = ∑ B ∈ A.powerset,
      (weight B.card (A.card-B.card+1) * f B +
        weight (B.card+1) (A.card-B.card) * f (insert a B)) := by
  unfold expect
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hBA := Finset.mem_powerset.mp hB
  have hcard := Finset.card_le_card hBA
  have hab : a ∉ B := fun h => ha (hBA h)
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hab]
  congr 3 <;> omega

theorem expect_const (A : Finset X) (c : ℝ) : expect A (fun _ => c) = c := by
  induction A using Finset.induction_on with
  | empty => simp [expect,weight_zero_zero]
  | @insert a A ha ih =>
    rw [expect_insert A a ha]
    calc
      _ = expect A (fun _ => c) := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [← add_mul, add_comm, ← weight_pascal]
      _ = c := ih

theorem expect_insert_le (A : Finset X) (a : X) (ha : a ∉ A) (f : Finset X → ℝ)
    (hf : ∀ B ⊆ A, f (insert a B) ≤ f B) : expect (insert a A) f ≤ expect A f := by
  rw [expect_insert A a ha]
  apply Finset.sum_le_sum
  intro B hB
  have hm := mul_le_mul_of_nonneg_left (hf B (Finset.mem_powerset.mp hB))
    (weight_nonneg (B.card+1) (A.card-B.card))
  have hp := weight_pascal B.card (A.card-B.card)
  rw [hp, add_mul]
  linarith

theorem marg_antitone (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X) (hAB : A ⊆ B) (b : X) :
    marg g B b ≤ marg g A b := by
  by_cases hb : b ∈ B
  · simpa [marg,Finset.insert_eq_of_mem hb] using hm A b
  · have hu : insert b A ∪ B = insert b B := by ext x; simp; aesop
    have hi : insert b A ∩ B = A := by ext x; simp; aesop
    have h := hs (insert b A) B
    rw [hu,hi] at h
    unfold marg
    linarith

theorem expect_marg_insert_le (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (a b : X) (ha : a ∉ A) :
    expect (insert a A) (fun B => marg g B b) ≤ expect A (fun B => marg g B b) := by
  apply expect_insert_le A a ha
  intro B hB
  exact marg_antitone g hm hs B (insert a B) (Finset.subset_insert _ _) b


theorem swap_comparison (g : Finset X → ℝ) (hg : g ∅ = 0) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (a b : X)
    (ha : a ∈ A) (hb : b ∉ A.erase a) :
    hPot g A - hPot g (insert b (A.erase a)) ≤
      (hPot g A - hPot g (A.erase a)) - expect A (fun B => marg g B b) := by
  have h := expect_marg_insert_le g hm hs (A.erase a) a b (Finset.notMem_erase _ _)
  rw [Finset.insert_erase ha] at h
  have hr := marginal_representation g hg (A.erase a) b hb
  change hPot g (insert b (A.erase a)) - hPot g (A.erase a) =
    expect (A.erase a) (fun B => marg g B b) at hr
  linarith

theorem monoInc_monotone (g : Finset X → ℝ) (hm : MonoInc g) : Monotone g := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro A a ha
  exact sub_nonneg.mp (hm A a)

theorem union_marginal_bound (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (T B : Finset X) :
    g (T ∪ B) ≤ g T + ∑ b ∈ B, marg g T b := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.sum_insert hb, Finset.union_insert]
    have h := marg_antitone g hm hs T (T ∪ B) Finset.subset_union_left b
    simp only [marg] at h ih ⊢
    linarith

theorem marginal_sum_bound (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (T B : Finset X) :
    g B - g T ≤ ∑ b ∈ B, marg g T b := by
  have h := union_marginal_bound g hm hs T B
  have hmono := monoInc_monotone g hm (show B ⊆ T ∪ B from Finset.subset_union_right)
  linarith

theorem expected_marginal_sum (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X) :
    g B - expect A g ≤ ∑ b ∈ B, expect A (fun T => marg g T b) := by
  have h : expect A (fun T => g B - g T) ≤
      expect A (fun T => ∑ b ∈ B, marg g T b) := by
    apply Finset.sum_le_sum
    intro T hT
    exact mul_le_mul_of_nonneg_left (marginal_sum_bound g hm hs T B)
      (weight_nonneg T.card (A.card-T.card))
  have he : expect A (fun T => g B - g T) = g B - expect A g := by
    simp only [expect,mul_sub,Finset.sum_sub_distrib]
    rw [← expect, expect_const]
  have he2 : expect A (fun T => ∑ b ∈ B, marg g T b) =
      ∑ b ∈ B, expect A (fun T => marg g T b) := by
    simp only [expect,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he,he2] at h
  exact h


theorem powerset_erase (A : Finset X) (a : X) :
    (A.erase a).powerset = A.powerset.filter (fun B => a ∉ B) := by
  ext B
  simp [Finset.subset_erase, and_comm]

theorem sum_erased_potential (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    (∑ a ∈ A, hPot g (A.erase a)) =
      ∑ B ∈ A.powerset, ((A.card-B.card : ℕ) : ℝ) *
        (g B * weight (B.card-1) (A.card-1-B.card)) := by
  calc
    _ = ∑ a ∈ A, ∑ B ∈ A.powerset,
        if a ∉ B then g B * weight (B.card-1) (A.card-1-B.card) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hPot_sum g hg, powerset_erase, Finset.sum_filter, Finset.card_erase_of_mem ha]
    _ = ∑ B ∈ A.powerset, ∑ a ∈ A,
        if a ∉ B then g B * weight (B.card-1) (A.card-1-B.card) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      have hBA := Finset.mem_powerset.mp hB
      rw [← Finset.sum_filter]
      have hf : A.filter (fun a => a ∉ B) = A \ B := by ext a; simp
      rw [hf, Finset.sum_const, Finset.card_sdiff_of_subset hBA]
      simp [nsmul_eq_mul]


theorem deletion_identity (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    (∑ a ∈ A, (hPot g A - hPot g (A.erase a))) + expect A g =
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,sum_erased_potential g hg,
    hPot_sum g hg,Finset.mul_sum]
  unfold expect
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ B ∈ A.powerset, g B *
        (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1)) := by
      apply Finset.sum_congr rfl
      intro B hB
      have hcard := Finset.card_le_card (Finset.mem_powerset.mp hB)
      by_cases hzero : B = ∅
      · subst B; simp [hg]
      by_cases heq : B = A
      · subst B; simp; ring
      have hb : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
      have hlt : B.card < A.card := lt_of_le_of_ne hcard (by
        intro hc
        exact heq (Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hB) hc.ge))
      have hj : 1 ≤ A.card-B.card := by omega
      have hs : A.card-1-B.card = A.card-B.card-1 := by omega
      have hpas := weight_pascal (B.card-1) (A.card-B.card-1)
      rw [Nat.sub_add_cancel hb,Nat.sub_add_cancel hj] at hpas
      have hc : (A.card : ℝ) = (B.card : ℝ) + ((A.card-B.card : ℕ) : ℝ) := by
        exact_mod_cast (show A.card = B.card + (A.card-B.card) by omega)
      rw [hs,hpas,hc]
      ring
    _ = _ := by rw [PotentialNormalization.coefficient_balance,hg,mul_zero,sub_zero]


theorem normalized_exchange_bound (g : Finset X → ℝ) (hg : g ∅ = 0) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X)
    (π : X → X) (hπ : Set.BijOn π (A : Set X) (B : Set X))
    (hnew : ∀ a ∈ A, π a ∉ A.erase a) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a))) ≤
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hsum := Finset.sum_le_sum (s := A) (fun a ha => swap_comparison g hg hm hs A a (π a) ha (hnew a ha))
  have hbij : (∑ a ∈ A, expect A (fun T => marg g T (π a))) =
      ∑ b ∈ B, expect A (fun T => marg g T b) := by
    apply Finset.sum_bij (fun a _ => π a)
    · intro a ha; exact hπ.mapsTo ha
    · intro a ha a' ha' he; exact hπ.injOn ha ha' he
    · intro b hb; obtain ⟨a,ha,he⟩ := hπ.surjOn hb; exact ⟨a,ha,he⟩
    · intro a ha; rfl
  simp only [Finset.sum_sub_distrib] at hsum
  rw [hbij] at hsum
  have hcover := expected_marginal_sum g hm hs A B
  have hdel := deletion_identity g hg A
  simp only [Finset.sum_sub_distrib] at hdel ⊢
  linarith

end PotentialMarginals
#print axioms PotentialMarginals.marginal_representation

open CurvatureSubmod.LocalSearch PotentialMarginals

theorem solution {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X))
    (π : X → X) (hπ : Set.BijOn π (↑A : Set X) (↑B : Set X))
    (hswap : ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X)) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hcard : ∀ a ∈ A, A.card = (insert (π a) (A.erase a)).card := by
    intro a ha
    have hc := hA.ncard_eq_ncard_of_isBase (hswap a ha)
    simpa only [Set.ncard_coe_finset] using hc
  have hnew : ∀ a ∈ A, π a ∉ A.erase a := by
    intro a ha hb
    have hc := hcard a ha
    rw [Finset.insert_eq_of_mem hb,Finset.card_erase_of_mem ha] at hc
    have hp : 0 < A.card := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  have hn := PotentialNormalization.normalized_properties g hgmono hgsub
  apply PotentialNormalization.normalization_transfer g (hg0 ∅) A B
    (fun a => insert (π a) (A.erase a)) hcard
  exact normalized_exchange_bound (fun C => g C - g ∅) hn.2.1 hn.2.2.1 hn.2.2.2 A B π hπ hnew

#print axioms solution
