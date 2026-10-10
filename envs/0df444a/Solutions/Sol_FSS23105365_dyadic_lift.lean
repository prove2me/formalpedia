-- Prove2me | solution 1 for FSS23105365.dyadic_lift
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T15:41:11.691991+00:00
-- url     : https://prove2.me/submissions/4fa922a0-9665-4f8b-95f6-4cdfde4f253f

-- Standalone proof of Lemma E.4, generated from the audited local proof modules.
-- Imports only Mathlib and the mission definitions; no unproved theorem imports.
import Definitions.Def_FSS23105365_FiniteState
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Prod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

-- From Solutions.FSS23105365_PathWeights
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The same finite path product as `pathLaw`, on an arbitrary finite state
type. This permits the sigma-type state copies in the E.4 construction. -/
def finitePathWeight {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) : ℝ :=
  μ (η 0) * ∏ i : Fin n, P (η i.castSucc) (η i.succ)

theorem pathLaw_eq_finitePathWeight {q n : ℕ} (M : MarkovChain q) (γ : Path q n) :
    pathLaw M γ = finitePathWeight M.initial M.transition γ := rfl

@[simp] theorem finitePathWeight_snoc {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) (h : H) :
    finitePathWeight μ P (Fin.snoc η h) =
      finitePathWeight μ P η * P (η (Fin.last n)) h := by
  simp only [finitePathWeight, Fin.prod_univ_castSucc]
  simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.succ_last, Fin.snoc_apply_zero]
  ring

theorem map_snoc {H Q : Type} (φ : H → Q) {n : ℕ}
    (η : Fin n → H) (h : H) :
    (fun i => φ ((Fin.snoc η h : Fin (n + 1) → H) i)) =
      Fin.snoc (fun i => φ (η i)) (φ h) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Joint mass of the observed path and the final hidden state. -/
def endpointPathMass {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) : ℝ :=
  ∑ η : Fin (n + 1) → H,
    if (fun i => φ (η i)) = γ ∧ η (Fin.last n) = h then finitePathWeight μ P η else 0

theorem endpointPathMass_zero {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q) (γ : Fin 1 → Q) (h : H) :
    endpointPathMass μ P φ γ h = if φ h = γ 0 then μ h else 0 := by
  classical
  let e : H ≃ (Fin 1 → H) := (Equiv.funUnique (Fin 1) H).symm
  have he := e.sum_comp (fun η : Fin 1 → H =>
    if (fun i => φ (η i)) = γ ∧ η (Fin.last 0) = h then finitePathWeight μ P η else 0)
  rw [endpointPathMass, ← he]
  have heval (a : H) : e a = fun _ => a := rfl
  simp only [heval, finitePathWeight, Fin.prod_univ_zero, mul_one]
  have hfun (a : H) : (fun _ : Fin 1 => φ a) = γ ↔ φ a = γ 0 := by
    constructor
    · intro ha; exact congrFun ha 0
    · intro ha
      funext i
      have hi : i = 0 := by apply Fin.ext; omega
      simpa [hi] using ha
  simp only [hfun]
  simp [and_comm, ite_and]

theorem endpointPathMass_step_sum {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) :
    (∑ a, endpointPathMass μ P φ γ a * P a h) =
      ∑ η : Fin (n + 1) → H, if (fun i => φ (η i)) = γ then
        finitePathWeight μ P η * P (η (Fin.last n)) h else 0 := by
  classical
  simp only [endpointPathMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hη : (fun i => φ (η i)) = γ
  · simp [hη, ite_mul]
  · simp [hη]

theorem endpointPathMass_snoc {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (q : Q) (h : H) :
    endpointPathMass μ P φ (Fin.snoc γ q) h =
      if φ h = q then ∑ a, endpointPathMass μ P φ γ a * P a h else 0 := by
  classical
  rw [endpointPathMass]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => H)).sum_comp]
  have heval (z : H × (Fin (n + 1) → H)) :
      (Fin.snocEquiv (fun _ : Fin (n + 2) => H)) z = Fin.snoc z.2 z.1 := rfl
  simp only [heval, map_snoc, Fin.snoc_inj,
    Fin.snoc_last, finitePathWeight_snoc]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single h]
  · rw [endpointPathMass_step_sum]
    by_cases hh : φ h = q
    · simp [hh]
    · simp [hh]
  · intro a _ ha
    simp [ha]
  · simp

/-- The fiber invariant in E.4, including zero-probability paths. Only the
initial masses and column margins are needed for this algebraic identity. -/
theorem endpointPathMass_fiber_invariant {H Q : Type} [Fintype H]
    [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    (μ₀ : Q → ℝ) (P₀ : Q → Q → ℝ) (w : Q → ℝ)
    (hw : ∀ q, w q ≠ 0)
    (hμ : ∀ h, μ h = μ₀ (φ h) / w (φ h))
    (hP : ∀ q h, (∑ a, if φ a = q then P a h else 0) =
      w q * P₀ q (φ h) / w (φ h))
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) :
    endpointPathMass μ P φ γ h =
      if φ h = γ (Fin.last n) then finitePathWeight μ₀ P₀ γ / w (γ (Fin.last n)) else 0 := by
  classical
  induction n generalizing h with
  | zero =>
    rw [endpointPathMass_zero]
    simp only [finitePathWeight, Fin.prod_univ_zero, mul_one, Fin.last_zero]
    by_cases hh : φ h = γ 0
    · simp [hh, hμ]
    · simp [hh]
  | succ n ih =>
    rcases (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)).surjective γ with ⟨⟨x, η⟩, rfl⟩
    have heval : (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)) (x, η) =
        Fin.snoc η x := rfl
    rw [heval, Fin.snoc_last, endpointPathMass_snoc]
    by_cases hh : φ h = x
    · simp only [if_pos hh]
      simp_rw [ih]
      calc
        (∑ a, (if φ a = η (Fin.last n) then
            finitePathWeight μ₀ P₀ η / w (η (Fin.last n)) else 0) * P a h) =
            (finitePathWeight μ₀ P₀ η / w (η (Fin.last n))) *
              ∑ a, if φ a = η (Fin.last n) then P a h else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ = _ := by
          rw [hP, hh, finitePathWeight_snoc]
          field_simp [hw]
    · simp [hh]

theorem sum_endpointPathMass {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    (∑ h, endpointPathMass μ P φ γ h) =
      ∑ η : Fin (n + 1) → H,
        if (fun i => φ (η i)) = γ then finitePathWeight μ P η else 0 := by
  classical
  simp only [endpointPathMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hη : (fun i => φ (η i)) = γ <;> simp [hη]

/-- Summing the invariant over the last fiber proves equality of the
entire projected path distribution, as required in E.4. -/
theorem projected_finitePathWeight_eq {H Q : Type} [Fintype H]
    [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    (μ₀ : Q → ℝ) (P₀ : Q → Q → ℝ) (w : Q → ℝ)
    (hw : ∀ q, w q ≠ 0)
    (hμ : ∀ h, μ h = μ₀ (φ h) / w (φ h))
    (hP : ∀ q h, (∑ a, if φ a = q then P a h else 0) =
      w q * P₀ q (φ h) / w (φ h))
    (hcard : ∀ q, (Fintype.card {h : H // φ h = q} : ℝ) = w q)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    (∑ η : Fin (n + 1) → H,
      if (fun i => φ (η i)) = γ then finitePathWeight μ P η else 0) =
        finitePathWeight μ₀ P₀ γ := by
  rw [← sum_endpointPathMass]
  simp_rw [endpointPathMass_fiber_invariant μ P φ μ₀ P₀ w hw hμ hP]
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype, hcard]
  exact mul_div_cancel₀ _ (hw _)

end FSS23105365

-- From Solutions.FSS23105365_RationalPathFacts
set_option autoImplicit false
namespace FSS23105365

theorem dyadic_is_rational {x : ℝ} (hx : Dyadic x) : ∃ a : ℚ, (a : ℝ) = x := by
  rcases hx with ⟨a, k, rfl⟩
  exact ⟨(a : ℚ) / 2 ^ k, by push_cast; rfl⟩

/-- Reachability with positive probability, as used when deleting
unreachable states in the first sentence of the E.4 proof. -/
def PositivelyReachable {q : ℕ} (M : MarkovChain q) (x : Fin q) : Prop :=
  ∃ n : ℕ, ∃ γ : Path q n, γ (Fin.last n) = x ∧ 0 < pathLaw M γ

theorem positivelyReachable_of_initial {q : ℕ} (M : MarkovChain q) (x : Fin q)
    (hx : 0 < M.initial x) : PositivelyReachable M x := by
  refine ⟨0, fun _ => x, rfl, ?_⟩
  simpa [pathLaw] using hx

theorem positivelyReachable_step {q : ℕ} (M : MarkovChain q) (x y : Fin q)
    (hx : PositivelyReachable M x) (hxy : 0 < M.transition x y) :
    PositivelyReachable M y := by
  obtain ⟨n, γ, hlast, hγ⟩ := hx
  refine ⟨n + 1, Fin.snoc γ y, Fin.snoc_last _ _, ?_⟩
  rw [pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
    ← pathLaw_eq_finitePathWeight]
  exact mul_pos hγ hxy

/-- Rationality in E.4 follows by dividing the dyadic probability of an
extended path by the positive dyadic probability of its prefix. The
transition itself is not assumed dyadic. -/
theorem pathDyadic_transition_rational {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (x y : Fin q) (hx : PositivelyReachable M x) :
    ∃ a : ℚ, (a : ℝ) = M.transition x y := by
  obtain ⟨n, γ, hlast, hγ⟩ := hx
  obtain ⟨a, ha⟩ := dyadic_is_rational (hM (n + 1) (Fin.snoc γ y))
  obtain ⟨b, hb⟩ := dyadic_is_rational (hM n γ)
  refine ⟨a / b, ?_⟩
  rw [Rat.cast_div, ha, hb, pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
    ← pathLaw_eq_finitePathWeight]
  field_simp [ne_of_gt hγ]

theorem pathDyadic_initial_dyadic {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (x : Fin q) : Dyadic (M.initial x) := by
  simpa [pathLaw] using hM 0 (fun _ => x)

end FSS23105365

-- From Solutions.FSS23105365_DyadicValuations
set_option autoImplicit false
namespace FSS23105365

theorem dyadic_rat_cast_iff (x : ℚ) :
    Dyadic (x : ℝ) ↔ ∃ a k : ℕ, x = (a : ℚ) / 2 ^ k := by
  constructor
  · rintro ⟨a, k, hx⟩
    refine ⟨a, k, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    simpa using hx
  · rintro ⟨a, k, rfl⟩
    exact ⟨a, k, by push_cast; rfl⟩

/-- A nonnegative rational whose reduced denominator is a power of two is
dyadic in the real-valued probability definition used by the mission. -/
theorem dyadic_of_rat_den_pow (x : ℚ) (hx : 0 ≤ x) (k : ℕ)
    (hden : x.den = 2 ^ k) : Dyadic (x : ℝ) := by
  have hn : (x.num.toNat : ℝ) = (x.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
  refine ⟨x.num.toNat, k, ?_⟩
  rw [Rat.cast_def, hden, hn]
  simp

/-- Odd-prime valuations of nonzero dyadic probabilities are nonnegative,
the fact that makes the minimum in E.4 well-founded. -/
theorem dyadic_odd_padicVal_nonneg (x : ℚ) (hx : Dyadic (x : ℝ))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : 0 ≤ padicValRat p x := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, k, rfl⟩ := (dyadic_rat_cast_iff x).mp hx
  by_cases ha : a = 0
  · simp [ha]
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have ht : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes hp2]
    simp
  rw [padicValRat.div ha' (pow_ne_zero _ (by norm_num)), padicValRat.pow, ht]
  simp

/-- The converse number-theoretic criterion needed in E.4: nonnegative
valuations at every prime other than two exclude every odd factor from
the reduced denominator. -/
theorem dyadic_of_odd_padicVal_nonneg (x : ℚ) (hx : 0 ≤ x)
    (hval : ∀ p : ℕ, p.Prime → p ≠ 2 → 0 ≤ padicValRat p x) :
    Dyadic (x : ℝ) := by
  have hnodvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ x.den := by
    intro hd
    let : Fact p.Prime := ⟨hp⟩
    have hn : ¬ p ∣ x.num.natAbs := by
      intro hn
      have hg : p ∣ 1 := by
        simpa only [x.reduced] using Nat.dvd_gcd hn hd
      exact hp.ne_one (Nat.dvd_one.mp hg)
    have hvn : padicValInt p x.num = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hvd : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hd
    have hv := hval p hp hp2
    rw [padicValRat_def, hvn] at hv
    omega
  have hfac : x.den.factorization = Finsupp.single 2 (x.den.factorization 2) := by
    ext p
    by_cases hp2 : p = 2
    · subst p; simp
    rw [Finsupp.single_eq_of_ne hp2]
    by_cases hp : p.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd (hnodvd p hp hp2)
    · exact Nat.factorization_eq_zero_of_not_prime _ hp
  have hden : x.den = 2 ^ x.den.factorization 2 := by
    calc
      x.den = x.den.factorization.prod (· ^ ·) :=
        (Nat.prod_factorization_pow_eq_self x.den_ne_zero).symm
      _ = 2 ^ x.den.factorization 2 := by rw [hfac]; simp
  exact dyadic_of_rat_den_pow x hx _ hden

end FSS23105365

-- From Solutions.FSS23105365_DyadicFacts
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem dyadic_zero : Dyadic 0 := by
  exact ⟨0, 0, by simp⟩

theorem dyadic_one : Dyadic 1 := by
  exact ⟨1, 0, by simp⟩

theorem dyadic_mul {x y : ℝ} (hx : Dyadic x) (hy : Dyadic y) :
    Dyadic (x * y) := by
  rcases hx with ⟨a, k, rfl⟩
  rcases hy with ⟨b, l, rfl⟩
  exact ⟨a * b, k + l, by simp [Nat.cast_mul, pow_add, div_mul_div_comm]⟩

theorem dyadic_add {x y : ℝ} (hx : Dyadic x) (hy : Dyadic y) :
    Dyadic (x + y) := by
  rcases hx with ⟨a, k, rfl⟩
  rcases hy with ⟨b, l, rfl⟩
  refine ⟨a * 2 ^ l + b * 2 ^ k, k + l, ?_⟩
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  simpa only [mul_comm] using
    div_add_div (a : ℝ) (b : ℝ)
      (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero l (by norm_num : (2 : ℝ) ≠ 0))

theorem dyadic_finset_prod {α : Type} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, Dyadic (f x)) : Dyadic (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dyadic_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact dyadic_mul (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

theorem dyadic_finset_sum {α : Type} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, Dyadic (f x)) : Dyadic (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dyadic_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact dyadic_add (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/-- The elementary dyadic closure used by the finite-chain constructions. -/
theorem transitionDyadic_pathDyadic {q : ℕ} (M : MarkovChain q)
    (h : TransitionDyadic M) : PathDyadic M := by
  intro n γ
  apply dyadic_mul (h.1 _)
  exact dyadic_finset_prod Finset.univ _ (fun i _ => h.2 _ _)

/-- Coordinatewise projection preserves path-dyadicity, even without injectivity. -/
theorem projectedPathLaw_dyadic {q r : ℕ} (M : MarkovChain r)
    (h : PathDyadic M) (φ : Fin r → Fin q) (n : ℕ) (γ : Path q n) :
    Dyadic (projectedPathLaw M φ γ) := by
  classical
  apply dyadic_finset_sum Finset.univ
  intro η _
  split_ifs
  · exact h n η
  · exact dyadic_zero

end FSS23105365

-- From Solutions.FSS23105365_DyadicWeightExistence
set_option autoImplicit false
namespace FSS23105365

/-- The odd-prime valuation minimum in E.4 is attained: its possible
values form a nonempty subset of the natural numbers. -/
theorem exists_minimum_odd_valuation (S : Set ℚ) (hne : S.Nonempty)
    (hd : ∀ a ∈ S, Dyadic (a : ℝ)) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ k : ℕ, (∃ a ∈ S, padicValRat p a = (k : ℤ)) ∧
      ∀ a ∈ S, (k : ℤ) ≤ padicValRat p a := by
  classical
  have hn (a : ℚ) (ha : a ∈ S) : 0 ≤ padicValRat p a :=
    dyadic_odd_padicVal_nonneg a (hd a ha) p hp hp2
  have hex : ∃ k : ℕ, ∃ a ∈ S, padicValRat p a = (k : ℤ) := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨(padicValRat p a).toNat, a, ha, (Int.toNat_of_nonneg (hn a ha)).symm⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun a ha => ?_⟩
  have hb : Nat.find hex ≤ (padicValRat p a).toNat :=
    Nat.find_min' hex ⟨a, ha, (Int.toNat_of_nonneg (hn a ha)).symm⟩
  calc
    (Nat.find hex : ℤ) ≤ ((padicValRat p a).toNat : ℤ) := by exact_mod_cast hb
    _ = padicValRat p a := Int.toNat_of_nonneg (hn a ha)

/-- The minima over a set of dyadic probabilities are the odd-prime
valuations of one positive integer. A single member bounds their support. -/
theorem exists_dyadic_set_weight (S : Set ℚ) (hne : S.Nonempty)
    (hd : ∀ a ∈ S, Dyadic (a : ℝ)) :
    ∃ w : ℕ, 0 < w ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ a ∈ S, padicValRat p a = padicValRat p (w : ℚ)) ∧
      ∀ a ∈ S, padicValRat p (w : ℚ) ≤ padicValRat p a := by
  classical
  have hex (p : ℕ) : ∃ k : ℕ,
      ((p.Prime ∧ p ≠ 2) →
        (∃ a ∈ S, padicValRat p a = (k : ℤ)) ∧ ∀ a ∈ S, (k : ℤ) ≤ padicValRat p a) ∧
      (¬ (p.Prime ∧ p ≠ 2) → k = 0) := by
    by_cases hp : p.Prime ∧ p ≠ 2
    · obtain ⟨k, hk, hb⟩ := exists_minimum_odd_valuation S hne hd p hp.1 hp.2
      exact ⟨k, fun _ => ⟨hk, hb⟩, fun h => (h hp).elim⟩
    · exact ⟨0, fun h => (hp h).elim, fun _ => rfl⟩
  choose a ha hz using hex
  obtain ⟨b, hb⟩ := hne
  have hsupp (p : ℕ) (hap : a p ≠ 0) : p ∈ b.num.natAbs.factorization.support := by
    have hp : p.Prime ∧ p ≠ 2 := by
      by_contra hp
      exact hap (hz p hp)
    have hbound := (ha p hp).2 b hb
    have hv : padicValNat p b.num.natAbs ≠ 0 := by
      rw [padicValRat_def, padicValInt] at hbound
      omega
    rw [Finsupp.mem_support_iff, Nat.factorization_def _ hp.1]
    exact hv
  let f : ℕ →₀ ℕ := Finsupp.onFinset b.num.natAbs.factorization.support a hsupp
  have hf (p : ℕ) : f p = a p := rfl
  have hfprime (p : ℕ) (hp : p ∈ f.support) : p.Prime := by
    have hap : a p ≠ 0 := by simpa only [hf] using Finsupp.mem_support_iff.mp hp
    by_contra hnp
    exact hap (hz p (fun h => hnp h.1))
  let w : ℕ := f.prod (· ^ ·)
  have hw : 0 < w := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hfprime p hp).pos _
  have hwfac : w.factorization = f := Nat.prod_pow_factorization_eq_self hfprime
  have hwval (p : ℕ) (hp : p.Prime) : padicValRat p (w : ℚ) = (a p : ℤ) := by
    rw [padicValRat.of_nat, ← Nat.factorization_def _ hp, hwfac, hf]
  refine ⟨w, hw, fun p hp hp2 => ?_⟩
  rw [hwval p hp]
  exact ha p ⟨hp, hp2⟩

/-- Abstract form of the valuation construction in E.4. The sets `S q`
will be the positive path probabilities ending at state `q`. -/
theorem exists_weights_of_dyadic_path_sets {Q : Type} (S : Q → Set ℚ)
    (hne : ∀ q, (S q).Nonempty)
    (hpos : ∀ q a, a ∈ S q → 0 < a)
    (hd : ∀ q a, a ∈ S q → Dyadic (a : ℝ))
    (μ : Q → ℚ) (P : Q → Q → ℚ)
    (hμn : ∀ q, 0 ≤ μ q) (hPn : ∀ q r, 0 ≤ P q r)
    (hμmem : ∀ q, 0 < μ q → μ q ∈ S q)
    (hclosed : ∀ q r a, a ∈ S q → 0 < P q r → a * P q r ∈ S r) :
    ∃ w : Q → ℕ, (∀ q, 0 < w q) ∧
      (∀ q, Dyadic ((μ q / (w q : ℚ) : ℚ) : ℝ)) ∧
      (∀ q r, Dyadic ((((w q : ℚ) * P q r) / (w r : ℚ) : ℚ) : ℝ)) := by
  classical
  choose w hw hmin using fun q => exists_dyadic_set_weight (S q) (hne q) (hd q)
  have hwn (q : Q) : (w q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw q))
  refine ⟨w, hw, fun q => ?_, fun q r => ?_⟩
  · by_cases hμ : μ q = 0
    · simpa [hμ] using dyadic_zero
    apply dyadic_of_odd_padicVal_nonneg _ (div_nonneg (hμn q) (Nat.cast_nonneg _))
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.div hμ (hwn q)]
    apply sub_nonneg.mpr
    exact (hmin q p hp hp2).2 _ (hμmem q (lt_of_le_of_ne (hμn q) (Ne.symm hμ)))
  · by_cases hP : P q r = 0
    · simpa [hP] using dyadic_zero
    apply dyadic_of_odd_padicVal_nonneg _
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPn q r)) (Nat.cast_nonneg _))
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha, hva⟩ := (hmin q p hp hp2).1
    have hnext := (hmin r p hp hp2).2 _
      (hclosed q r a ha (lt_of_le_of_ne (hPn q r) (Ne.symm hP)))
    rw [padicValRat.mul (ne_of_gt (hpos q a ha)) hP, hva] at hnext
    rw [padicValRat.div (mul_ne_zero (hwn q) hP) (hwn r), padicValRat.mul (hwn q) hP]
    exact sub_nonneg.mpr hnext

end FSS23105365

-- From Solutions.FSS23105365_DyadicRealization
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- A finite family of nonnegative dyadic numbers has a common power-of-two
denominator. The exponent can be chosen positive, as required in Lemma E.3. -/
theorem dyadic_common_denominator {α : Type} [Fintype α] (p : α → ℝ)
    (hp : ∀ x, Dyadic (p x)) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : α → ℕ, ∀ x, p x = (a x : ℝ) / 2 ^ k := by
  classical
  choose a e he using hp
  let k := (∑ x, e x) + 1
  have hek (x : α) : e x ≤ k := by
    exact le_trans (Finset.single_le_sum (fun y _ => Nat.zero_le (e y))
      (Finset.mem_univ x)) (Nat.le_succ _)
  refine ⟨k, Nat.zero_lt_succ _, fun x => a x * 2 ^ (k - e x), ?_⟩
  intro x
  rw [he x, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ k = 2 ^ (e x) * 2 ^ (k - e x) := by
    rw [← pow_add, Nat.add_sub_of_le (hek x)]
  rw [hpow]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).symm

/-- Allocate a finite uniform source to prescribed integer multiplicities. -/
theorem exists_map_with_fiber_counts {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (a : α → ℕ) (ha : ∑ x, a x = Fintype.card β) :
    ∃ f : β → α, ∀ x, Fintype.card {u : β // f u = x} = a x := by
  classical
  let e : β ≃ (Σ x, Fin (a x)) := Fintype.equivOfCardEq (by simp [ha])
  refine ⟨fun u => (e u).1, fun x => ?_⟩
  let ef : {u : β // (e u).1 = x} ≃ {u : (Σ y, Fin (a y)) // u.1 = x} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  let ep : {u : (Σ y, Fin (a y)) // u.1 = x} ≃ Fin (a x) :=
    Equiv.sigmaSubtype x
  simpa using Fintype.card_congr (ef.trans ep)

/-- A normalized distribution with the specified dyadic denominator can use
exactly that many fair bits, so all Markov rows can share a block length. -/
theorem distribution_realization_of_counts {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (k : ℕ) (a : α → ℕ)
    (ha : ∀ x, p x = (a x : ℝ) / 2 ^ k) (hsum : ∑ x, p x = 1) :
    ∃ f : Bits k → α,
      ∀ x, (Fintype.card {u : Bits k // f u = x} : ℝ) / 2 ^ k = p x := by
  classical
  have hcounts : ∑ x, a x = 2 ^ k := by
    have h : (∑ x, (a x : ℝ)) / 2 ^ k = 1 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      simpa only [div_eq_mul_inv, ← Finset.sum_mul] using
        (show (∑ x, (a x : ℝ) / 2 ^ k) = 1 by simpa only [← ha] using hsum)
    have h' : (∑ x, (a x : ℝ)) = (2 : ℝ) ^ k :=
      (div_eq_one_iff_eq (pow_ne_zero _ (by norm_num))).mp h
    exact_mod_cast h'
  obtain ⟨f, hf⟩ := exists_map_with_fiber_counts (β := Bits k) a (by
    simpa only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hcounts)
  exact ⟨f, fun x => by rw [hf, ha]⟩

/-- The normalized dyadic case of the finite sampling construction used in
Lemma E.3: a fixed finite fair-bit seed realizes the distribution exactly. -/
theorem dyadic_distribution_realization {α : Type} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ x, Dyadic (p x)) (hsum : ∑ x, p x = 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : Bits k → α,
      ∀ x, (Fintype.card {u : Bits k // f u = x} : ℝ) / 2 ^ k = p x := by
  obtain ⟨k, hk, a, ha⟩ := dyadic_common_denominator p hp
  exact ⟨k, hk, distribution_realization_of_counts p k a ha hsum⟩

/-- Initial and transition maps in the first paragraph of Lemma E.3. All
transition rows use the same positive block length; no probability oracle
is assumed. -/
theorem transitionDyadic_block_maps {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ g : Bits v → Fin q, ∃ δ : Fin q → Bits s → Fin q,
        (∀ x, (Fintype.card {e : Bits v // g e = x} : ℝ) / 2 ^ v = M.initial x) ∧
        (∀ x y, (Fintype.card {u : Bits s // δ x u = y} : ℝ) / 2 ^ s =
          M.transition x y) := by
  obtain ⟨v, hv, g, hg⟩ := dyadic_distribution_realization M.initial hM.1 M.initial_sum
  obtain ⟨s, hs, a, ha⟩ := dyadic_common_denominator
    (fun xy : Fin q × Fin q => M.transition xy.1 xy.2) (fun xy => hM.2 xy.1 xy.2)
  have hrows (x : Fin q) := distribution_realization_of_counts
    (M.transition x) s (fun y => a (x, y)) (fun y => ha (x, y)) (M.row_sum x)
  choose δ hδ using hrows
  exact ⟨v, s, hv, hs, g, δ, hg, hδ⟩

end FSS23105365

-- From Solutions.FSS23105365_IntegerMargins
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Fibers partition the finite source set. -/
theorem sum_fiber_card {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : (∑ y, Fintype.card {x : α // f x = y}) = Fintype.card α := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- The integer-matrix construction in E.4: if the total column demand is
`card α * m`, it can be allocated into rows of exactly `m` units each. -/
theorem exists_integer_matrix_with_margins {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (m : ℕ) (b : β → ℕ)
    (hb : ∑ y, b y = Fintype.card α * m) :
    ∃ C : α → β → ℕ,
      (∀ x, ∑ y, C x y = m) ∧ (∀ y, ∑ x, C x y = b y) := by
  classical
  obtain ⟨f, hf⟩ := exists_map_with_fiber_counts (β := α × Fin m) b (by simpa using hb)
  let C : α → β → ℕ := fun x y => Fintype.card {j : Fin m // f (x, j) = y}
  refine ⟨C, fun x => ?_, fun y => ?_⟩
  · simpa [C] using sum_fiber_card (fun j : Fin m => f (x, j))
  · have h := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x (j : Fin m) => f (x, j) = y))
    simpa only [Fintype.card_sigma, hf, C] using h.symm

end FSS23105365

-- From Solutions.FSS23105365_DyadicLiftKernel
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

abbrev StateCopies {q : ℕ} (w : Fin q → ℕ) := (x : Fin q) × Fin (w x)

/-- Given the weights obtained in the first half of E.4, construct the
dyadic transition kernel with exactly the row and column margins used by
the fiber invariant. Existence of those weights remains a separate target. -/
theorem exists_dyadic_lift_kernel {q : ℕ} (M : MarkovChain q) (w : Fin q → ℕ)
    (hw : ∀ x, 0 < w x)
    (hd : ∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) :
    ∃ T : StateCopies w → StateCopies w → ℝ,
      (∀ h h', Dyadic (T h h')) ∧
      (∀ h h', 0 ≤ T h h') ∧
      (∀ h, ∑ h', T h h' = 1) ∧
      (∀ x (h' : StateCopies w), ∑ i : Fin (w x), T ⟨x, i⟩ h' =
        (w x : ℝ) * M.transition x h'.1 / (w h'.1 : ℝ)) := by
  classical
  obtain ⟨k, hk, a, ha⟩ := dyadic_common_denominator
    (fun xy : Fin q × Fin q => (w xy.1 : ℝ) * M.transition xy.1 xy.2 / (w xy.2 : ℝ))
    (fun xy => hd xy.1 xy.2)
  have hden : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hwn (x : Fin q) : (w x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw x))
  have ha' (x y : Fin q) : (a (x, y) : ℝ) =
      ((w x : ℝ) * M.transition x y / (w y : ℝ)) * 2 ^ k :=
    ((eq_div_iff hden).mp (ha (x, y))).symm
  have htot (x : Fin q) : (∑ h' : StateCopies w, a (x, h'.1)) = w x * 2 ^ k := by
    have hr : (∑ h' : StateCopies w, (a (x, h'.1) : ℝ)) = (w x : ℝ) * 2 ^ k := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (∑ y, (w y : ℝ) * (a (x, y) : ℝ)) =
            ((w x : ℝ) * 2 ^ k) * ∑ y, M.transition x y := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [ha']
          field_simp [hwn]
        _ = (w x : ℝ) * 2 ^ k := by rw [M.row_sum, mul_one]
    exact_mod_cast hr
  have hmat (x : Fin q) := exists_integer_matrix_with_margins
    (α := Fin (w x)) (β := StateCopies w) (2 ^ k) (fun h' => a (x, h'.1))
      (by simpa using htot x)
  choose C hrow hcol using hmat
  let T : StateCopies w → StateCopies w → ℝ :=
    fun h h' => (C h.1 h.2 h' : ℝ) / 2 ^ k
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro h h'; exact ⟨C h.1 h.2 h', k, rfl⟩
  · intro h h'; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) _))
  · intro h
    change (∑ h', (C h.1 h.2 h' : ℝ) / 2 ^ k) = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hrow]
    simp [hden]
  · intro x h'
    change (∑ i : Fin (w x), (C x i h' : ℝ) / 2 ^ k) = _
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hcol]
    exact (ha (x, h'.1)).symm

end FSS23105365

-- From Solutions.FSS23105365_DyadicLiftFromWeights
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The second half of E.4, starting from its explicit integer weights.
All finite-chain normalization and the full projected path law are proved;
the existence of the weights is deliberately not assumed to be E.4 itself. -/
theorem dyadic_lift_from_weights {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (w : Fin q → ℕ) (hw : ∀ x, 0 < w x)
    (hinit : ∀ x, Dyadic (M.initial x / (w x : ℝ)))
    (htrans : ∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  classical
  obtain ⟨T, hTd, hTn, hTr, hTc⟩ := exists_dyadic_lift_kernel M w hw htrans
  let H := StateCopies w
  let μ : H → ℝ := fun h => M.initial h.1 / (w h.1 : ℝ)
  have hwn (x : Fin q) : (w x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw x))
  have hμn (h : H) : 0 ≤ μ h :=
    div_nonneg (M.initial_nonneg h.1) (Nat.cast_nonneg _)
  have hμs : ∑ h : H, μ h = 1 := by
    change (∑ h : StateCopies w, M.initial h.1 / (w h.1 : ℝ)) = 1
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    convert M.initial_sum using 1
    apply Finset.sum_congr rfl
    intro x _
    field_simp [hwn]
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let N : MarkovChain (Fintype.card H) :=
    { initial := fun h => μ (e.symm h)
      transition := fun h h' => T (e.symm h) (e.symm h')
      initial_nonneg := fun h => hμn (e.symm h)
      transition_nonneg := fun h h' => hTn (e.symm h) (e.symm h')
      initial_sum := by rw [e.symm.sum_comp]; exact hμs
      row_sum := fun h => by rw [e.symm.sum_comp]; exact hTr (e.symm h) }
  let φ : Fin (Fintype.card H) → Fin q := fun h => (e.symm h).1
  have hr : 0 < Fintype.card H := Fintype.card_pos_iff.mpr
    ⟨⟨⟨0, hq⟩, ⟨0, hw ⟨0, hq⟩⟩⟩⟩
  refine ⟨Fintype.card H, hr, N, φ, ⟨fun h => hinit (e.symm h).1,
    fun h h' => hTd (e.symm h) (e.symm h')⟩, fun n γ => ?_⟩
  have hcols (x : Fin q) (h : H) :
      (∑ a : H, if a.1 = x then T a h else 0) =
        (w x : ℝ) * M.transition x h.1 / (w h.1 : ℝ) := by
    change (∑ a : StateCopies w, if a.1 = x then T a h else 0) = _
    rw [Fintype.sum_sigma, Finset.sum_eq_single x]
    · simpa using hTc x h
    · intro y _ hy; simp [hy]
    · simp
  have hcard (x : Fin q) : (Fintype.card {h : H // h.1 = x} : ℝ) = (w x : ℝ) := by
    exact_mod_cast (show Fintype.card {h : H // h.1 = x} = w x from by
      simpa only [Fintype.card_fin] using Fintype.card_congr
        (Equiv.sigmaSubtype (β := fun y : Fin q => Fin (w y)) x))
  let ep : (Fin (n + 1) → H) ≃ Path (Fintype.card H) n :=
    Equiv.arrowCongr (Equiv.refl _) e
  rw [projectedPathLaw, ← ep.sum_comp]
  calc
    (∑ η : Fin (n + 1) → H,
      if (fun i => φ (ep η i)) = γ then pathLaw N (ep η) else 0) =
        ∑ η : Fin (n + 1) → H,
          if (fun i => (η i).1) = γ then finitePathWeight μ T η else 0 := by
      apply Finset.sum_congr rfl
      intro η _
      simp [ep, φ, N, Equiv.arrowCongr, Function.comp_def, pathLaw, finitePathWeight]
      rfl
    _ = pathLaw M γ := by
      rw [pathLaw_eq_finitePathWeight]
      exact projected_finitePathWeight_eq μ T (fun h : H => h.1)
        M.initial M.transition (fun x => (w x : ℝ)) hwn (fun _ => rfl) hcols hcard γ

end FSS23105365

-- From Solutions.FSS23105365_DyadicReachableWeights
set_option autoImplicit false
namespace FSS23105365

/-- The integer weights in E.4 exist after unreachable states have been
removed. Positive path probabilities are used exactly as in the paper. -/
theorem pathDyadic_weights_of_reachable {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (hreach : ∀ x, PositivelyReachable M x) :
    ∃ w : Fin q → ℕ, (∀ x, 0 < w x) ∧
      (∀ x, Dyadic (M.initial x / (w x : ℝ))) ∧
      (∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) := by
  classical
  choose μ hμ using fun x => dyadic_is_rational (pathDyadic_initial_dyadic M hM x)
  choose P hP using fun x y => pathDyadic_transition_rational M hM x y (hreach x)
  let S : Fin q → Set ℚ := fun x =>
    {a | ∃ n : ℕ, ∃ γ : Path q n,
      γ (Fin.last n) = x ∧ 0 < pathLaw M γ ∧ (a : ℝ) = pathLaw M γ}
  have hne (x : Fin q) : (S x).Nonempty := by
    obtain ⟨n, γ, hlast, hpos⟩ := hreach x
    obtain ⟨a, ha⟩ := dyadic_is_rational (hM n γ)
    exact ⟨a, n, γ, hlast, hpos, ha⟩
  have hpos (x : Fin q) (a : ℚ) (ha : a ∈ S x) : 0 < a := by
    obtain ⟨n, γ, _, hp, heq⟩ := ha
    have : (0 : ℝ) < (a : ℝ) := by rw [heq]; exact hp
    exact_mod_cast this
  have hd (x : Fin q) (a : ℚ) (ha : a ∈ S x) : Dyadic (a : ℝ) := by
    obtain ⟨n, γ, _, _, heq⟩ := ha
    rw [heq]
    exact hM n γ
  have hμn (x : Fin q) : 0 ≤ μ x := by
    have : (0 : ℝ) ≤ (μ x : ℝ) := by rw [hμ]; exact M.initial_nonneg x
    exact_mod_cast this
  have hPn (x y : Fin q) : 0 ≤ P x y := by
    have : (0 : ℝ) ≤ (P x y : ℝ) := by rw [hP]; exact M.transition_nonneg x y
    exact_mod_cast this
  have hμmem (x : Fin q) (hx : 0 < μ x) : μ x ∈ S x := by
    refine ⟨0, fun _ => x, rfl, ?_, ?_⟩
    · have : (0 : ℝ) < (μ x : ℝ) := by exact_mod_cast hx
      simpa [pathLaw, hμ] using this
    · simpa [pathLaw] using hμ x
  have hclosed (x y : Fin q) (a : ℚ) (ha : a ∈ S x) (hxy : 0 < P x y) :
      a * P x y ∈ S y := by
    obtain ⟨n, γ, hlast, hγ, heq⟩ := ha
    have hPpos : 0 < M.transition x y := by
      rw [← hP]
      exact_mod_cast hxy
    have hnext : pathLaw M (Fin.snoc γ y) = pathLaw M γ * M.transition x y := by
      rw [pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
        ← pathLaw_eq_finitePathWeight]
    refine ⟨n + 1, Fin.snoc γ y, Fin.snoc_last _ _, ?_, ?_⟩
    · rw [hnext]; exact mul_pos hγ hPpos
    · rw [Rat.cast_mul, heq, hP, hnext]
  obtain ⟨w, hw, hwi, hwt⟩ := exists_weights_of_dyadic_path_sets S hne hpos hd
    μ P hμn hPn hμmem hclosed
  refine ⟨w, hw, fun x => ?_, fun x y => ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_natCast, hμ] using hwi x
  · simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, hP] using hwt x y

/-- E.4 for a chain all of whose states are positively reachable. -/
theorem dyadic_lift_of_all_reachable {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) (hreach : ∀ x, PositivelyReachable M x) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  obtain ⟨w, hw, hi, ht⟩ := pathDyadic_weights_of_reachable M hM hreach
  exact dyadic_lift_from_weights hq M w hw hi ht

end FSS23105365

-- From Solutions.FSS23105365_PathReachability
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem pathLaw_nonneg {q n : ℕ} (M : MarkovChain q) (γ : Path q n) :
    0 ≤ pathLaw M γ := by
  apply mul_nonneg (M.initial_nonneg _)
  exact Finset.prod_nonneg (fun _ _ => M.transition_nonneg _ _)

theorem positive_path_states_reachable {q n : ℕ} (M : MarkovChain q)
    (γ : Path q n) (hγ : 0 < pathLaw M γ) (i : Fin (n + 1)) :
    PositivelyReachable M (γ i) := by
  induction n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    apply positivelyReachable_of_initial
    simpa [pathLaw] using hγ
  | succ n ih =>
    rcases (Fin.snocEquiv (fun _ : Fin (n + 2) => Fin q)).surjective γ with ⟨⟨x, η⟩, rfl⟩
    have heval : (Fin.snocEquiv (fun _ : Fin (n + 2) => Fin q)) (x, η) =
        Fin.snoc η x := rfl
    rw [heval] at hγ ⊢
    have hprod : 0 < pathLaw M η * M.transition (η (Fin.last n)) x := by
      simpa only [pathLaw_eq_finitePathWeight, finitePathWeight_snoc] using hγ
    have hη : 0 < pathLaw M η := by
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact (not_lt_of_ge (pathLaw_nonneg M η) h.1).elim
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨n + 1, Fin.snoc η x, rfl, hγ⟩
    · simpa using ih η hη j

theorem initial_zero_of_not_reachable {q : ℕ} (M : MarkovChain q) (x : Fin q)
    (hx : ¬ PositivelyReachable M x) : M.initial x = 0 := by
  apply le_antisymm _ (M.initial_nonneg x)
  exact le_of_not_gt (fun h => hx (positivelyReachable_of_initial M x h))

theorem transition_zero_to_unreachable {q : ℕ} (M : MarkovChain q) (x y : Fin q)
    (hx : PositivelyReachable M x) (hy : ¬ PositivelyReachable M y) :
    M.transition x y = 0 := by
  apply le_antisymm _ (M.transition_nonneg x y)
  exact le_of_not_gt (fun h => hy (positivelyReachable_step M x y hx h))

theorem exists_positivelyReachable {q : ℕ} (M : MarkovChain q) :
    ∃ x, PositivelyReachable M x := by
  by_contra h
  push Not at h
  have hz : ∑ x, M.initial x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact initial_zero_of_not_reachable M x (h x)
  rw [M.initial_sum] at hz
  exact one_ne_zero hz

end FSS23105365

-- From Solutions.FSS23105365_ReachableRestriction
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem sum_subtype_of_zero_outside {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (hf : ∀ x, ¬ p x → f x = 0) :
    (∑ x : {x // p x}, f x) = ∑ x, f x := by
  have hz : (∑ x : {x // ¬ p x}, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hf x x.property
  simpa only [hz, add_zero] using Fintype.sum_subtype_add_sum_subtype p f

theorem pathLaw_of_state_embedding {q r n : ℕ} (M : MarkovChain q) (N : MarkovChain r)
    (ψ : Fin r → Fin q)
    (hi : ∀ x, N.initial x = M.initial (ψ x))
    (ht : ∀ x y, N.transition x y = M.transition (ψ x) (ψ y)) (η : Path r n) :
    pathLaw N η = pathLaw M (fun i => ψ (η i)) := by
  simp only [pathLaw, hi, ht]

/-- An injective state restriction preserves the whole path law when it
contains every state on each positive-probability path. -/
theorem projectedPathLaw_of_state_embedding {q r : ℕ} (M : MarkovChain q) (N : MarkovChain r)
    (ψ : Fin r → Fin q) (hψ : Function.Injective ψ)
    (hi : ∀ x, N.initial x = M.initial (ψ x))
    (ht : ∀ x y, N.transition x y = M.transition (ψ x) (ψ y))
    (hs : ∀ n (γ : Path q n), 0 < pathLaw M γ → ∀ i, ∃ x, ψ x = γ i)
    (n : ℕ) (γ : Path q n) : projectedPathLaw N ψ γ = pathLaw M γ := by
  classical
  by_cases hex : ∃ η : Path r n, (fun i => ψ (η i)) = γ
  · obtain ⟨η, hη⟩ := hex
    rw [projectedPathLaw, Finset.sum_eq_single η]
    · rw [if_pos hη, pathLaw_of_state_embedding M N ψ hi ht, hη]
    · intro η' _ hne
      apply if_neg
      intro heq
      apply hne
      funext i
      apply hψ
      exact (congrFun heq i).trans (congrFun hη i).symm
    · simp
  · have hz : pathLaw M γ = 0 := by
      apply le_antisymm _ (pathLaw_nonneg M γ)
      apply le_of_not_gt
      intro hpos
      choose η hη using hs n γ hpos
      exact hex ⟨η, funext hη⟩
    rw [hz, projectedPathLaw]
    apply Finset.sum_eq_zero
    intro η _
    exact if_neg (fun h => hex ⟨η, h⟩)

/-- Delete precisely the states unreachable from the initial support.
The finite restricted chain is normalized, all its states are reachable,
and its coordinatewise projection has the original full trajectory law. -/
theorem exists_reachable_restriction {q : ℕ} (M : MarkovChain q) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ ψ : Fin r → Fin q,
      (∀ x, PositivelyReachable N x) ∧
      (∀ n (η : Path r n), pathLaw N η = pathLaw M (fun i => ψ (η i))) ∧
      (∀ n (γ : Path q n), projectedPathLaw N ψ γ = pathLaw M γ) := by
  classical
  let H := {x : Fin q // PositivelyReachable M x}
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let ψ : Fin (Fintype.card H) → Fin q := fun x => (e.symm x).val
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hμ : (∑ x : H, M.initial x.val) = 1 := by
    rw [sum_subtype_of_zero_outside (PositivelyReachable M) M.initial
      (initial_zero_of_not_reachable M), M.initial_sum]
  have hP (x : H) : (∑ y : H, M.transition x.val y.val) = 1 := by
    rw [sum_subtype_of_zero_outside (PositivelyReachable M) (M.transition x.val)
      (fun y hy => transition_zero_to_unreachable M x.val y x.property hy), M.row_sum]
  let N : MarkovChain (Fintype.card H) :=
    { initial := fun x => M.initial (ψ x)
      transition := fun x y => M.transition (ψ x) (ψ y)
      initial_nonneg := fun x => M.initial_nonneg (ψ x)
      transition_nonneg := fun x y => M.transition_nonneg (ψ x) (ψ y)
      initial_sum := by
        change (∑ x, M.initial (e.symm x).val) = 1
        exact (e.symm.sum_comp (fun x : H => M.initial x.val)).trans hμ
      row_sum := fun x => by
        change (∑ y, M.transition (ψ x) (e.symm y).val) = 1
        exact (e.symm.sum_comp (fun y : H => M.transition (ψ x) y.val)).trans
          (hP (e.symm x)) }
  have hr : 0 < Fintype.card H := by
    obtain ⟨x, hx⟩ := exists_positivelyReachable M
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  have hmap (n : ℕ) (η : Path (Fintype.card H) n) :
      pathLaw N η = pathLaw M (fun i => ψ (η i)) :=
    pathLaw_of_state_embedding M N ψ (fun _ => rfl) (fun _ _ => rfl) η
  have hlift (n : ℕ) (γ : Path q n) (hp : 0 < pathLaw M γ) :
      ∃ η : Path (Fintype.card H) n, (fun i => ψ (η i)) = γ := by
    refine ⟨fun i => e ⟨γ i, positive_path_states_reachable M γ hp i⟩, ?_⟩
    funext i
    simp [ψ]
  refine ⟨Fintype.card H, hr, N, ψ, ?_, hmap, ?_⟩
  · intro x
    obtain ⟨n, γ, hlast, hp⟩ := (e.symm x).property
    obtain ⟨η, hη⟩ := hlift n γ hp
    refine ⟨n, η, ?_, ?_⟩
    · apply hψ
      exact (congrFun hη (Fin.last n)).trans hlast
    · rw [hmap, hη]; exact hp
  · exact projectedPathLaw_of_state_embedding M N ψ hψ (fun _ => rfl) (fun _ _ => rfl)
      (fun n γ hp i => by
        obtain ⟨η, hη⟩ := hlift n γ hp
        exact ⟨η i, congrFun hη i⟩)

end FSS23105365

-- From Solutions.FSS23105365_PathProjection
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Finite pushforward sums compose without assumptions on the weights. -/
theorem finite_pushforward_comp {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (z : γ) :
    (∑ y, if g y = z then ∑ x, if f x = y then p x else 0 else 0) =
      ∑ x, if g (f x) = z then p x else 0 := by
  classical
  calc
    _ = ∑ y, ∑ x, if f x = y then (if g y = z then p x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z <;> simp [hy]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp

theorem projectedPathLaw_comp {q r s n : ℕ} (M : MarkovChain s)
    (φ : Fin s → Fin r) (ψ : Fin r → Fin q) (γ : Path q n) :
    projectedPathLaw M (fun h => ψ (φ h)) γ =
      ∑ η : Path r n, if (fun i => ψ (η i)) = γ then projectedPathLaw M φ η else 0 := by
  exact (finite_pushforward_comp (fun ξ : Path s n => fun i => φ (ξ i))
    (fun η : Path r n => fun i => ψ (η i)) (pathLaw M) γ).symm

end FSS23105365

-- From Solutions.FSS23105365_DyadicLift
set_option autoImplicit false
namespace FSS23105365

/-- Full Lemma E.4 of Zenodo 23105365, with the exact type of the existing
`dyadic_lift` target. No reachability or weight hypothesis is added. -/
theorem dyadic_lift_proved (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  classical
  obtain ⟨r, hr, N, ψ, hreach, hmap, hproj⟩ := exists_reachable_restriction M
  have hN : PathDyadic N := by
    intro n η
    rw [hmap]
    exact hM n (fun i => ψ (η i))
  obtain ⟨s, hs, L, φ, hL, hLN⟩ := dyadic_lift_of_all_reachable hr N hN hreach
  refine ⟨s, hs, L, fun h => ψ (φ h), hL, fun n γ => ?_⟩
  rw [projectedPathLaw_comp]
  simp_rw [hLN]
  exact hproj n γ

end FSS23105365

end

open FSS23105365

theorem solution (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := FSS23105365.dyadic_lift_proved q hq M hM
