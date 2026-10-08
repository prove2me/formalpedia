-- Prove2me | solution 1 for ErschlerZheng.green_orbitKernel_muBeta_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T10:10:12.532635+00:00
-- url     : https://prove2.me/submissions/15ef26a3-e389-49df-9d1a-b2d46d2638ef

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_orbitKernel_muBeta_le_and_tail_le
import Theorems.Thm_ErschlerZheng_heatKernel_le_of_onDiagonal_of_tail
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Theorems.Thm_ErschlerZheng_stepProb_orbitKernel_muBeta_le
import Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- A substochastic kernel. -/
def IsSub (p : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, ∑' y, p x y ≤ 1

lemma isSub_of_isTransition {p : X → X → ℝ} (h : IsTransition p) : IsSub p :=
  ⟨h.1, h.2.1, fun x => (h.2.2 x).le⟩

lemma IsSub.le_one {p : X → X → ℝ} (h : IsSub p) (x y : X) : p x y ≤ 1 :=
  le_trans ((h.2.1 x).le_tsum y fun z _ => h.1 x z) (h.2.2 x)

/-- Fubini for `a(w) q(w, z) r(z)`, `a ≥ 0` summable, `q` substochastic, `0 ≤ r ≤ 1`. -/
lemma summable_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    Summable (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq.1 _ _)) (hr0 _)
  have hrow : ∀ w, Summable (fun z => a w * q w z * r z) := fun w =>
    Summable.of_nonneg_of_le (fun z => h0 (w, z))
      (fun z => by
        have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
        simpa using this)
      ((hq.2.1 w).mul_left (a w))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun w => tsum_nonneg fun z => h0 (w, z)) (fun w => ?_) has
  calc ∑' z, a w * q w z * r z ≤ ∑' z, a w * q w z :=
        Summable.tsum_le_tsum (fun z => by
          have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
          simpa using this) (hrow w) ((hq.2.1 w).mul_left (a w))
    _ = a w * ∑' z, q w z := tsum_mul_left
    _ ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
    _ = a w := mul_one _

/-- Exchange of the order of summation for `a(w) q(w, z) r(z)`. -/
lemma tsum_comm_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    ∑' w, a w * ∑' z, q w z * r z = ∑' z, (∑' w, a w * q w z) * r z := by
  have hs := summable_triple ha0 has hq hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun w z => a w * q w z * r z) hs
  have hcol : ∀ z, Summable (fun w => a w * q w z * r z) :=
    fun z => hs.prod_symm.prod_factor z
  calc ∑' w, a w * ∑' z, q w z * r z = ∑' w, ∑' z, a w * q w z * r z := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun z => by ring
    _ = ∑' z, ∑' w, a w * q w z * r z := hcomm.symm
    _ = ∑' z, (∑' w, a w * q w z) * r z := by
        refine tsum_congr fun z => ?_
        rw [← tsum_mul_right]

/-- The weighted column sums `z ↦ ∑_w a(w) q(w, z)` are summable with total `≤ ∑ a`. -/
lemma summable_col {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) :
    Summable (fun z => ∑' w, a w * q w z) ∧ (∀ z, Summable (fun w => a w * q w z)) ∧
      ∑' z, ∑' w, a w * q w z ≤ ∑' w, a w := by
  have hs := summable_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one] at hs
  refine ⟨?_, fun z => ?_, ?_⟩
  · have := hs.prod_symm.prod
    simpa using this
  · have := hs.prod_symm.prod_factor z
    simpa using this
  · have h := tsum_comm_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [← h]
    refine Summable.tsum_le_tsum (fun w => ?_) ?_ has
    · calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _
    · refine Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (tsum_nonneg (hq.1 w)))
        (fun w => ?_) has
      calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _

variable [DecidableEq X]

lemma stepProb_zero (p : X → X → ℝ) (x y : X) :
    stepProb p 0 x y = if x = y then 1 else 0 := rfl

lemma isSub_stepProb {p : X → X → ℝ} (hp : IsSub p) : ∀ n, IsSub (stepProb p n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun x y => by simp only [stepProb_zero]; split_ifs <;> norm_num, fun x => ?_,
      fun x => ?_⟩
    · exact (hasSum_ite_eq x (1 : ℝ)).summable.congr fun y => by
        simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    · have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
        funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
      rw [this, tsum_ite_eq]
  | succ n ih =>
    refine ⟨fun x y => tsum_nonneg fun z => mul_nonneg (hp.1 x z) (ih.1 z y), fun x => ?_,
      fun x => ?_⟩
    · exact (summable_col (hp.1 x) (hp.2.1 x) ih).1
    · exact le_trans (summable_col (hp.1 x) (hp.2.1 x) ih).2.2 (hp.2.2 x)

lemma stepProb_nonneg {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    0 ≤ stepProb p n x y := (isSub_stepProb hp n).1 x y

lemma stepProb_le_one {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p n x y ≤ 1 := (isSub_stepProb hp n).le_one x y

/-! ## The heat kernel -/

lemma uniformize_eq_self {J : X → X → ℝ} (hJ : IsTransition J) : uniformize J = J := by
  funext a b; simp [uniformize, hJ.2.2 a]

/-- The Poisson weights. -/
noncomputable def poi (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t ^ n / n.factorial

lemma poi_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poi t n := by
  unfold poi; positivity

lemma hasSum_poi (t : ℝ) : HasSum (poi t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp t
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-t))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have e : poi t = fun i => Real.exp (-t) * (t ^ i / ↑i.factorial) := by
    funext n; unfold poi; ring
  rw [e]; exact h2

lemma summable_poi (t : ℝ) : Summable (poi t) := (hasSum_poi t).summable

lemma tsum_poi (t : ℝ) : ∑' n, poi t n = 1 := (hasSum_poi t).tsum_eq

lemma heatKernel_eq {J : X → X → ℝ} (t : ℝ) (x y : X) :
    heatKernel J t x y = ∑' n, poi t n * stepProb (uniformize J) n x y := rfl

lemma summable_heat {p : X → X → ℝ} (hp : IsSub p) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    Summable (fun n => poi t n * stepProb p n x y) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poi_nonneg ht n) (stepProb_nonneg hp n x y))
    (fun n => by
      have := mul_le_mul_of_nonneg_left (stepProb_le_one hp n x y) (poi_nonneg ht n)
      simpa using this)
    (summable_poi t)

end MarkovHK
end

section
/-!
# Near and far parts of a kernel; `uniformize` of a substochastic kernel (shared by H6 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

end MarkovHK
end

section
/-!
# Orbit kernels of `μ_β` and `υ_n` as Markov kernels (helpers for Proposition 7.19, prover 6)

* `G_ω` and the orbit `1^∞·G_ω` are countable.
* For `ν ⩾ 0` summable on a subgroup `K`, the rows of `P_ν` sum to `Σ ν`; `P_ν` is a transition
  kernel when `ν` is a probability, and symmetric when `ν` is.
* `υ_n` restricted to `G_ω` is a sub-probability, so `P_{(υ_n + υ̌_n)/2}` is substochastic.
* `μ_β ⩾ C_β 2^{-nβ} (υ_n + υ̌_n)/2` pointwise, for `n ⩾ 1`, `D ∣ n`.
* `μ_β` is symmetric; `k_n = A⌊log₂ n⌋` is admissible and eventually `⩽ n` (copied from prover 5's
  `P5Goal`, which is still being edited).
-/

open scoped RightActions
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

open GrigBasic Garrido Filter

set_option linter.unusedSectionVars false

/-! ### Countability -/

lemma gens_finite (ω : ℕ → Fin 3) : (gens ω).Finite := by
  unfold gens
  exact (((Set.finite_singleton _).insert _).insert _).insert _

instance countable_grigorchuk (ω : ℕ → Fin 3) : Countable (grigorchuk ω) := by
  have hT : (gens ω ∪ (gens ω)⁻¹).Countable :=
    ((gens_finite ω).union (gens_finite ω).inv).countable
  have hc : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut).Countable := by
    have h1 : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut) =
        (Submonoid.closure (gens ω ∪ (gens ω)⁻¹) : Set BinaryTreeAut) := by
      unfold grigorchuk
      rw [← Subgroup.closure_toSubmonoid]
      rfl
    rw [h1, Submonoid.closure_eq_image_prod]
    have : Countable (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) := hT.to_subtype
    have h2 : {l : List BinaryTreeAut | ∀ x ∈ l, x ∈ gens ω ∪ (gens ω)⁻¹} ⊆
        Set.range (fun l : List (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) =>
          l.map Subtype.val) := by
      intro l hl
      refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
      simp [List.map_attach_eq_pmap]
    exact ((Set.countable_range _).mono h2).image _
  exact hc.to_subtype

instance countable_orbitOne (ω : ℕ → Fin 3) : Countable (orbitOne ω) := by
  have : (orbitOne ω).Countable := by
    have h : orbitOne ω ⊆ Set.range (fun g : grigorchuk ω => oneRay <• (g : BinaryTreeAut)) := by
      rintro y ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    exact (Set.countable_range _).mono h
  exact this.to_subtype

/-! ### Orbit kernels -/

section Orbit

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X] (K : Subgroup H)

lemma orbitKernel_nonneg' {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (o : X) (x y : rightOrbit K o) :
    0 ≤ orbitKernel K ν o x y := by
  classical
  unfold orbitKernel
  exact tsum_nonneg fun g => by split_ifs <;> simp [hν g]

/-- The rows of `P_ν` sum to `Σ ν`. -/
lemma hasSum_orbitKernel_row {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (hs : Summable ν) (o : X)
    (x : rightOrbit K o) : HasSum (fun y => orbitKernel K ν o x y) (∑' g, ν g) := by
  classical
  -- the point `x·g` of the orbit
  let act : K → rightOrbit K o := fun g => ⟨(x : X) <• (g : H), by
    obtain ⟨k, hk, hx⟩ := x.2
    refine ⟨k * g, K.mul_mem hk g.2, ?_⟩
    rw [hx, MulOpposite.op_mul, mul_smul]⟩
  let F : rightOrbit K o × K → ℝ := fun p => if (x : X) <• (p.2 : H) = p.1 then ν p.2 else 0
  have hinj : Function.Injective (fun g : K => (act g, g)) := fun a b h => (Prod.mk.inj h).2
  have hF : HasSum F (∑' g, ν g) := by
    have hcomp : F ∘ (fun g : K => (act g, g)) = ν := by
      funext g; simp [F, act]
    have hsupp : ∀ p ∉ Set.range (fun g : K => (act g, g)), F p = 0 := by
      rintro ⟨y, g⟩ hp
      simp only [F]
      split_ifs with h
      · exact absurd ⟨g, by
          simp only [Prod.mk.injEq, and_true]
          exact Subtype.ext h⟩ hp
      · rfl
    rw [← hinj.hasSum_iff hsupp, hcomp]
    exact hs.hasSum
  refine hF.prod_fiberwise fun y => ?_
  show HasSum (fun g : K => if (x : X) <• (g : H) = y then ν g else 0) (orbitKernel K ν o x y)
  unfold orbitKernel
  refine Summable.hasSum ?_
  refine Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hν g]) (fun g => ?_) hs
  split_ifs
  · exact le_rfl
  · exact hν g

lemma isTransition_orbitKernel {ν : K → ℝ} (hν : IsProbability ν) (o : X) :
    IsTransition (orbitKernel K ν o) := by
  refine ⟨fun x y => orbitKernel_nonneg' K hν.1 o x y, fun x => ?_, fun x => ?_⟩
  · exact (hasSum_orbitKernel_row K hν.1 hν.2.summable o x).summable
  · rw [(hasSum_orbitKernel_row K hν.1 hν.2.summable o x).tsum_eq, hν.2.tsum_eq]

lemma isSymmetric_orbitKernel {ν : K → ℝ} (hν : ∀ g, ν g⁻¹ = ν g) (o : X) :
    MarkovChain.IsSymmetric (orbitKernel K ν o) := by
  classical
  intro x y
  unfold orbitKernel
  rw [← (Equiv.inv K).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply, InvMemClass.coe_inv, hν]
  have hiff : ((x : X) <• (g : H)⁻¹ = y) ↔ ((y : X) <• (g : H) = x) := by
    constructor
    · intro h; rw [← h, ← mul_smul, ← MulOpposite.op_mul, inv_mul_cancel, MulOpposite.op_one,
        one_smul]
    · intro h; rw [← h, ← mul_smul, ← MulOpposite.op_mul, mul_inv_cancel, MulOpposite.op_one,
        one_smul]
  by_cases h : (y : X) <• (g : H) = x
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

end Orbit

/-! ### The measures `υ_n` on `G_ω` -/

/-! ### `μ_β` dominates its `n`-th component -/

/-! ### Symmetry of `μ_β` and the parameters (after prover 5's `P5Goal`) -/

lemma inv_mem_genSet {ω : ℕ → Fin 3} {g : grigorchuk ω} (hg : g ∈ genSet ω) :
    g⁻¹ ∈ genSet ω := by
  simp only [genSet, Set.mem_preimage, Subgroup.coe_inv] at hg ⊢
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  rcases hg with h | h | h | h <;> rw [h] <;> simp [grigA_inv, gen_inv]

lemma inv_mem_genSet_iff {ω : ℕ → Fin 3} {g : grigorchuk ω} : g⁻¹ ∈ genSet ω ↔ g ∈ genSet ω :=
  ⟨fun h => by simpa using inv_mem_genSet h, inv_mem_genSet⟩

lemma muBeta_inv (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (g : grigorchuk ω) :
    muBeta D ω k β g⁻¹ = muBeta D ω k β g := by
  classical
  unfold muBeta
  have hu : uniformMeasure (genSet ω) g⁻¹ = uniformMeasure (genSet ω) g := by
    by_cases h : g ∈ genSet ω
    · simp [uniformMeasure, h, inv_mem_genSet_iff]
    · simp [uniformMeasure, h, inv_mem_genSet_iff]
  rw [hu]
  congr 2
  refine tsum_congr fun n => ?_
  split_ifs
  · congr 1
    simp only [upsilonCheck, Subgroup.coe_inv, inv_inv]
    ring
  · rfl

lemma sq_le_two_pow (j : ℕ) (hj : 4 ≤ j) : j ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 2 * j + 1 ≤ j ^ 2 := by nlinarith
    calc (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
      _ ≤ j ^ 2 + j ^ 2 := by omega
      _ ≤ 2 ^ j + 2 ^ j := by omega
      _ = 2 ^ (j + 1) := by ring

lemma eventually_kLog_le (A : ℕ) : ∀ᶠ n : ℕ in atTop, kLog A n ≤ n := by
  refine (eventually_ge_atTop (2 ^ (2 * A + 4))).mono fun n hn => ?_
  set j := Nat.log 2 n with hj
  have hj4 : 2 * A + 4 ≤ j := by
    have := Nat.log_mono_right (b := 2) hn
    rwa [Nat.log_pow (by norm_num)] at this
  have h1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 (by
    have : 0 < 2 ^ (2 * A + 4) := by positivity
    omega)
  have h2 := sq_le_two_pow j (by omega)
  unfold kLog
  rw [← hj]
  nlinarith

lemma isAdmissibleSeq_kLog (D A : ℕ) (hD : 3 ≤ D) (hDA : D ∣ A) (hA : 0 < A) :
    IsAdmissibleSeq D (kLog A) := by
  refine ⟨fun m n hmn => Nat.mul_le_mul_left A (Nat.log_mono_right hmn), fun n hn hDn => ?_⟩
  have hnD : D ≤ n := Nat.le_of_dvd hn hDn
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  exact ⟨Nat.mul_pos hA hlog, Dvd.dvd.mul_right hDA _⟩

lemma three_le_of_satisfiesFr {D : ℕ} {ω : ℕ → Fin 3} (h : SatisfiesFr D ω) : 3 ≤ D := by
  obtain ⟨m, hm, -⟩ := h 0
  omega

end P6Dev

end ErschlerZheng
end

section
/-!
# The Green function as the time integral of the heat kernel (helpers for Proposition 7.11)

For a transition kernel `J`, `p(t, x, y) = Σ_n e^{-t} tⁿ/n! Jⁿ(x, y)` and `∫_0^∞ e^{-t} tⁿ/n! dt = 1`
(the Γ integral), so `G_J(x, y) = ∫_0^∞ p(t, x, y) dt` in `[0, ∞]` (Tonelli). With
`p(t) ⩽ C₀ t^{-1/β}` for `t > T` and `p(t) ⩽ K t` for `0 < t ⩽ T`:
`G ⩽ K T²/2 + C₀ β/(1-β) T^{1-1/β}` (`0 < β < 1`).
-/

open MeasureTheory Set DurrettProbability MarkovChain MarkovHK
open scoped ENNReal

namespace ErschlerZheng

namespace P6Dev

lemma lintegral_poi (n : ℕ) : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (poi t n) = 1 := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (((n : ℝ) + 1) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hG := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at hG
  have heq : EqOn (fun t => ENNReal.ofReal (poi t n))
      (fun t => ENNReal.ofReal (Real.exp (-t) * t ^ (((n : ℝ) + 1) - 1) / n.factorial))
      (Ioi 0) := by
    intro t ht
    simp only [poi, add_sub_cancel_right, Real.rpow_natCast]
  rw [setLIntegral_congr_fun measurableSet_Ioi heq, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, ← hG, div_self (by positivity), ENNReal.ofReal_one]
  · exact hint.div_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : (0 : ℝ) < t := ht
    positivity

variable {X : Type*} [DecidableEq X]

/-- `G_J(x, y) = ∫_0^∞ p(t, x, y) dt`. -/
lemma green_eq_lintegral {J : X → X → ℝ} (hJ : IsTransition J) (x y : X) :
    green J x y = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (heatKernel J t x y) := by
  have hsub := isSub_of_isTransition hJ
  have h1 : EqOn (fun t => ENNReal.ofReal (heatKernel J t x y))
      (fun t => ∑' n, ENNReal.ofReal (poi t n) * ENNReal.ofReal (stepProb J n x y)) (Ioi 0) := by
    intro t ht
    have ht : (0 : ℝ) ≤ t := le_of_lt ht
    simp only
    rw [heatKernel_eq, uniformize_eq_self hJ, ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (poi_nonneg ht n) (stepProb_nonneg hsub n x y))
      (summable_heat hsub ht x y)]
    exact tsum_congr fun n => ENNReal.ofReal_mul (poi_nonneg ht n)
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_tsum]
  · unfold green
    refine tsum_congr fun n => ?_
    rw [lintegral_mul_const _ (Measurable.ennreal_ofReal (by unfold poi; fun_prop)),
      lintegral_poi, one_mul]
  · intro n
    exact ((Measurable.ennreal_ofReal (by unfold poi; fun_prop)).mul_const _).aemeasurable

/-- `∫_0^∞ f ⩽ K T²/2 + C₀ β/(1-β) T^{1-1/β}` from `f ⩽ K t` on `(0, T]` and `f ⩽ C₀ t^{-1/β}`
beyond. -/
lemma lintegral_le_of_bounds (f : ℝ → ℝ≥0∞) {β C₀ K T : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hT : 0 < T) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (h1 : ∀ t, T < t → f t ≤ ENNReal.ofReal (C₀ * t ^ (-(1 / β))))
    (h2 : ∀ t, 0 < t → t ≤ T → f t ≤ ENNReal.ofReal (K * t)) :
    ∫⁻ t in Ioi (0 : ℝ), f t ≤
      ENNReal.ofReal (K * T ^ 2 / 2 + C₀ * (β / (1 - β)) * T ^ (1 - 1 / β)) := by
  have hb : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  refine (lintegral_union_le _ _ _).trans ?_
  have hβ' : 0 < β / (1 - β) := div_pos hβ0 (by linarith)
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add ?_ ?_
  · calc ∫⁻ t in Ioc 0 T, f t ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (K * t) :=
          setLIntegral_mono' measurableSet_Ioc fun t ht => h2 t ht.1 ht.2
      _ = ENNReal.ofReal (∫ t in Ioc 0 T, K * t) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (Continuous.integrableOn_Ioc (by fun_prop))
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            exact mul_nonneg hK ht.1.le
      _ = ENNReal.ofReal (K * T ^ 2 / 2) := by
          rw [← intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_const_mul,
            integral_id]
          congr 1; ring
  · have ha : -(1 / β) < -1 := by linarith
    calc ∫⁻ t in Ioi T, f t ≤ ∫⁻ t in Ioi T, ENNReal.ofReal (C₀ * t ^ (-(1 / β))) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht => h1 t ht
      _ = ENNReal.ofReal (∫ t in Ioi T, C₀ * t ^ (-(1 / β))) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (integrableOn_Ioi_rpow_of_lt ha hT).const_mul C₀
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have : 0 < t := hT.trans ht
            positivity
      _ = ENNReal.ofReal (C₀ * (β / (1 - β)) * T ^ (1 - 1 / β)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hT]
          congr 1
          have e : -(1 / β) + 1 = 1 - 1 / β := by ring
          rw [e]
          have hne : 1 - 1 / β ≠ 0 := by linarith
          have h1β : 1 - β ≠ 0 := by linarith
          have key : -(T ^ (1 - 1 / β)) / (1 - 1 / β) = β / (1 - β) * T ^ (1 - 1 / β) := by
            rw [div_eq_iff hne]
            have hβne : β ≠ 0 := hβ0.ne'
            field_simp
            ring
          rw [neg_div] at key ⊢
          rw [key]; ring

/-- `e^{-ct} ⩽ (s/c)^s t^{-s}`. -/
lemma exp_neg_le_rpow {c s t : ℝ} (hc : 0 < c) (hs : 0 < s) (ht : 0 < t) :
    Real.exp (-(c * t)) ≤ (s / c) ^ s / t ^ s := by
  have h1 : c * t / s ≤ Real.exp (c * t / s) := by
    have := Real.add_one_le_exp (c * t / s); linarith
  have h2 : (c * t / s) ^ s ≤ Real.exp (c * t) := by
    calc (c * t / s) ^ s ≤ Real.exp (c * t / s) ^ s := Real.rpow_le_rpow (by positivity) h1 hs.le
      _ = Real.exp (c * t) := by rw [← Real.exp_mul]; congr 1; field_simp
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  have e : t ^ s = (s / c) ^ s * (c * t / s) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  rw [e, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
  calc (s / c) ^ s * (c * t / s) ^ s ≤ (s / c) ^ s * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- A discrete-time on-diagonal bound `Pⁿ ⩽ C n^{-s}` (`n ⩾ 1`) gives the continuous-time one
`p(t) ⩽ C₀ t^{-s}` (`t > 0`): split the Poisson weights at `n = t/2`; below, `poi(t, n) ⩽
2^{t/2} e^{-t/2} poi(t/2, n)`, whose sum is `e^{-(1 - log 2) t/2}`. -/
lemma heat_le_of_stepProb_le {J : X → X → ℝ} (hJ : IsTransition J) {s C : ℝ} (hs : 0 < s)
    (hC : 0 ≤ C) (h : ∀ n : ℕ, 1 ≤ n → ∀ x y, stepProb J n x y ≤ C / (n : ℝ) ^ s) :
    ∀ t : ℝ, 0 < t → ∀ x y,
      heatKernel J t x y ≤ (s / ((1 - Real.log 2) / 2)) ^ s / t ^ s + C * 2 ^ s / t ^ s := by
  intro t ht x y
  have hsub := isSub_of_isTransition hJ
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set c := (1 - Real.log 2) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set w := (2 : ℝ) ^ (t / 2) * Real.exp (-(t / 2)) with hw
  have hw_eq : w = Real.exp (-(c * t)) := by
    rw [hw, Real.rpow_def_of_pos two_pos, ← Real.exp_add, hc]; congr 1; ring
  rw [heatKernel_eq, uniformize_eq_self hJ]
  have hpt : ∀ n : ℕ, poi t n * stepProb J n x y ≤
      w * poi (t / 2) n + C * 2 ^ s / t ^ s * poi t n := by
    intro n
    have hp0 := stepProb_nonneg hsub n x y
    have hp1 := stepProb_le_one hsub n x y
    have hpoi := poi_nonneg ht.le n
    have hpoi2 := poi_nonneg (by linarith : (0 : ℝ) ≤ t / 2) n
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    by_cases hn : (n : ℝ) < t / 2
    · have h1 : poi t n ≤ w * poi (t / 2) n := by
        have e : w * poi (t / 2) n = (2 : ℝ) ^ (t / 2) / 2 ^ n * poi t n := by
          rw [hw]; unfold poi
          rw [div_pow]
          have : Real.exp (-(t / 2)) * Real.exp (-(t / 2)) = Real.exp (-t) := by
            rw [← Real.exp_add]; congr 1; ring
          field_simp
          rw [← this]; ring
        rw [e]
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ (t / 2) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn.le
        have h3 : 1 ≤ (2 : ℝ) ^ (t / 2) / 2 ^ n := by
          rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
      have h4 : 0 ≤ C * 2 ^ s / t ^ s * poi t n := by positivity
      nlinarith
    · rw [not_lt] at hn
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · rw [h0] at hn; simp at hn; linarith
        · exact h0
      have hb := h n hn1 x y
      have h5 : C / (n : ℝ) ^ s ≤ C * 2 ^ s / t ^ s := by
        have e : C * 2 ^ s / t ^ s = C / (t / 2) ^ s := by
          rw [Real.div_rpow ht.le (by norm_num)]; field_simp
        rw [e]
        exact div_le_div_of_nonneg_left hC (by positivity)
          (Real.rpow_le_rpow (by positivity) hn hs.le)
      have h6 : 0 ≤ w * poi (t / 2) n := by positivity
      calc poi t n * stepProb J n x y ≤ poi t n * (C * 2 ^ s / t ^ s) :=
            mul_le_mul_of_nonneg_left (hb.trans h5) hpoi
        _ ≤ _ := by nlinarith
  have hsum := Summable.tsum_le_tsum hpt (summable_heat hsub ht.le x y)
    (((summable_poi (t / 2)).mul_left w).add ((summable_poi t).mul_left _))
  rw [Summable.tsum_add ((summable_poi (t / 2)).mul_left w) ((summable_poi t).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_poi, tsum_poi, mul_one, mul_one, hw_eq] at hsum
  refine hsum.trans ?_
  have := exp_neg_le_rpow hc0 hs ht
  linarith

end P6Dev

end ErschlerZheng
end

section
/-!
# The scale function `φ` of Proposition 7.20 from the bounds of Proposition 7.18 (prover 6)

`ψ_{a,γ}(r) = r^a (log₂ r)^{-γ}` is non-decreasing on `[R, ∞)` once `γ ⩽ a log R`, `R > 1`.
`(log₂ L)^b ⩽ K L^ε` for `L ⩾ 2`. From tail and truncated second-moment bounds
`C r^{-β}(log₂ r)^a (log₂ log₂ r)^b`, `C r^{2-β}(…)` for `r ⩾ 4`, the function
`φ(r) = ψ_{β,a+ε}(max r R₀)/c` is positive, non-decreasing, doubling with constant `2^β`, and
satisfies the two hypotheses (ii) of Proposition 7.20 for every `r > 0`. A pointwise bound
`J(u, v) ⩽ C ρ^{-1-β}(log₂ ρ)^{a'}(log₂ log₂ ρ)^b` (`ρ ⩾ 4`) bounds `‖J^R_2‖_∞` for large `R`.
-/

open DurrettProbability MarkovChain
open scoped ENNReal

namespace ErschlerZheng

namespace P6Dev

/-- `u^a (log₂ u)^{-γ}` is monotone on `[R, ∞)`. -/
lemma psi_mono {a γ R u v : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hR : 1 < R)
    (hRγ : γ ≤ a * Real.log R) (hu : R ≤ u) (huv : u ≤ v) :
    u ^ a * Real.logb 2 u ^ (-γ) ≤ v ^ a * Real.logb 2 v ^ (-γ) := by
  have hu1 : 1 < u := lt_of_lt_of_le hR hu
  have hv1 : 1 < v := lt_of_lt_of_le hu1 huv
  have hlu : 0 < Real.log u := Real.log_pos hu1
  have hlv : 0 < Real.log v := Real.log_pos hv1
  have hℓu : 0 < Real.logb 2 u := Real.logb_pos one_lt_two hu1
  have hℓv : 0 < Real.logb 2 v := Real.logb_pos one_lt_two hv1
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by linarith), Real.log_rpow hℓu, Real.log_rpow (by linarith),
    Real.log_rpow hℓv]
  have hratio : Real.log (Real.logb 2 v) - Real.log (Real.logb 2 u) ≤
      (Real.log v - Real.log u) / Real.log u := by
    rw [← Real.log_div hℓv.ne' hℓu.ne']
    have e : Real.logb 2 v / Real.logb 2 u = Real.log v / Real.log u := by
      unfold Real.logb
      have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp
    rw [e]
    have := Real.log_le_sub_one_of_pos (div_pos hlv hlu)
    calc _ ≤ Real.log v / Real.log u - 1 := this
      _ = _ := by field_simp
  have hlog_mono : Real.log R ≤ Real.log u := Real.log_le_log (by linarith) hu
  have hdiff : 0 ≤ Real.log v - Real.log u := sub_nonneg.mpr (Real.log_le_log (by linarith) huv)
  have key : γ * ((Real.log v - Real.log u) / Real.log u) ≤ a * (Real.log v - Real.log u) := by
    rw [mul_div_assoc', div_le_iff₀ hlu]
    calc γ * (Real.log v - Real.log u) ≤ (a * Real.log R) * (Real.log v - Real.log u) :=
          mul_le_mul_of_nonneg_right hRγ hdiff
      _ ≤ (a * Real.log u) * (Real.log v - Real.log u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_mono ha.le) hdiff
      _ = _ := by ring
  nlinarith [mul_le_mul_of_nonneg_left hratio hγ]

/-- `(log₂ L)^b ⩽ (b/(ε log 2))^b L^ε` for `L ⩾ 2`. -/
lemma logb_rpow_le {b ε L : ℝ} (hb : 0 < b) (hε : 0 < ε) (hL : 2 ≤ L) :
    Real.logb 2 L ^ b ≤ (b / (ε * Real.log 2)) ^ b * L ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 < L := by linarith
  have h1 : Real.log L ≤ L ^ (ε / b) / (ε / b) := Real.log_le_rpow_div hL0.le (by positivity)
  have hℓ : 0 ≤ Real.logb 2 L := (Real.logb_pos one_lt_two (by linarith)).le
  have h2 : Real.logb 2 L ≤ b / (ε * Real.log 2) * L ^ (ε / b) := by
    unfold Real.logb
    rw [div_le_iff₀ hl2]
    calc Real.log L ≤ L ^ (ε / b) / (ε / b) := h1
      _ = b / (ε * Real.log 2) * L ^ (ε / b) * Real.log 2 := by
          field_simp
  calc Real.logb 2 L ^ b ≤ (b / (ε * Real.log 2) * L ^ (ε / b)) ^ b :=
        Real.rpow_le_rpow hℓ h2 hb.le
    _ = (b / (ε * Real.log 2)) ^ b * L ^ ε := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hL0.le,
          div_mul_cancel₀ _ hb.ne']

/-- `ψ(r) = r^a (log₂ r)^{-γ}`. -/
noncomputable def psi (a γ r : ℝ) : ℝ := r ^ a * Real.logb 2 r ^ (-γ)

lemma psi_pos {a γ r : ℝ} (hr : 1 < r) : 0 < psi a γ r := by
  unfold psi
  have := Real.logb_pos one_lt_two hr
  have : 0 < r := by linarith
  positivity

/-- For `r ⩾ 4`, `C r^{-β} ℓ^a ℓℓ^b ⩽ C K / ψ_{β,a+ε}(r)`, with `ℓ = log₂ r`. -/
lemma bound_absorb {β a b ε C r : ℝ} (hb : 0 < b) (hε : 0 < ε) (hC : 0 ≤ C) (hr : 4 ≤ r) :
    C * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b ≤
      C * (b / (ε * Real.log 2)) ^ b / psi β (a + ε) r := by
  have hr0 : 0 < r := by linarith
  have hℓ2 : 2 ≤ Real.logb 2 r := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hr0]; norm_num; linarith
  have hℓ : 0 < Real.logb 2 r := by linarith
  have hll := logb_rpow_le hb hε hℓ2
  have hll0 : 0 ≤ Real.logb 2 (Real.logb 2 r) := (Real.logb_pos one_lt_two (by linarith)).le
  unfold psi
  rw [div_eq_mul_inv, mul_inv, Real.rpow_neg hℓ.le, inv_inv, ← Real.rpow_neg hr0.le,
    Real.rpow_add hℓ]
  have h0 : 0 ≤ C * r ^ (-β) * Real.logb 2 r ^ a := by positivity
  calc C * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b
      ≤ C * r ^ (-β) * Real.logb 2 r ^ a * ((b / (ε * Real.log 2)) ^ b * Real.logb 2 r ^ ε) :=
        mul_le_mul_of_nonneg_left hll h0
    _ = _ := by ring


lemma le_one_of_isTransition {X : Type*} {J : X → X → ℝ} (hJ : IsTransition J) (x y : X) :
    J x y ≤ 1 := by
  rw [← hJ.2.2 x]
  exact (hJ.2.1 x).le_tsum y fun z _ => hJ.1 x z

/-- The scale function `φ`. -/
lemma exists_phi {X : Type*} {J ρ : X → X → ℝ} (hJ : IsTransition J) (hρ0 : ∀ x y, 0 ≤ ρ x y)
    {β a b ε C : ℝ} (hβ : 0 < β) (ha : 0 ≤ a) (hb : 0 < b) (hε : 0 < ε) (hC : 0 ≤ C)
    (htail : ∀ x, ∀ r : ℝ, 4 ≤ r → ∑' y, (if r ≤ ρ x y then J x y else 0) ≤
      C * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b)
    (hsec : ∀ x, ∀ r : ℝ, 4 ≤ r → ∑' y, (if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) ≤
      C * r ^ (2 - β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b) :
    ∃ φ : ℝ → ℝ, (∀ r, 0 < r → 0 < φ r) ∧ MonotoneOn φ (Set.Ioi 0) ∧
      (∀ r, 0 < r → φ (2 * r) ≤ 2 ^ β * φ r) ∧
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if r < ρ x y then J x y else 0) ≤ 1 / φ r) ∧
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) ≤ r ^ 2 / φ r) ∧
      ∃ c > 0, ∃ R₀ ≥ (4 : ℝ), (∀ r, R₀ ≤ r → φ r = psi β (a + ε) r / c) ∧
        (∀ r, psi β (a + ε) R₀ / c ≤ φ r) := by
  set γ := a + ε with hγ
  have hγ0 : 0 ≤ γ := by positivity
  set K := (b / (ε * Real.log 2)) ^ b with hK
  have hK0 : 0 ≤ K := by
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  set R₀ := max 4 (Real.exp (γ / β)) with hR₀
  have hR₀4 : 4 ≤ R₀ := le_max_left _ _
  have hR₀1 : 1 < R₀ := by linarith
  have hR₀γ : γ ≤ β * Real.log R₀ := by
    have : γ / β ≤ Real.log R₀ := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact le_max_right _ _
    rw [div_le_iff₀ hβ] at this; linarith
  have hmono : ∀ u v, R₀ ≤ u → u ≤ v → psi β γ u ≤ psi β γ v := fun u v hu huv =>
    psi_mono hβ hγ0 hR₀1 hR₀γ hu huv
  have hψR₀ : 0 < psi β γ R₀ := psi_pos hR₀1
  set c := max (C * K) (psi β γ R₀) with hc
  have hc0 : 0 < c := lt_of_lt_of_le hψR₀ (le_max_right _ _)
  have hcK : C * K ≤ c := le_max_left _ _
  have hcψ : psi β γ R₀ ≤ c := le_max_right _ _
  set φ : ℝ → ℝ := fun r => psi β γ (max r R₀) / c with hφ
  have hφpos : ∀ r, 0 < φ r := fun r =>
    div_pos (psi_pos (lt_of_lt_of_le hR₀1 (le_max_right _ _))) hc0
  have hφlow : ∀ r, psi β γ R₀ / c ≤ φ r := fun r =>
    div_le_div_of_nonneg_right (hmono _ _ le_rfl (le_max_right _ _)) hc0.le
  have hφle1 : ∀ r, r < R₀ → φ r ≤ 1 := fun r hr => by
    simp only [hφ, max_eq_right hr.le]
    rw [div_le_one hc0]; exact hcψ
  have hφeq : ∀ r, R₀ ≤ r → φ r = psi β γ r / c := fun r hr => by
    simp only [hφ, max_eq_left hr]
  have hrow : ∀ x, ∑' y, J x y = 1 := hJ.2.2
  refine ⟨φ, fun r _ => hφpos r, ?_, ?_, ?_, ?_, c, hc0, R₀, hR₀4, hφeq, hφlow⟩
  · -- monotone
    intro r _ s _ hrs
    exact div_le_div_of_nonneg_right (hmono _ _ (le_max_right _ _) (max_le_max hrs le_rfl)) hc0.le
  · -- doubling
    intro r hr
    set m := max r R₀ with hm
    have hm1 : 1 < m := lt_of_lt_of_le hR₀1 (le_max_right _ _)
    have h2m : max (2 * r) R₀ ≤ 2 * m := max_le (by linarith [le_max_left r R₀])
      (by linarith [le_max_right r R₀])
    have hA : psi β γ (max (2 * r) R₀) ≤ psi β γ (2 * m) := hmono _ _ (le_max_right _ _) h2m
    have hB : psi β γ (2 * m) ≤ 2 ^ β * psi β γ m := by
      unfold psi
      have hℓm : 0 < Real.logb 2 m := Real.logb_pos one_lt_two hm1
      have hℓ2m : Real.logb 2 m ≤ Real.logb 2 (2 * m) :=
        Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have := Real.rpow_le_rpow_of_nonpos hℓm hℓ2m (by linarith : -γ ≤ 0)
      have h0 : 0 ≤ (2 : ℝ) ^ β * m ^ β := by positivity
      calc 2 ^ β * m ^ β * Real.logb 2 (2 * m) ^ (-γ) ≤ 2 ^ β * m ^ β * Real.logb 2 m ^ (-γ) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    show psi β γ (max (2 * r) R₀) / c ≤ 2 ^ β * (psi β γ (max r R₀) / c)
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (hA.trans hB) hc0.le
  · -- tail
    intro x r hr
    have hs1 : Summable (fun y => if r < ρ x y then J x y else 0) :=
      Summable.of_nonneg_of_le (fun y => by split_ifs <;> simp [hJ.1 x y])
        (fun y => by split_ifs <;> simp [hJ.1 x y]) (hJ.2.1 x)
    by_cases hrR : R₀ ≤ r
    · have hs2 : Summable (fun y => if r ≤ ρ x y then J x y else 0) :=
        Summable.of_nonneg_of_le (fun y => by split_ifs <;> simp [hJ.1 x y])
          (fun y => by split_ifs <;> simp [hJ.1 x y]) (hJ.2.1 x)
      have h1 : ∑' y, (if r < ρ x y then J x y else 0) ≤
          ∑' y, (if r ≤ ρ x y then J x y else 0) :=
        Summable.tsum_le_tsum (fun y => by
          by_cases h : r < ρ x y
          · rw [if_pos h, if_pos h.le]
          · rw [if_neg h]; split_ifs <;> simp [hJ.1 x y]) hs1 hs2
      have h2 := htail x r (by linarith)
      have h3 := bound_absorb hb hε hC (by linarith : (4 : ℝ) ≤ r) (β := β) (a := a)
      rw [hφeq r hrR, one_div_div]
      have hψ : 0 < psi β γ r := psi_pos (by linarith)
      calc _ ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ C * K / psi β γ r := h3
        _ ≤ c / psi β γ r := div_le_div_of_nonneg_right hcK hψ.le
    · rw [not_le] at hrR
      have h1 : ∑' y, (if r < ρ x y then J x y else 0) ≤ ∑' y, J x y :=
        Summable.tsum_le_tsum (fun y => by split_ifs <;> simp [hJ.1 x y]) hs1 (hJ.2.1 x)
      rw [hrow] at h1
      have := hφle1 r hrR
      have hp := hφpos r
      calc _ ≤ (1 : ℝ) := h1
        _ ≤ 1 / φ r := by rw [le_div_iff₀ hp]; linarith
  · -- second moment
    intro x r hr
    have hs1 : Summable (fun y => if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) := by
      refine Summable.of_nonneg_of_le (fun y => by
          split_ifs
          · exact mul_nonneg (sq_nonneg _) (hJ.1 x y)
          · exact le_rfl) (fun y => ?_) ((hJ.2.1 x).mul_left (r ^ 2))
      split_ifs with h
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hρ0 x y) h 2) (hJ.1 x y)
      · exact mul_nonneg (sq_nonneg _) (hJ.1 x y)
    by_cases hrR : R₀ ≤ r
    · have h2 := hsec x r (by linarith)
      have h3 := bound_absorb hb hε hC (by linarith : (4 : ℝ) ≤ r) (β := β) (a := a)
      rw [hφeq r hrR]
      have hψ : 0 < psi β γ r := psi_pos (by linarith)
      have hr0 : 0 < r := by linarith
      have e : C * r ^ (2 - β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b =
          r ^ 2 * (C * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b) := by
        rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_two]; ring
      calc _ ≤ _ := h2
        _ = _ := e
        _ ≤ r ^ 2 * (C * K / psi β γ r) := mul_le_mul_of_nonneg_left h3 (sq_nonneg r)
        _ ≤ r ^ 2 * (c / psi β γ r) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcK hψ.le) (sq_nonneg r)
        _ = r ^ 2 / (psi β γ r / c) := by field_simp
    · rw [not_le] at hrR
      have h1 : ∑' y, (if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) ≤ ∑' y, r ^ 2 * J x y := by
        refine Summable.tsum_le_tsum (fun y => ?_) hs1 ((hJ.2.1 x).mul_left (r ^ 2))
        split_ifs with h
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hρ0 x y) h 2) (hJ.1 x y)
        · exact mul_nonneg (sq_nonneg _) (hJ.1 x y)
      rw [tsum_mul_left, hrow, mul_one] at h1
      have := hφle1 r hrR
      have hp := hφpos r
      calc _ ≤ r ^ 2 := h1
        _ ≤ r ^ 2 / φ r := by
            rw [le_div_iff₀ hp]
            exact mul_le_of_le_one_right (sq_nonneg r) this

/-- The far part: `‖J^R_2‖_∞ ⩽ c₄/ψ_{1+β, a'+ε}(R)` for `R ⩾ R₁`, and `⩽ 1` always. -/
lemma far_bound {X : Type*} {J ρ : X → X → ℝ} (hJ : IsTransition J)
    {β a' b ε C : ℝ} (hβ : 0 < β) (ha : 0 ≤ a') (hb : 0 < b) (hε : 0 < ε) (hC : 0 ≤ C)
    (hpt : ∀ u v, 4 ≤ ρ u v → J u v ≤
      C * ρ u v ^ (-1 - β) * Real.logb 2 (ρ u v) ^ a' * Real.logb 2 (Real.logb 2 (ρ u v)) ^ b) :
    (∀ R, supNorm (farPart J ρ R) ≤ 1) ∧
    ∃ c₄ ≥ (0 : ℝ), ∃ R₁ ≥ (4 : ℝ),
      (∀ u v, R₁ ≤ u → u ≤ v → psi (1 + β) (a' + ε) u ≤ psi (1 + β) (a' + ε) v) ∧
      ∀ R, R₁ ≤ R →
      supNorm (farPart J ρ R) ≤ ENNReal.ofReal (c₄ / psi (1 + β) (a' + ε) R) := by
  constructor
  · intro R
    refine iSup₂_le fun u v => ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold farPart
    split_ifs
    · exact le_one_of_isTransition hJ u v
    · exact zero_le_one
  set γ := a' + ε with hγ
  have hγ0 : 0 ≤ γ := by positivity
  set K := (b / (ε * Real.log 2)) ^ b with hK
  have hK0 : 0 ≤ K := by
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  set R₁ := max 4 (Real.exp (γ / (1 + β))) with hR₁
  have hR₁4 : 4 ≤ R₁ := le_max_left _ _
  have hR₁1 : 1 < R₁ := by linarith
  have hR₁γ : γ ≤ (1 + β) * Real.log R₁ := by
    have : γ / (1 + β) ≤ Real.log R₁ := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at this; linarith
  refine ⟨C * K, by positivity, R₁, hR₁4, fun u v hu huv =>
    psi_mono (by linarith : (0 : ℝ) < 1 + β) hγ0 hR₁1 hR₁γ hu huv, fun R hR => ?_⟩
  have hR1 : 1 < R := by linarith
  have hψR : 0 < psi (1 + β) γ R := psi_pos hR1
  refine iSup₂_le fun u v => ENNReal.ofReal_le_ofReal ?_
  unfold farPart
  split_ifs with h
  · have hρ4 : 4 ≤ ρ u v := by linarith
    have h1 := hpt u v hρ4
    have h2 := bound_absorb hb hε hC hρ4 (β := 1 + β) (a := a')
    have e : ρ u v ^ (-1 - β) = ρ u v ^ (-(1 + β)) := by congr 1; ring
    rw [e] at h1
    have hmon := psi_mono (by linarith : (0 : ℝ) < 1 + β) hγ0 hR₁1 hR₁γ hR h.le
    calc J u v ≤ _ := h1
      _ ≤ C * K / psi (1 + β) γ (ρ u v) := h2
      _ ≤ C * K / psi (1 + β) γ R := div_le_div_of_nonneg_left (by positivity) hψR hmon
  · exact div_nonneg (by positivity) hψR.le

end P6Dev

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

theorem rayPrefix_add (x : Ray) (n m : ℕ) :
    rayPrefix x (n + m) = rayPrefix x n ++ rayPrefix (shiftRay x n) m := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    by_cases hi : i < n
    · rw [List.getElem_append_left (by rw [length_rayPrefix]; exact hi), getElem_rayPrefix]
    · rw [List.getElem_append_right (by rw [length_rayPrefix]; omega), getElem_rayPrefix]
      simp only [shiftRay, length_rayPrefix]
      congr 1
      omega

/-- `x = x_1 … x_n (𝔰ⁿ x)`. -/
theorem prepend_rayPrefix_shiftRay (x : Ray) (n : ℕ) : prepend (rayPrefix x n) (shiftRay x n) = x := by
  funext i
  unfold prepend
  split_ifs with h
  · rw [getElem_rayPrefix]
  · simp only [shiftRay, length_rayPrefix] at h ⊢
    congr 1; omega

end RayBasic

end ErschlerZheng
end

section
/-!
# The Gray code on finite words, and how the generators move it

For a word `w` of length `N`, `grayList w < 2^N`. The generator `a` changes it by `+1` when `w`
has an even number of zeros and by `-1` otherwise; a generator `γ_ω` either fixes `w` or changes
it by `-1` (even) or `+1` (odd). From every word there is a generator step up (below the top
value `2^N - 1`) and down (above `0`) whose section at `w` is trivial.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace GrayDev

open GrigBasic

theorem grayList_cons (b : Bool) (v : List Bool) :
    grayList (b :: v) = (b :: v).count false % 2 + 2 * grayList v := rfl

theorem grayList_append_true (w : List Bool) : grayList (w ++ [true]) = grayList w := by
  induction w with
  | nil => simp [grayList]
  | cons b v ih =>
    rw [List.cons_append, grayList_cons, grayList_cons, ih]
    simp [List.count_cons, List.count_append]

theorem grayList_append_replicate (w : List Bool) (m : ℕ) :
    grayList (w ++ List.replicate m true) = grayList w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, grayList_append_true, ih]

theorem grayList_inj : ∀ (v w : List Bool), v.length = w.length → grayList v = grayList w → v = w
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: v, c :: w, hl, hg => by
    rw [grayList_cons, grayList_cons] at hg
    have h1 : (b :: v).count false % 2 = (c :: w).count false % 2 := by omega
    have h2 : grayList v = grayList w := by omega
    have hv := grayList_inj v w (by simpa using hl) h2
    subst hv
    cases b <;> cases c <;> simp [List.count_cons] at h1 ⊢ <;> omega

end GrayDev

end ErschlerZheng
end

section
/-!
# The Schreier graph of `1^∞` through the Gray code

Rays that are all ones from position `N` on are `prepend w 1^∞` with `|w| = N`; their Gray code
is `grayList w`. A generator moves the Gray code of such a ray by at most one, and from `w` to
`w'` of the same length there is a path of `|ḡ(w) - ḡ(w')|` generators with trivial sections at
the intermediate words, so it carries any tail along unchanged.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierDev

open GrigBasic RayBasic GrayDev

/-- `x_k = 1` for every `k ⩾ N`. -/
def AllOnesFrom (N : ℕ) (x : Ray) : Prop := ∀ k ≥ N, x k = true

theorem isCofinal_iff (x : Ray) : IsCofinal x ↔ ∃ N, AllOnesFrom N x :=
  Filter.eventually_atTop

theorem AllOnesFrom.mono {N M : ℕ} {x : Ray} (h : AllOnesFrom N x) (hNM : N ≤ M) :
    AllOnesFrom M x := fun k hk => h k (le_trans hNM hk)

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

theorem shiftRay_eq_oneRay {N : ℕ} {x : Ray} (h : AllOnesFrom N x) : shiftRay x N = oneRay := by
  funext i; simp only [shiftRay, oneRay]; exact h _ (by omega)

theorem eq_prepend {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    x = prepend (rayPrefix x N) oneRay := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay x N]
  rw [shiftRay_eq_oneRay h]

theorem grayCode_eq {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    grayCode x = grayList (rayPrefix x N) := by
  unfold grayCode
  set M := maxZeroIndex x with hM
  have hMdef : M = sSup {k | 1 ≤ k ∧ x (k - 1) = false} := rfl
  have hbdd : ∀ k ∈ {k | 1 ≤ k ∧ x (k - 1) = false}, k ≤ N := by
    rintro k ⟨hk1, hk⟩
    by_contra hc
    have := h (k - 1) (by omega)
    rw [this] at hk
    exact Bool.noConfusion hk
  have hMN : M ≤ N := csSup_le' hbdd
  have hones : AllOnesFrom M x := by
    intro k hk
    by_contra hc
    have hmem : k + 1 ∈ {k | 1 ≤ k ∧ x (k - 1) = false} := by
      refine ⟨by omega, ?_⟩
      simpa using hc
    have := le_csSup ⟨N, hbdd⟩ hmem
    rw [← hMdef] at this
    omega
  have hsplit : rayPrefix x N = rayPrefix x M ++ List.replicate (N - M) true := by
    rw [show N = M + (N - M) by omega, rayPrefix_add, shiftRay_eq_oneRay hones,
      rayPrefix_oneRay]
    simp
  rw [hsplit, grayList_append_replicate]

/-! ### Generators on rays that are eventually all ones -/

end SchreierDev

end ErschlerZheng
end

section
/-!
# Proposition 7.11: the Green function bound (Erschler–Zheng pp. 49–51, prover 6)

* `J = P_{μ_β}` is a symmetric transition kernel; `d_𝒮` is a metric on `1^∞·G_ω` (the Gray-code
  distance, A2 and A9's module).
* On-diagonal: `Pⁿ ⩽ C n^{-1/β}` (Proposition 7.19, H3) gives `p(t, x, y) ⩽ C₀ t^{-1/β}` for all
  `t > 0` (split the Poisson weights at `t/2`; `P6Green.heat_le_of_stepProb_le`).
* Scale: `φ(r) = ψ_{β, a+ε'}(max r R₀)/c` with `a = 2A(β − 1/D)`, `ε' = min(ε, A/D)`, from the tail
  and second-moment bounds of Proposition 7.18 (H1).
* Off-diagonal (Proposition 7.20, Markov H8): for `t ⩽ φ(d)`,
  `p(t, x, y) ⩽ K t`, `K = C/φ(d)^{1+1/β} + ‖J^{κd}_2‖_∞`, `κ = β/(3(1+β))`, the far part bounded by
  the pointwise bound of Proposition 7.18.
* `G = ∫_0^∞ p(t) dt ⩽ ∫_0^{T} K t + ∫_T^∞ C₀ t^{-1/β}`, `T = (C₀/K)^{β/(1+β)} ⩽ φ(d)`, which is
  `C₀^{2β/(1+β)}(1/2 + β/(1−β)) K^{(1−β)/(1+β)}`; and `K ⩽ K₁ d^{-1-β} (log₂ d)^{a'+ε'}`,
  `a' = 2A(1 − 1/D + β)`, whose `(1−β)/(1+β)` power is the stated bound.
-/

open scoped RightActions ENNReal
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

open SchreierDev

set_option linter.unusedSectionVars false

/-! ### `d_𝒮` is a metric on the orbit -/

lemma isCofinal_of_mem_orbitOne (ω : ℕ → Fin 3) (x : orbitOne ω) : IsCofinal (x : Ray) := by
  have h := ((isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary).2.1 ω oneRay).1
  have hx : (x : Ray) ∈ rightOrbit (grigorchuk ω) oneRay := x.2
  rw [h] at hx
  exact hx

lemma orbitDist_eq_abs (ω : ℕ → Fin 3) (x y : orbitOne ω) :
    orbitDist ω x y = |(grayCode (x : Ray) : ℝ) - grayCode (y : Ray)| := by
  have h := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x y (isCofinal_of_mem_orbitOne ω x)
    (isCofinal_of_mem_orbitOne ω y)
  unfold orbitDist
  have h' : ((schreierDist ω x y : ℤ) : ℝ) =
      ((|(grayCode (x : Ray) : ℤ) - grayCode (y : Ray)| : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

lemma isMetric_orbitDist (ω : ℕ → Fin 3) : IsMetric (orbitDist ω) where
  self_eq x := by rw [orbitDist_eq_abs]; simp
  eq_of_eq_zero x y h := by
    rw [orbitDist_eq_abs, abs_eq_zero, sub_eq_zero] at h
    have hg : grayCode (x : Ray) = grayCode (y : Ray) := by exact_mod_cast h
    obtain ⟨N1, h1⟩ := (isCofinal_iff (x : Ray)).mp (isCofinal_of_mem_orbitOne ω x)
    obtain ⟨N2, h2⟩ := (isCofinal_iff (y : Ray)).mp (isCofinal_of_mem_orbitOne ω y)
    have hx' := h1.mono (le_max_left N1 N2)
    have hy' := h2.mono (le_max_right N1 N2)
    rw [grayCode_eq hx', grayCode_eq hy'] at hg
    have := GrayDev.grayList_inj _ _ (by simp [length_rayPrefix]) hg
    apply Subtype.ext
    rw [eq_prepend hx', eq_prepend hy', this]
  symm x y := by rw [orbitDist_eq_abs, orbitDist_eq_abs, abs_sub_comm]
  triangle x y z := by
    rw [orbitDist_eq_abs, orbitDist_eq_abs, orbitDist_eq_abs]; exact abs_sub_le _ _ _

/-! ### The time integral -/

lemma T_algebra {β C₀ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hC₀ : 0 < C₀) (hK : 0 < K) :
    K * ((C₀ / K) ^ (β / (1 + β))) ^ 2 / 2 +
        C₀ * (β / (1 - β)) * ((C₀ / K) ^ (β / (1 + β))) ^ (1 - 1 / β) =
      C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * K ^ ((1 - β) / (1 + β)) := by
  have hβne : β ≠ 0 := hβ0.ne'
  have h1β : 1 + β ≠ 0 := by linarith
  set q := β / (1 + β) with hq
  have hT : (C₀ / K) ^ q = C₀ ^ q * K ^ (-q) := by
    rw [Real.div_rpow hC₀.le hK.le, Real.rpow_neg hK.le, div_eq_mul_inv]
  have h1 : K * ((C₀ / K) ^ q) ^ 2 = C₀ ^ (2 * β / (1 + β)) * K ^ ((1 - β) / (1 + β)) := by
    rw [hT, mul_pow, ← Real.rpow_natCast (C₀ ^ q), ← Real.rpow_natCast (K ^ (-q)),
      ← Real.rpow_mul hC₀.le, ← Real.rpow_mul hK.le]
    have e1 : q * ((2 : ℕ) : ℝ) = 2 * β / (1 + β) := by rw [hq]; push_cast; ring
    have e2 : (1 - β) / (1 + β) = 1 + (-q * ((2 : ℕ) : ℝ)) := by
      rw [hq]; push_cast; field_simp; ring
    rw [e1, e2, Real.rpow_add hK, Real.rpow_one]; ring
  have h2 : C₀ * ((C₀ / K) ^ q) ^ (1 - 1 / β) =
      C₀ ^ (2 * β / (1 + β)) * K ^ ((1 - β) / (1 + β)) := by
    rw [hT, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC₀.le,
      ← Real.rpow_mul hK.le]
    have e1 : 2 * β / (1 + β) = 1 + q * (1 - 1 / β) := by rw [hq]; field_simp; ring
    have e2 : (1 - β) / (1 + β) = -q * (1 - 1 / β) := by rw [hq]; field_simp; ring
    rw [e1, e2, Real.rpow_add hC₀, Real.rpow_one]; ring
  calc _ = (K * ((C₀ / K) ^ q) ^ 2) / 2 +
        (β / (1 - β)) * (C₀ * ((C₀ / K) ^ q) ^ (1 - 1 / β)) := by ring
    _ = _ := by rw [h1, h2]; ring

lemma green_le_of_heat {X : Type*} [DecidableEq X] {J : X → X → ℝ} (hJ : IsTransition J)
    {β C₀ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hC₀ : 0 < C₀) (hK : 0 < K) (x y : X)
    (h1 : ∀ t : ℝ, 0 < t → heatKernel J t x y ≤ C₀ / t ^ (1 / β))
    (h2 : ∀ t : ℝ, 0 < t → t ≤ (C₀ / K) ^ (β / (1 + β)) →
      ENNReal.ofReal (heatKernel J t x y) ≤ ENNReal.ofReal (K * t)) :
    green J x y ≤ ENNReal.ofReal
      (C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * K ^ ((1 - β) / (1 + β))) := by
  rw [green_eq_lintegral hJ, ← T_algebra hβ0 hβ1 hC₀ hK]
  refine lintegral_le_of_bounds _ hβ0 hβ1 (by positivity) hK.le hC₀.le (fun t ht => ?_) h2
  have htpos : 0 < t := lt_trans (by positivity) ht
  refine ENNReal.ofReal_le_ofReal ((h1 t htpos).trans (le_of_eq ?_))
  rw [Real.rpow_neg htpos.le, div_eq_mul_inv]

/-! ### Powers of `ψ` -/

lemma one_div_psi_rpow {a γ s r : ℝ} (hr : 1 < r) :
    1 / psi a γ r ^ s = r ^ (-(a * s)) * Real.logb 2 r ^ (γ * s) := by
  have hr0 : 0 < r := by linarith
  have hℓ : 0 < Real.logb 2 r := Real.logb_pos one_lt_two hr
  unfold psi
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr0.le,
    ← Real.rpow_mul hℓ.le, one_div, mul_inv, ← Real.rpow_neg hr0.le, ← Real.rpow_neg hℓ.le,
    show -(-γ * s) = γ * s by ring]

end P6Dev

end ErschlerZheng
end

section
open scoped RightActions ENNReal
open DurrettProbability MarkovChain
open ErschlerZheng
set_option maxHeartbeats 4000000 in
open P6Dev in
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    [DecidableEq (orbitOne ω)] (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ)
    (hA : 0 < A) (hDA : D ∣ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ x y : orbitOne ω, 2 ≤ orbitDist ω x y →
      MarkovChain.green (orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay) x y ≤
        ENNReal.ofReal (C *
          (orbitDist ω x y / Real.logb 2 (orbitDist ω x y) ^ (2 * A)) ^ (β - 1) *
          Real.logb 2 (orbitDist ω x y) ^ (-((1 - β) / (1 + β) * (2 * (A : ℝ) / D - ε)))) := by
  /- parameters -/
  have hD3 := three_le_of_satisfiesFr hω
  have hD : 1 ≤ D := by omega
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD3
  have hDpos : (0 : ℝ) < D := by linarith
  have hinvD : 1 / (D : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hDpos (by norm_num)]; linarith
  have hβ : 0 < β := by linarith
  have hβD : 1 / (D : ℝ) < β := by linarith
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hk := isAdmissibleSeq_kLog D A hD3 hDA hA
  obtain ⟨C', -, hprob⟩ := isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le D β hβ
  have hμ := (hprob ω hω (kLog A) hk (eventually_kLog_le A)).1
  set J := orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay with hJdef
  have hJT : IsTransition J := isTransition_orbitKernel (grigorchuk ω) hμ (oneRay : Ray)
  have hJS : MarkovChain.IsSymmetric J :=
    isSymmetric_orbitKernel _ (muBeta_inv D ω (kLog A) β) oneRay
  have hρ := isMetric_orbitDist ω
  have hρ0 : ∀ x y, 0 ≤ orbitDist ω x y := fun x y => by
    rw [orbitDist_eq_abs]; exact abs_nonneg _
  /- the on-diagonal heat kernel bound, from Proposition 7.19 -/
  obtain ⟨C₃, hC₃⟩ := stepProb_orbitKernel_muBeta_le D β hβ1 hβ2
  set C₃' := max C₃ 0 with hC₃'
  have hstep : ∀ n : ℕ, 1 ≤ n → ∀ x y, stepProb J n x y ≤ C₃' / (n : ℝ) ^ (1 / β) :=
    fun n hn x y => (hC₃ ω hω (kLog A) hk n hn x y).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlog2 : 0 < (1 - Real.log 2) / 2 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  set C₀ := (1 / β / ((1 - Real.log 2) / 2)) ^ (1 / β) + C₃' * 2 ^ (1 / β) with hC₀def
  have hC₀ : 0 < C₀ := by
    have h1 : 0 < (1 / β / ((1 - Real.log 2) / 2)) ^ (1 / β) :=
      Real.rpow_pos_of_pos (div_pos (by positivity) hlog2) _
    have h2 : 0 ≤ C₃' * 2 ^ (1 / β) := mul_nonneg (le_max_right _ _) (by positivity)
    linarith
  have hheat : ∀ t : ℝ, 0 < t → ∀ x y, heatKernel J t x y ≤ C₀ / t ^ (1 / β) := by
    intro t ht x y
    have := heat_le_of_stepProb_le hJT (by positivity) (le_max_right _ _) hstep t ht x y
    rw [hC₀def, add_div]; exact this
  /- Proposition 7.18 -/
  obtain ⟨C₁, h18i, h18ii, h18iii⟩ := orbitKernel_muBeta_le_and_tail_le D ω hω β hβ1 hβ2 A hA hDA
  set C₂ := max C₁ 0 with hC₂
  have hC₂0 : 0 ≤ C₂ := le_max_right _ _
  set ε' := min ε (A / D) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'AD : ε' ≤ A / D := min_le_right _ _
  set a := 2 * (A : ℝ) * (β - 1 / D) with ha
  set a' := 2 * (A : ℝ) * (1 - 1 / D + β) with ha'
  set b := 1 + 1 / (D : ℝ) with hb
  have ha0 : 0 ≤ a := by rw [ha]; have : 0 < β - 1 / D := by linarith
                         positivity
  have ha'0 : 0 ≤ a' := by rw [ha']; have : 0 < 1 - 1 / (D : ℝ) + β := by linarith
                           positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hlogs : ∀ r : ℝ, 4 ≤ r → 0 ≤ Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b := by
    intro r hr
    have h1 : 0 ≤ Real.logb 2 r := (Real.logb_pos one_lt_two (by linarith)).le
    have h2 : 0 ≤ Real.logb 2 (Real.logb 2 r) := Real.logb_nonneg one_lt_two (by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]; norm_num; linarith)
    exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)
  have htail' : ∀ x, ∀ r : ℝ, 4 ≤ r → ∑' y, (if r ≤ orbitDist ω x y then J x y else 0) ≤
      C₂ * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b := by
    intro x r hr
    refine (h18ii x r hr).trans ?_
    have := hlogs r hr
    have h0 : 0 ≤ r ^ (-β) := by positivity
    calc C₁ * r ^ (-β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b
        = C₁ * (r ^ (-β) * (Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b)) := by ring
      _ ≤ C₂ * (r ^ (-β) * (Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  have hsec' : ∀ x, ∀ r : ℝ, 4 ≤ r →
      ∑' y, (if orbitDist ω x y ≤ r then orbitDist ω x y ^ 2 * J x y else 0) ≤
      C₂ * r ^ (2 - β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b := by
    intro x r hr
    refine (h18iii x r hr).trans ?_
    have := hlogs r hr
    have h0 : 0 ≤ r ^ (2 - β) := by positivity
    calc C₁ * r ^ (2 - β) * Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b
        = C₁ * (r ^ (2 - β) * (Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b)) := by ring
      _ ≤ C₂ * (r ^ (2 - β) * (Real.logb 2 r ^ a * Real.logb 2 (Real.logb 2 r) ^ b)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  have hpt' : ∀ u v, 4 ≤ orbitDist ω u v → J u v ≤
      C₂ * orbitDist ω u v ^ (-1 - β) * Real.logb 2 (orbitDist ω u v) ^ a' *
        Real.logb 2 (Real.logb 2 (orbitDist ω u v)) ^ b := by
    intro u v huv
    refine (h18i u v huv).trans ?_
    have h1 : 0 ≤ Real.logb 2 (orbitDist ω u v) := (Real.logb_pos one_lt_two (by linarith)).le
    have h1' : 0 ≤ Real.logb 2 (Real.logb 2 (orbitDist ω u v)) := Real.logb_nonneg one_lt_two (by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]; norm_num; linarith)
    have h2 : 0 ≤ Real.logb 2 (orbitDist ω u v) ^ a' *
        Real.logb 2 (Real.logb 2 (orbitDist ω u v)) ^ b :=
      mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h1' _)
    have h0 : 0 ≤ orbitDist ω u v ^ (-1 - β) := by positivity
    calc C₁ * orbitDist ω u v ^ (-1 - β) * Real.logb 2 (orbitDist ω u v) ^ a' *
          Real.logb 2 (Real.logb 2 (orbitDist ω u v)) ^ b
        = C₁ * (orbitDist ω u v ^ (-1 - β) * (Real.logb 2 (orbitDist ω u v) ^ a' *
          Real.logb 2 (Real.logb 2 (orbitDist ω u v)) ^ b)) := by ring
      _ ≤ C₂ * (orbitDist ω u v ^ (-1 - β) * (Real.logb 2 (orbitDist ω u v) ^ a' *
          Real.logb 2 (Real.logb 2 (orbitDist ω u v)) ^ b)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  /- the scale function and the far part -/
  obtain ⟨φ, hφpos, hφmono, hφdbl, hφtail, hφsec, cφ, hcφ, R₀, hR₀, hφeq, hφlow⟩ :=
    exists_phi hJT hρ0 hβ ha0 hb0 hε'0 hC₂0 htail' hsec'
  obtain ⟨hfar1, c₄, hc₄, R₁, hR₁, hψmono', hfar2⟩ := far_bound hJT hβ ha'0 hb0 hε'0 hC₂0 hpt'
  /- Proposition 7.20 -/
  obtain ⟨CH, hCH, hH8⟩ := heatKernel_le_of_onDiagonal_of_tail C₀ (2 ^ β) β hC₀ hβ
  have hoff := hH8 (orbitOne ω) J (orbitDist ω) φ hJT hJS hρ (fun t ht x => hheat t ht x x)
    hφpos hφmono hφdbl hφtail hφsec
  /- constants -/
  set γ := a + ε' with hγ
  set γ' := a' + ε' with hγ'
  set p := (1 - β) / (1 + β) with hp
  have hp0 : 0 < p := div_pos (by linarith) (by linarith)
  set Cm := max CH C₀ with hCm
  have hCm0 : 0 < Cm := lt_of_lt_of_le hC₀ (le_max_right _ _)
  set κ := β / (3 * (1 + β)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; linarith
  set e := 1 + 1 / β with he
  have he0 : 0 < e := by positivity
  set D₁ := max R₀ (R₁ / κ) with hD₁
  have hD₁4 : 4 ≤ D₁ := le_trans hR₀ (le_max_left _ _)
  have hψR₀ : 0 < psi β γ R₀ := psi_pos (by linarith)
  have hψR₁ : 0 < psi (1 + β) γ' R₁ := psi_pos (by linarith)
  set φmin := psi β γ R₀ / cφ with hφmin
  have hφmin0 : 0 < φmin := div_pos hψR₀ hcφ
  set Smax := max 1 (c₄ / psi (1 + β) γ' R₁) with hSmax
  set K₁ := max (Cm * cφ ^ e + c₄ * κ ^ (-(1 + β)))
    ((Cm / φmin ^ e + Smax) * D₁ ^ (1 + β)) with hK₁
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * K₁ ^ p,
    by have : 0 < β / (1 - β) := div_pos hβ (by linarith)
       positivity, fun x y hxy => ?_⟩
  /- one pair -/
  set d := orbitDist ω x y with hd
  have hd2 : (2 : ℝ) ≤ d := hxy
  have hxy' : x ≠ y := by
    intro h; rw [h, hρ.self_eq] at hd; linarith
  have hφd : 0 < φ d := hφpos d (by linarith)
  set S := if R₁ ≤ κ * d then c₄ / psi (1 + β) γ' (κ * d) else 1 with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; split_ifs with h
    · exact div_nonneg hc₄ (psi_pos (by linarith)).le
    · exact zero_le_one
  have hfar : supNorm (farPart J (orbitDist ω) (β * d / (3 * (1 + β)))) ≤ ENNReal.ofReal S := by
    have e1 : β * d / (3 * (1 + β)) = κ * d := by rw [hκ]; ring
    rw [e1, hS]
    split_ifs with h
    · exact hfar2 _ h
    · rw [ENNReal.ofReal_one]; exact hfar1 _
  set K := Cm / φ d ^ e + S with hKdef
  have hK0 : 0 < K := by positivity
  /- `T ⩽ φ(d)` -/
  have hT : (C₀ / K) ^ (β / (1 + β)) ≤ φ d := by
    have h1 : C₀ / K ≤ φ d ^ e := by
      rw [div_le_iff₀ hK0]
      have : C₀ ≤ Cm := le_max_right _ _
      have h2 : Cm / φ d ^ e * φ d ^ e = Cm := div_mul_cancel₀ _ (by positivity)
      nlinarith [mul_nonneg hS0 (le_of_lt (Real.rpow_pos_of_pos hφd e))]
    calc (C₀ / K) ^ (β / (1 + β)) ≤ (φ d ^ e) ^ (β / (1 + β)) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = φ d := by
          rw [← Real.rpow_mul hφd.le]
          have : e * (β / (1 + β)) = 1 := by rw [he]; field_simp; ring
          rw [this, Real.rpow_one]
  /- the Green function bound in terms of `K` -/
  have hgreen := green_le_of_heat hJT hβ hβ2 hC₀ hK0 x y (fun t ht => hheat t ht x y)
    (fun t ht htT => by
      have h := hoff x y hxy' t ht (htT.trans hT)
      refine h.trans ?_
      have hmul : ENNReal.ofReal t * supNorm (farPart J (orbitDist ω) (β * d / (3 * (1 + β)))) ≤
          ENNReal.ofReal (t * S) := by
        rw [ENNReal.ofReal_mul ht.le]
        gcongr
      calc ENNReal.ofReal (CH * t / φ d ^ (1 + 1 / β)) +
            ENNReal.ofReal t * supNorm (farPart J (orbitDist ω) (β * d / (3 * (1 + β))))
          ≤ ENNReal.ofReal (CH * t / φ d ^ e) + ENNReal.ofReal (t * S) := add_le_add le_rfl hmul
        _ = ENNReal.ofReal (CH * t / φ d ^ e + t * S) :=
            (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ ≤ ENNReal.ofReal (K * t) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hKdef]
            have : CH ≤ Cm := le_max_left _ _
            have h1 : CH * t / φ d ^ e ≤ Cm * t / φ d ^ e :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this ht.le) (by positivity)
            have h2 : Cm * t / φ d ^ e = Cm / φ d ^ e * t := by ring
            nlinarith)
  refine hgreen.trans (ENNReal.ofReal_le_ofReal ?_)
  /- `K ⩽ K₁ d^{-1-β} (log₂ d)^{γ'}` -/
  have hℓ1 : 1 ≤ Real.logb 2 d := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]; simpa using hd2
  have hℓ0 : 0 < Real.logb 2 d := by linarith
  have hd0 : 0 < d := by linarith
  set B := d ^ (-1 - β) * Real.logb 2 d ^ γ' with hB
  have hB0 : 0 < B := by positivity
  have hγγ' : γ * e ≤ γ' := by
    rw [hγ, hγ', he, ha, ha']
    have h1 : ε' * (1 + 1 / β) ≤ ε' + 2 * A / D / β := by
      have : ε' / β ≤ (A / D) / β := div_le_div_of_nonneg_right hε'AD hβ.le
      have e1 : ε' * (1 + 1 / β) = ε' + ε' / β := by ring
      have e2 : (A : ℝ) / D / β ≤ 2 * A / D / β := by
        apply div_le_div_of_nonneg_right _ hβ.le
        rw [mul_div_assoc]; have : (0 : ℝ) ≤ A / D := by positivity
        linarith
      linarith
    have e3 : 2 * (A : ℝ) * (β - 1 / D) * (1 + 1 / β) =
        2 * A * (1 - 1 / D + β) - 2 * A / D / β := by field_simp; ring
    nlinarith
  have hKB : K ≤ K₁ * B := by
    by_cases hbig : D₁ ≤ d
    · have hdR₀ : R₀ ≤ d := le_trans (le_max_left _ _) hbig
      have hκd : R₁ ≤ κ * d := by
        have := le_trans (le_max_right R₀ (R₁ / κ)) hbig
        rw [div_le_iff₀ hκ0] at this; linarith
      have hSeq : S = c₄ / psi (1 + β) γ' (κ * d) := by rw [hS, if_pos hκd]
      -- the near term
      have hnear : Cm / φ d ^ e ≤ Cm * cφ ^ e * B := by
        have hψd : 0 < psi β γ d := psi_pos (by linarith)
        have e0 : Cm / φ d ^ e = Cm * cφ ^ e * (1 / psi β γ d ^ e) := by
          rw [hφeq d hdR₀, Real.div_rpow hψd.le hcφ.le, div_div_eq_mul_div]
          ring
        rw [e0]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [one_div_psi_rpow (by linarith : (1 : ℝ) < d), hB]
        have e1 : -(β * e) = -1 - β := by rw [he]; field_simp; ring
        rw [e1]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hℓ1 hγγ')
          (by positivity)
      -- the far term
      have hfarK : S ≤ c₄ * κ ^ (-(1 + β)) * B := by
        have hκd1 : 1 < κ * d := by linarith
        have e0 : S = c₄ * (1 / psi (1 + β) γ' (κ * d) ^ (1 : ℝ)) := by
          rw [hSeq, Real.rpow_one, div_eq_mul_one_div]
        rw [e0, one_div_psi_rpow hκd1, mul_one, mul_one, hB, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc₄
        have hκd0 : 0 < κ * d := by positivity
        have hℓκ : 0 < Real.logb 2 (κ * d) := Real.logb_pos one_lt_two (by linarith)
        have hℓle : Real.logb 2 (κ * d) ≤ Real.logb 2 d :=
          Real.logb_le_logb_of_le one_lt_two hκd0 (by nlinarith)
        rw [Real.mul_rpow hκ0.le hd0.le]
        have e1 : -(1 + β) = -1 - β := by ring
        rw [e1]
        have hγ'0 : 0 ≤ γ' := by positivity
        calc κ ^ (-1 - β) * d ^ (-1 - β) * Real.logb 2 (κ * d) ^ γ'
            ≤ κ ^ (-1 - β) * d ^ (-1 - β) * Real.logb 2 d ^ γ' :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hℓκ.le hℓle hγ'0) (by positivity)
          _ = _ := by ring
      calc K = Cm / φ d ^ e + S := rfl
        _ ≤ Cm * cφ ^ e * B + c₄ * κ ^ (-(1 + β)) * B := add_le_add hnear hfarK
        _ = (Cm * cφ ^ e + c₄ * κ ^ (-(1 + β))) * B := by ring
        _ ≤ K₁ * B := mul_le_mul_of_nonneg_right (le_max_left _ _) hB0.le
    · rw [not_le] at hbig
      have hnear : Cm / φ d ^ e ≤ Cm / φmin ^ e :=
        div_le_div_of_nonneg_left hCm0.le (by positivity)
          (Real.rpow_le_rpow hφmin0.le (hφlow d) he0.le)
      have hfarK : S ≤ Smax := by
        rw [hS]; split_ifs with h
        · refine le_trans ?_ (le_max_right _ _)
          exact div_le_div_of_nonneg_left hc₄ hψR₁ (hψmono' R₁ (κ * d) le_rfl h)
        · exact le_max_left _ _
      have hBlow : D₁ ^ (-(1 + β)) ≤ B := by
        rw [hB]
        have h1 : D₁ ^ (-(1 + β)) ≤ d ^ (-1 - β) := by
          have e1 : -1 - β = -(1 + β) := by ring
          rw [e1]
          exact Real.rpow_le_rpow_of_nonpos hd0 hbig.le (by linarith)
        have h2 : 1 ≤ Real.logb 2 d ^ γ' := Real.one_le_rpow hℓ1 (by positivity)
        nlinarith [Real.rpow_nonneg hd0.le (-1 - β)]
      have hD₁pos : 0 < D₁ := by linarith
      calc K = Cm / φ d ^ e + S := rfl
        _ ≤ Cm / φmin ^ e + Smax := add_le_add hnear hfarK
        _ = (Cm / φmin ^ e + Smax) * D₁ ^ (1 + β) * D₁ ^ (-(1 + β)) := by
            rw [mul_assoc, ← Real.rpow_add hD₁pos, add_neg_cancel, Real.rpow_zero, mul_one]
        _ ≤ (Cm / φmin ^ e + Smax) * D₁ ^ (1 + β) * B :=
            mul_le_mul_of_nonneg_left hBlow (by positivity)
        _ ≤ K₁ * B := mul_le_mul_of_nonneg_right (le_max_right _ _) hB0.le
  /- the exponents -/
  have hKp : K ^ p ≤ K₁ ^ p * B ^ p := by
    rw [← Real.mul_rpow hK₁0.le hB0.le]
    exact Real.rpow_le_rpow hK0.le hKB hp0.le
  have hBp : B ^ p ≤ (d / Real.logb 2 d ^ (2 * A)) ^ (β - 1) *
      Real.logb 2 d ^ (-((1 - β) / (1 + β) * (2 * (A : ℝ) / D - ε))) := by
    rw [hB, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hd0.le,
      ← Real.rpow_mul hℓ0.le, Real.div_rpow hd0.le (by positivity),
      ← Real.rpow_natCast (Real.logb 2 d) (2 * A), ← Real.rpow_mul hℓ0.le, div_eq_mul_inv,
      ← Real.rpow_neg hℓ0.le, mul_assoc, ← Real.rpow_add hℓ0]
    have e1 : (-1 - β) * p = β - 1 := by rw [hp]; field_simp; ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hℓ1 ?_) (by positivity)
    rw [hγ', ha', hp]
    push_cast
    have h1 : (1 - β) / (1 + β) * ε' ≤ (1 - β) / (1 + β) * ε :=
      mul_le_mul_of_nonneg_left hε'ε hp0.le
    have e2 : (2 * (A : ℝ) * (1 - 1 / D + β) + ε') * ((1 - β) / (1 + β)) =
        -(2 * A * (β - 1)) + -((1 - β) / (1 + β) * (2 * A / D - ε')) := by
      field_simp; ring
    rw [e2]
    have e3 : -((1 - β) / (1 + β) * (2 * A / D - ε')) =
        -((1 - β) / (1 + β) * (2 * A / D)) + (1 - β) / (1 + β) * ε' := by ring
    have e4 : -((1 - β) / (1 + β) * (2 * A / D - ε)) =
        -((1 - β) / (1 + β) * (2 * A / D)) + (1 - β) / (1 + β) * ε := by ring
    rw [e3, e4]
    linarith
  have hc5 : 0 ≤ C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) := by
    have : 0 < β / (1 - β) := div_pos hβ (by linarith)
    positivity
  calc C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * K ^ ((1 - β) / (1 + β))
      ≤ C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * (K₁ ^ p * B ^ p) :=
        mul_le_mul_of_nonneg_left hKp hc5
    _ ≤ C₀ ^ (2 * β / (1 + β)) * (1 / 2 + β / (1 - β)) * (K₁ ^ p *
          ((d / Real.logb 2 d ^ (2 * A)) ^ (β - 1) *
            Real.logb 2 d ^ (-((1 - β) / (1 + β) * (2 * (A : ℝ) / D - ε))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBp (by positivity)) hc5
    _ = _ := by ring
end
