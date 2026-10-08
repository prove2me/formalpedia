-- Prove2me | solution 1 for ErschlerZheng.hasNontrivialPoissonBoundary_muBeta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T10:10:12.211522+00:00
-- url     : https://prove2.me/submissions/dd3aee78-a841-483e-adf7-78c50cf3c702

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top
import Theorems.Thm_ErschlerZheng_green_orbitKernel_muBeta_le
import Theorems.Thm_ErschlerZheng_tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le
import Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
import Theorems.Thm_ErschlerZheng_isLevelTransitive_and_isotropy_grigorchuk
import Theorems.Thm_ErschlerZheng_isNondegenerate_muBeta

section
/-!
# The orbit chain `P_μ` and its step probabilities in `[0, ∞]` (helpers for B8)

`ofReal (P^{n+1}(y, x)) = Σ_g μ(g) ofReal (P^n(y·g, x))`, so `green` counts the expected visits of
`o·W_n`.
-/

open scoped RightActions ENNReal

namespace ErschlerZheng

namespace B8MarkovDev

open scoped Classical

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X]

theorem orbit_smul' {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, by rw [MulOpposite.op_mul, mul_smul]⟩

/-- `y·g` on the orbit. -/
def oact {G : Subgroup H} {o : X} (y : rightOrbit G o) (g : G) : rightOrbit G o :=
  ⟨(y : X) <• (g : H), orbit_smul' y.2 g.2⟩

theorem orbitKernel_nonneg (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) : 0 ≤ orbitKernel G μ o y z :=
  tsum_nonneg fun g => by split_ifs <;> simp [hμ.1 g]

theorem orbitKernel_summand_summable (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) :
    Summable fun g : G => if (y : X) <• (g : H) = z then μ g else 0 := by
  refine Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hμ.1 g]) (fun g => ?_)
    hμ.2.summable
  split_ifs
  · exact le_rfl
  · exact hμ.1 g

theorem ofReal_orbitKernel (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) :
    ENNReal.ofReal (orbitKernel G μ o y z) =
      ∑' g : G, if oact y g = z then ENNReal.ofReal (μ g) else 0 := by
  unfold orbitKernel
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => by split_ifs <;> simp [hμ.1 g])
    (orbitKernel_summand_summable G hμ o y z)]
  congr 1; funext g
  by_cases h : (y : X) <• (g : H) = z
  · have h' : oact y g = z := Subtype.ext h
    simp [h, h']
  · have h' : oact y g ≠ z := fun e => h (congrArg Subtype.val e)
    simp [h, h']

theorem tsum_ofReal_orbitKernel (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y : rightOrbit G o) : ∑' z, ENNReal.ofReal (orbitKernel G μ o y z) = 1 := by
  simp_rw [ofReal_orbitKernel G hμ o y]
  rw [ENNReal.tsum_comm]
  have : ∀ g : G, (∑' z : rightOrbit G o, if oact y g = z then ENNReal.ofReal (μ g) else 0) =
      ENNReal.ofReal (μ g) := fun g => by
    rw [tsum_eq_single (oact y g) (fun z hz => by rw [if_neg (Ne.symm hz)])]
    simp
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

variable [DecidableEq X]

/-- The step probabilities are in `[0, 1]` and satisfy the first-step recursion over `G`. -/
theorem stepProb_spec (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X) :
    ∀ n : ℕ, ∀ y x : rightOrbit G o,
      0 ≤ DurrettProbability.stepProb (orbitKernel G μ o) n y x ∧
        DurrettProbability.stepProb (orbitKernel G μ o) n y x ≤ 1 ∧
        ENNReal.ofReal (DurrettProbability.stepProb (orbitKernel G μ o) (n + 1) y x) =
          ∑' g : G, ENNReal.ofReal (μ g) *
            ENNReal.ofReal (DurrettProbability.stepProb (orbitKernel G μ o) n (oact y g) x) := by
  set P := orbitKernel G μ o
  have hPsum : ∀ y : rightOrbit G o, Summable fun z => P y z := by
    intro y
    have h := ENNReal.summable_toReal (f := fun z => ENNReal.ofReal (P y z))
      (by rw [tsum_ofReal_orbitKernel G hμ o y]; exact ENNReal.one_ne_top)
    exact h.congr fun z => ENNReal.toReal_ofReal (orbitKernel_nonneg G hμ o y z)
  -- the recursion, given bounds at level `n`
  have hrec : ∀ n : ℕ, (∀ z x : rightOrbit G o,
      0 ≤ DurrettProbability.stepProb P n z x ∧ DurrettProbability.stepProb P n z x ≤ 1) →
      ∀ y x : rightOrbit G o, ENNReal.ofReal (DurrettProbability.stepProb P (n + 1) y x) =
        ∑' g : G, ENNReal.ofReal (μ g) *
          ENNReal.ofReal (DurrettProbability.stepProb P n (oact y g) x) := by
    intro n hb y x
    show ENNReal.ofReal (∑' z, P y z * DurrettProbability.stepProb P n z x) = _
    have hsum : Summable fun z => P y z * DurrettProbability.stepProb P n z x := by
      refine Summable.of_nonneg_of_le
        (fun z => mul_nonneg (orbitKernel_nonneg G hμ o y z) (hb z x).1) (fun z => ?_) (hPsum y)
      calc P y z * DurrettProbability.stepProb P n z x ≤ P y z * 1 :=
            mul_le_mul_of_nonneg_left (hb z x).2 (orbitKernel_nonneg G hμ o y z)
        _ = P y z := mul_one _
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (orbitKernel_nonneg G hμ o y z) (hb z x).1) hsum]
    simp_rw [ENNReal.ofReal_mul (orbitKernel_nonneg G hμ o y _), ofReal_orbitKernel G hμ o y,
      ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; funext g
    rw [tsum_eq_single (oact y g) (fun z hz => by rw [if_neg (Ne.symm hz), zero_mul])]
    simp
  intro n
  induction n with
  | zero =>
    intro y x
    have hb : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P 0 z x ∧
        DurrettProbability.stepProb P 0 z x ≤ 1 := by
      intro z x
      simp only [DurrettProbability.stepProb]
      split_ifs <;> norm_num
    exact ⟨(hb y x).1, (hb y x).2, hrec 0 hb y x⟩
  | succ n ih =>
    have hb : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P (n + 1) z x ∧
        DurrettProbability.stepProb P (n + 1) z x ≤ 1 := by
      intro z x
      refine ⟨tsum_nonneg fun w => mul_nonneg (orbitKernel_nonneg G hμ o z w) (ih w x).1, ?_⟩
      have h1 := (ih z x).2.2
      have h2 : ∑' g : G, ENNReal.ofReal (μ g) *
          ENNReal.ofReal (DurrettProbability.stepProb P n (oact z g) x) ≤ 1 := by
        calc ∑' g : G, ENNReal.ofReal (μ g) *
              ENNReal.ofReal (DurrettProbability.stepProb P n (oact z g) x)
            ≤ ∑' g : G, ENNReal.ofReal (μ g) * 1 := by
              gcongr with g
              exact ENNReal.ofReal_le_one.mpr (ih _ x).2.1
          _ = 1 := by
              simp only [mul_one]
              rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq,
                ENNReal.ofReal_one]
      rw [← h1] at h2
      exact ENNReal.ofReal_le_one.mp h2
    have hb' : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P n z x ∧
        DurrettProbability.stepProb P n z x ≤ 1 := fun z x => ⟨(ih z x).1, (ih z x).2.1⟩
    intro y x
    exact ⟨(hb y x).1, (hb y x).2, hrec (n + 1) hb y x⟩

end B8MarkovDev

end ErschlerZheng
end

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mono (S : Set G) {m n : ℕ} (h : m ≤ n) : Chou.wordBall S m ⊆ Chou.wordBall S n :=
  fun _ ⟨l, hl, hls, he⟩ => ⟨l, le_trans hl h, hls, he⟩

theorem wordBall_mul_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S m * Chou.wordBall S n ⊆ Chou.wordBall S (m + n) := by
  rintro _ ⟨_, ⟨l, hl, hls, rfl⟩, _, ⟨l', hl', hls', rfl⟩, rfl⟩
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hls x h
  · exact hls' x h

theorem wordBall_add_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S (m + n) ⊆ Chou.wordBall S m * Chou.wordBall S n := by
  rintro _ ⟨l, hl, hls, rfl⟩
  refine ⟨(l.take m).prod, ⟨l.take m, by simp, fun x hx => hls x (List.mem_of_mem_take hx), rfl⟩,
    (l.drop m).prod, ⟨l.drop m, by simp; omega, fun x hx => hls x (List.mem_of_mem_drop hx), rfl⟩,
    ?_⟩
  show (l.take m).prod * (l.drop m).prod = l.prod
  rw [← List.prod_append, List.take_append_drop]

theorem one_mem_wordBall (S : Set G) (n : ℕ) : (1 : G) ∈ Chou.wordBall S n :=
  ⟨[], by simp, by simp, rfl⟩

theorem exists_mem_wordBall (S : Set G) (g : G) (hg : g ∈ Subgroup.closure S) :
    ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, hm⟩ := ihg
    obtain ⟨n, hn⟩ := ihh
    exact ⟨m + n, wordBall_mul_subset S m n ⟨g, hm, h, hn, rfl⟩⟩
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

/-- The letters: `1`, the elements of `S`, and their inverses. -/
def letters (S : Finset G) : Set G := insert 1 ((S : Set G) ∪ (S : Set G)⁻¹)

theorem letters_finite (S : Finset G) : (letters S).Finite :=
  ((S.finite_toSet.union S.finite_toSet.inv)).insert 1

theorem wordBall_one_subset (S : Finset G) : Chou.wordBall (S : Set G) 1 ⊆ letters S := by
  rintro _ ⟨l, hl, hls, rfl⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp [letters]
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rcases hls x (by simp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · simp at hl

theorem wordBall_finite (S : Finset G) (n : ℕ) : (Chou.wordBall (S : Set G) n).Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    rintro _ ⟨l, hl, -, rfl⟩
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    simp
  | succ n ih =>
    exact ((ih.mul (letters_finite S)).subset
      ((wordBall_add_subset _ n 1).trans (Set.mul_subset_mul_left (wordBall_one_subset S))))

end WordBallDev

end ErschlerZheng
end

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

theorem nil_smul (g : BinaryTreeAut) : ([] : List Bool) <• g = [] :=
  List.eq_nil_of_length_eq_zero (length_vertex_smul g [])

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_mul (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  apply sec_unique
  intro w
  rw [vertex_smul_mul, vertex_smul_mul, append_vertex_smul, append_vertex_smul,
    vertex_smul_mul]

theorem sec_nil (g : BinaryTreeAut) : sec g [] = g := by
  apply sec_unique
  intro w
  rw [nil_smul]
  rfl

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem sec_grigA (x : Bool) : sec grigA [x] = 1 := by
  apply sec_unique
  intro w
  rw [vertex_smul_grigA, vertex_smul_grigA]
  rfl

theorem sec_grigA_cons (x : Bool) (u : List Bool) : sec grigA (x :: u) = 1 := by
  rw [sec_cons, sec_grigA, sec_one]

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

theorem vertex_smul_gen (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    v <• gen ω γ = genFun ω γ v := by
  rw [vertex_smul_def, gen_inv]
  rfl

/-- The element `ω_0(γ) ∈ {a, id}`. -/
def letterElt (i : Fin 3) (γ : BCD) : BinaryTreeAut := if letterValue i γ then grigA else 1

theorem sec_gen_false (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [false] = letterElt (ω 0) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen]
  unfold letterElt
  by_cases h : letterValue (ω 0) γ
  · simp only [List.cons_append, List.nil_append, genFun, h, if_true]
    rw [vertex_smul_grigA]
    rfl
  · simp only [List.cons_append, List.nil_append, genFun, h]
    rfl

theorem sec_gen_true (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [true] = gen (shiftSeq ω 1) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen, vertex_smul_gen]
  simp [genFun]

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

theorem shiftSeq_zero (ω : ℕ → Fin 3) : shiftSeq ω 0 = ω := by
  funext j; simp [shiftSeq]

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

variable [DecidableEq X]

/-! ## The heat kernel -/

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

end Orbit

/-! ### The measures `υ_n` on `G_ω` -/

lemma upsilon_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    0 ≤ upsilon D ω k n g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `Σ_{g ∈ s} υ_n(e g) ⩽ 1` for an injective `e`. -/
lemma sum_upsilon_le {ι : Type*} (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ)
    (e : ι → BinaryTreeAut) (he : Function.Injective e) (s : Finset ι) :
    ∑ g ∈ s, upsilon D ω k n (e g) ≤ 1 := by
  classical
  unfold upsilon
  rw [← Finset.sum_div]
  by_cases h0 : Nat.card (LambdaN D ω k n) = 0
  · simp [h0]
  have hfin : Finite (LambdaN D ω k n) := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero h0)).2
  letI : Fintype (LambdaN D ω k n) := Fintype.ofFinite _
  have hpos : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.pos_of_ne_zero h0
  rw [div_le_one hpos]
  have key : ∑ g ∈ s, Nat.card {p : LambdaN D ω k n // theta D ω k n p = e g} ≤
      Nat.card (LambdaN D ω k n) := by
    simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_univ _
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpa hpb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpa hpb
      exact hab (he (hpa.symm.trans hpb))
  exact_mod_cast key

lemma upsilon_le_one (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    upsilon D ω k n g ≤ 1 := by
  have := sum_upsilon_le D ω k n (fun _ : Unit => g) (fun _ _ _ => rfl) {()}
  simpa using this

/-! ### `μ_β` dominates its `n`-th component -/

lemma rpow_neg_mul_eq (β : ℝ) (m : ℕ) : (2 : ℝ) ^ (-((m : ℝ) * β)) = ((2 : ℝ) ^ (-β)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

lemma summable_two_rpow (β : ℝ) (hβ : 0 < β) :
    Summable (fun m : ℕ => (2 : ℝ) ^ (-((m : ℝ) * β))) := by
  simp_rw [rpow_neg_mul_eq]
  exact summable_geometric_of_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

lemma summable_normSeries (D : ℕ) (β : ℝ) (hβ : 0 < β) :
    Summable (fun m : ℕ => if 1 ≤ m ∧ D ∣ m then (2 : ℝ) ^ (-((m : ℝ) * β)) else 0) :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
    (fun m => by split_ifs <;> [exact le_rfl; positivity]) (summable_two_rpow β hβ)

lemma normConst_pos (D : ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D) : 0 < normConst D β := by
  unfold normConst
  have : 0 < ∑' m : ℕ, if 1 ≤ m ∧ D ∣ m then (2 : ℝ) ^ (-((m : ℝ) * β)) else 0 :=
    (summable_normSeries D β hβ).tsum_pos (fun m => by split_ifs <;> positivity) D
      (by rw [if_pos ⟨hD, dvd_refl D⟩]; positivity)
  positivity

lemma summable_muBeta_series (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β)
    (hD : 1 ≤ D) (g : grigorchuk ω) :
    Summable (fun m : ℕ => if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0) := by
  have hC := (normConst_pos D β hβ hD).le
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((summable_two_rpow β hβ).mul_left (normConst D β * 2))
  · split_ifs
    · exact mul_nonneg (mul_nonneg hC (by positivity))
        (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
    · exact le_rfl
  · split_ifs
    · have h1 := upsilon_le_one D ω k m g
      have h2 := upsilon_le_one D ω k m (g : BinaryTreeAut)⁻¹
      have h0 : 0 ≤ normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) := mul_nonneg hC (by positivity)
      unfold upsilonCheck
      calc normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
            (upsilon D ω k m g + upsilon D ω k m (g : BinaryTreeAut)⁻¹)
          ≤ normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) h0
        _ = normConst D β * 2 * (2 : ℝ) ^ (-((m : ℝ) * β)) := by ring
    · positivity

/-! ### Symmetry of `μ_β` and the parameters (after prover 5's `P5Goal`) -/

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

/-- `ψ(r) = r^a (log₂ r)^{-γ}`. -/
noncomputable def psi (a γ r : ℝ) : ℝ := r ^ a * Real.logb 2 r ^ (-γ)

lemma psi_pos {a γ r : ℝ} (hr : 1 < r) : 0 < psi a γ r := by
  unfold psi
  have := Real.logb_pos one_lt_two hr
  have : 0 < r := by linarith
  positivity

end P6Dev

end ErschlerZheng
end

section
/-!
# Helpers for Theorem 7.13 (prover 7)

* Orbit chains: `P^m(w, z) P^n(z, x) ⩽ P^{m+n}(w, x)`, so `P^m(w, z) G(z, x) ⩽ G(w, x)`; for a
  non-degenerate step law every orbit point reaches every other with positive probability.
  Hence one finite value `G(w, x)` makes `G(z, x)` finite for every `z`.
* The Schreier ball of radius `1` in the orbit `1^∞·G_ω` is finite and the orbit is infinite, so
  every orbit point has a point at Schreier distance `⩾ 2`.
* The comparison function `f̃(s) = K / ψ(max(s, R₀))`, `ψ(r) = r^{1-β}(log₂ r)^{-a'}`, satisfies
  the hypotheses of Proposition 7.12 with `D' = 1/(1-β)` and dominates Proposition 7.11's bound.
-/

open scoped RightActions ENNReal
open DurrettProbability

namespace ErschlerZheng

namespace P7Dev

set_option linter.unusedSectionVars false

open B8MarkovDev

section Markov

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X] [DecidableEq X]

theorem stepProb_mul_le (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X) :
    ∀ (m n : ℕ) (y z x : rightOrbit G o),
      ENNReal.ofReal (stepProb (orbitKernel G μ o) m y z) *
          ENNReal.ofReal (stepProb (orbitKernel G μ o) n z x) ≤
        ENNReal.ofReal (stepProb (orbitKernel G μ o) (m + n) y x)
  | 0, n, y, z, x => by
    by_cases h : y = z
    · subst h; simp [stepProb]
    · simp [stepProb, h]
  | m + 1, n, y, z, x => by
    have hs := stepProb_spec G hμ o
    rw [(hs m y z).2.2, show m + 1 + n = (m + n) + 1 by ring, (hs (m + n) y x).2.2,
      ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun g => ?_
    rw [mul_assoc]
    gcongr
    exact stepProb_mul_le G hμ o m n _ z x

theorem stepProb_one_ge (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y : rightOrbit G o) (g : G) :
    ENNReal.ofReal (μ g) ≤ ENNReal.ofReal (stepProb (orbitKernel G μ o) 1 y (oact y g)) := by
  rw [(stepProb_spec G hμ o 0 y (oact y g)).2.2]
  refine le_trans ?_ (ENNReal.le_tsum g)
  simp [stepProb]

theorem oact_oact {G : Subgroup H} {o : X} (y : rightOrbit G o) (a b : G) :
    oact (oact y a) b = oact y (a * b) := by
  apply Subtype.ext
  show ((y : X) <• (a : H)) <• (b : H) = (y : X) <• ((a * b : G) : H)
  rw [Subgroup.coe_mul, MulOpposite.op_mul, mul_smul]

theorem exists_stepProb_pos (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ)
    (hnd : IsNondegenerate μ) (o : X) (g : G) :
    ∀ y : rightOrbit G o, ∃ m, 0 < ENNReal.ofReal (stepProb (orbitKernel G μ o) m y (oact y g)) := by
  have hg : g ∈ Subsemigroup.closure {g | μ g ≠ 0} := by
    unfold IsNondegenerate at hnd
    rw [hnd]; exact Subsemigroup.mem_top g
  induction hg using Subsemigroup.closure_induction with
  | mem s hs =>
    intro y
    refine ⟨1, lt_of_lt_of_le ?_ (stepProb_one_ge G hμ o y s)⟩
    exact ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hμ.1 s) (Ne.symm hs))
  | mul a b _ _ iha ihb =>
    intro y
    obtain ⟨m, hm⟩ := iha y
    obtain ⟨n, hn⟩ := ihb (oact y a)
    rw [oact_oact] at hn
    refine ⟨m + n, lt_of_lt_of_le ?_ (stepProb_mul_le G hμ o m n y (oact y a) _)⟩
    exact ENNReal.mul_pos hm.ne' hn.ne'

theorem stepProb_mul_green_le (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (m : ℕ) (w z x : rightOrbit G o) :
    ENNReal.ofReal (stepProb (orbitKernel G μ o) m w z) *
        MarkovChain.green (orbitKernel G μ o) z x ≤
      MarkovChain.green (orbitKernel G μ o) w x := by
  unfold MarkovChain.green
  rw [← ENNReal.tsum_mul_left]
  calc _ ≤ ∑' n, ENNReal.ofReal (stepProb (orbitKernel G μ o) (m + n) w x) :=
        ENNReal.tsum_le_tsum fun n => stepProb_mul_le G hμ o m n w z x
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective m)
        (fun n => ENNReal.ofReal (stepProb (orbitKernel G μ o) n w x))

/-- One finite Green value `G(w, x)` makes `G(z, x)` finite for every orbit point `z`. -/
theorem green_lt_top_of (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ)
    (hnd : IsNondegenerate μ) (o : X) (w z x : rightOrbit G o)
    (hw : MarkovChain.green (orbitKernel G μ o) w x < ⊤) :
    MarkovChain.green (orbitKernel G μ o) z x < ⊤ := by
  -- `z = w·g` for some `g ∈ G`
  obtain ⟨kw, hkw, ew⟩ := w.2
  obtain ⟨kz, hkz, ez⟩ := z.2
  set g : G := ⟨kw⁻¹ * kz, G.mul_mem (G.inv_mem hkw) hkz⟩
  have hz : oact w g = z := by
    apply Subtype.ext
    show (w : X) <• (kw⁻¹ * kz) = z
    rw [ew, ez, op_smul_op_smul, mul_inv_cancel_left]
  obtain ⟨m, hm⟩ := exists_stepProb_pos G hμ hnd o g w
  rw [hz] at hm
  have hle := stepProb_mul_green_le G hμ o m w z x
  by_contra htop
  rw [not_lt_top_iff] at htop
  rw [htop, ENNReal.mul_top hm.ne'] at hle
  exact absurd (lt_of_le_of_lt hle hw) (lt_irrefl _)

end Markov

/-! ### The Schreier ball of radius 1 is finite; the orbit is infinite -/

open WordBallDev in
theorem mem_image_of_schreierDist_le (ω : ℕ → Fin 3) {x w : Ray}
    (hxw : ∃ g ∈ grigorchuk ω, w = x <• g) (h : schreierDist ω x w ≤ 1) :
    w ∈ (fun g => x <• g) '' Chou.wordBall (gens ω) 1 := by
  obtain ⟨g, hg, rfl⟩ := hxw
  obtain ⟨n, hn⟩ := exists_mem_wordBall (gens ω) g hg
  have hne : {n | ∃ g' ∈ Chou.wordBall (gens ω) n, x <• g = x <• g'}.Nonempty := ⟨n, g, hn, rfl⟩
  obtain ⟨g', hg', he⟩ := Nat.sInf_mem hne
  exact ⟨g', wordBall_mono _ h hg', he.symm⟩

open WordBallDev in
theorem wordBall_one_finite (ω : ℕ → Fin 3) : (Chou.wordBall (gens ω) 1).Finite := by
  have := wordBall_finite (P6Dev.gens_finite ω).toFinset 1
  rwa [Set.Finite.coe_toFinset] at this

theorem orbit_rel (ω : ℕ → Fin 3) (x w : orbitOne ω) :
    ∃ g ∈ grigorchuk ω, (w : Ray) = (x : Ray) <• g := by
  obtain ⟨kx, hkx, ex⟩ := x.2
  obtain ⟨kw, hkw, ew⟩ := w.2
  refine ⟨kx⁻¹ * kw, (grigorchuk ω).mul_mem ((grigorchuk ω).inv_mem hkx) hkw, ?_⟩
  rw [ex, ew, op_smul_op_smul, mul_inv_cancel_left]

/-- The points of the orbit at Schreier distance `⩽ 1` from `x` (in either order) are finitely
many. -/
theorem finite_near (ω : ℕ → Fin 3) (x : orbitOne ω) :
    {w : orbitOne ω | schreierDist ω x w ≤ 1}.Finite ∧
      {w : orbitOne ω | schreierDist ω w x ≤ 1}.Finite := by
  constructor
  · refine ((wordBall_one_finite ω).image (fun g => (x : Ray) <• g)).preimage
      Subtype.val_injective.injOn |>.subset fun w hw => ?_
    exact mem_image_of_schreierDist_le ω (orbit_rel ω x w) hw
  · refine ((wordBall_one_finite ω).image (fun g => (x : Ray) <• g⁻¹)).preimage
      Subtype.val_injective.injOn |>.subset fun w hw => ?_
    obtain ⟨g, hg, e⟩ := mem_image_of_schreierDist_le ω (orbit_rel ω w x) hw
    refine ⟨g, hg, ?_⟩
    show (x : Ray) <• g⁻¹ = w
    rw [← e, ← mul_smul, ← MulOpposite.op_mul, mul_inv_cancel, MulOpposite.op_one, one_smul]

theorem infinite_orbitOne (ω : ℕ → Fin 3) : Infinite (orbitOne ω) := by
  have hA2 := ((isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary).2.1 ω oneRay).1
  let e : ℕ → orbitOne ω := fun k => ⟨fun i => decide (i ≠ k), by
    show _ ∈ rightOrbit (grigorchuk ω) oneRay
    rw [hA2]
    exact Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => by
      simp only [oneRay, decide_eq_true_eq]; omega⟩⟩
  refine Infinite.of_injective e fun a b hab => ?_
  have := congrFun (congrArg Subtype.val hab) a
  simp only [e, ne_eq, not_true_eq_false, decide_false] at this
  by_contra h
  simp [h] at this

theorem exists_far (ω : ℕ → Fin 3) (x : orbitOne ω) :
    ∃ w : orbitOne ω, 2 ≤ schreierDist ω w x := by
  have := infinite_orbitOne ω
  obtain ⟨w, hw⟩ := (finite_near ω x).2.exists_notMem
  exact ⟨w, by simp only [Set.mem_ofPred_eq, not_le] at hw; omega⟩

/-! ### The comparison function -/

/-- `f̃(s) = K / ψ_{t, a'}(max(s, R₀))`, `ψ_{t,a'}(r) = r^t (log₂ r)^{-a'}`. -/
noncomputable def ftil (K t a' R₀ : ℝ) (s : ℝ) : ℝ := K / P6Dev.psi t a' (max s R₀)

section Ftil

variable {K t a' R₀ : ℝ} (hK : 0 < K) (ht : 0 < t) (ha : 0 ≤ a') (hR : 4 ≤ R₀)
  (hRa : a' ≤ t * Real.log R₀)
include hK ht ha hR hRa

theorem ftil_pos (s : ℝ) : 0 < ftil K t a' R₀ s :=
  div_pos hK (P6Dev.psi_pos (by linarith [le_max_right s R₀]))

theorem psi_le_psi {u v : ℝ} (hu : R₀ ≤ u) (huv : u ≤ v) :
    P6Dev.psi t a' u ≤ P6Dev.psi t a' v :=
  P6Dev.psi_mono ht ha (by linarith) hRa hu huv

theorem ftil_antitone : AntitoneOn (ftil K t a' R₀) (Set.Ici 0) := by
  intro s _ u _ hsu
  unfold ftil
  exact div_le_div_of_nonneg_left hK.le (P6Dev.psi_pos (by linarith [le_max_right s R₀]))
    (psi_le_psi hK ht ha hR hRa (le_max_right _ _) (max_le_max hsu le_rfl))

theorem ftil_ratio (s : ℝ) (hs : 1 ≤ s) :
    (2 : ℝ) ^ (-t) ≤ ftil K t a' R₀ (2 * s) / ftil K t a' R₀ s := by
  set u := max s R₀
  set v := max (2 * s) R₀
  have hu4 : 4 ≤ u := le_trans hR (le_max_right _ _)
  have huv : u ≤ v := max_le_max (by linarith) le_rfl
  have hv2 : v ≤ 2 * u := max_le (by linarith [le_max_left s R₀]) (by linarith [le_max_right s R₀])
  have hpu := P6Dev.psi_pos (a := t) (γ := a') (show 1 < u by linarith)
  have hpv := P6Dev.psi_pos (a := t) (γ := a') (show 1 < v by linarith)
  have hLu : 0 < Real.logb 2 u := Real.logb_pos one_lt_two (by linarith)
  have hLuv : Real.logb 2 u ≤ Real.logb 2 v := Real.logb_le_logb_of_le one_lt_two (by linarith) huv
  have key : P6Dev.psi t a' v ≤ 2 ^ t * P6Dev.psi t a' u := by
    unfold P6Dev.psi
    calc v ^ t * Real.logb 2 v ^ (-a') ≤ (2 * u) ^ t * Real.logb 2 u ^ (-a') :=
          mul_le_mul (Real.rpow_le_rpow (by linarith) hv2 ht.le)
            (Real.rpow_le_rpow_of_nonpos hLu hLuv (by linarith))
            (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
      _ = 2 ^ t * (u ^ t * Real.logb 2 u ^ (-a')) := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
  unfold ftil
  rw [div_div_div_cancel_left' _ _ hK.ne', le_div_iff₀ hpv]
  calc (2 : ℝ) ^ (-t) * P6Dev.psi t a' v ≤ 2 ^ (-t) * (2 ^ t * P6Dev.psi t a' u) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = P6Dev.psi t a' u := by
        rw [← mul_assoc, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_mul]

end Ftil

/-- Proposition 7.11's bound rewritten: `C (d/L^{2A})^{β-1} L^{-e} = C d^{β-1} L^{2A(1-β)-e}`. -/
theorem bound_eq (C β e d : ℝ) (A : ℕ) (hd : 1 < d) :
    C * (d / Real.logb 2 d ^ (2 * A)) ^ (β - 1) * Real.logb 2 d ^ (-e) =
      C * (d ^ (β - 1) * Real.logb 2 d ^ (2 * A * (1 - β) - e)) := by
  have hL : 0 < Real.logb 2 d := Real.logb_pos one_lt_two hd
  rw [Real.div_rpow (by linarith) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
    div_eq_mul_inv, ← Real.rpow_neg hL.le, mul_assoc, mul_assoc, ← Real.rpow_add hL]
  congr 3
  push_cast; ring

theorem div_psi_eq (K t a' r : ℝ) (hr : 1 < r) :
    K / P6Dev.psi t a' r = K * ((r ^ t)⁻¹ * Real.logb 2 r ^ a') := by
  have hL : 0 < Real.logb 2 r := Real.logb_pos one_lt_two hr
  unfold P6Dev.psi
  rw [Real.rpow_neg (x := Real.logb 2 r) hL.le, div_eq_mul_inv, mul_inv, inv_inv]

/-- `f̃` dominates Proposition 7.11's bound at every `d ⩾ 2`. -/
theorem bound_le_ftil {C β t a' R₀ e : ℝ} (A : ℕ) (hC : 0 < C) (htβ : t = 1 - β) (ht : 0 < t)
    (ha : 0 ≤ a') (hR : 4 ≤ R₀) (he : a' = 2 * A * t - e) (d : ℝ) (hd : 2 ≤ d) :
    C * (d / Real.logb 2 d ^ (2 * A)) ^ (β - 1) * Real.logb 2 d ^ (-e) ≤
      ftil (C * R₀ ^ t) t a' R₀ d := by
  have hd1 : 1 < d := by linarith
  have hL : 0 < Real.logb 2 d := Real.logb_pos one_lt_two hd1
  rw [bound_eq C β e d A hd1, show 2 * (A : ℝ) * (1 - β) - e = a' by rw [he, htβ],
    show β - 1 = -t by rw [htβ]; ring, Real.rpow_neg (by linarith)]
  unfold ftil
  have hR1 : (1 : ℝ) ≤ R₀ ^ t := Real.one_le_rpow (by linarith) ht.le
  rcases le_or_gt R₀ d with hdR | hdR
  · rw [max_eq_left hdR, div_psi_eq _ _ _ _ hd1]
    have hX : 0 ≤ (d ^ t)⁻¹ * Real.logb 2 d ^ a' := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le hR1) hX |>.trans_eq'
      (by ring) |>.trans (le_of_eq (by ring))
  · rw [max_eq_right hdR.le, div_psi_eq _ _ _ _ (by linarith)]
    have hRt : 0 < R₀ ^ t := by positivity
    have e1 : C * R₀ ^ t * ((R₀ ^ t)⁻¹ * Real.logb 2 R₀ ^ a') = C * Real.logb 2 R₀ ^ a' := by
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h1 : (d ^ t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hd1.le ht.le)
    have h2 : Real.logb 2 d ^ a' ≤ Real.logb 2 R₀ ^ a' :=
      Real.rpow_le_rpow hL.le (Real.logb_le_logb_of_le one_lt_two (by linarith) hdR.le) ha
    calc (d ^ t)⁻¹ * Real.logb 2 d ^ a' ≤ 1 * Real.logb 2 R₀ ^ a' :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _

/-- The `n`-th term of the series of p. 44 is `O(n^{-e})`. -/
theorem term_le {β t a' e : ℝ} (A n : ℕ) (hn : 1 ≤ n) (htβ : t = 1 - β) (ht : 0 < t)
    (ha : 0 ≤ a') (he : a' = 2 * A * t - e) :
    (2 : ℝ) ^ (-((n : ℝ) * β)) * 2 ^ n * (P6Dev.psi t a' (2 ^ (n + 2 * kLog A n)))⁻¹ ≤
      (2 : ℝ) ^ (2 * A * t) * (1 + 2 * A) ^ a' * (n : ℝ) ^ (-e) := by
  set L := Nat.log 2 n
  set m := n + 2 * kLog A n with hm
  have hm' : (m : ℝ) = n + 2 * A * L := by simp [hm, kLog, L]; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by rw [hm']; positivity
  have hlog : Real.logb 2 ((2 : ℝ) ^ m) = m := by
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have hpsi : (P6Dev.psi t a' (2 ^ m))⁻¹ = (2 : ℝ) ^ (-((m : ℝ) * t)) * (m : ℝ) ^ a' := by
    unfold P6Dev.psi
    rw [hlog, mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg
      (by norm_num), ← Real.rpow_neg hm0.le, neg_neg]
  rw [hpsi, ← Real.rpow_natCast (2 : ℝ) n, ← mul_assoc, ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]
  -- the power of two
  have hexp : -((n : ℝ) * β) + n + -((m : ℝ) * t) = -(2 * A * t * L) := by
    rw [hm', htβ]; ring
  rw [hexp]
  have hnL : (n : ℝ) ≤ 2 ^ ((L : ℝ) + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast]
    exact_mod_cast (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n).le
  have h2 : (2 : ℝ) ^ (-(2 * A * t * L)) ≤ 2 ^ (2 * A * t) * (n : ℝ) ^ (-(2 * A * t)) := by
    have hA0 : 0 ≤ 2 * (A : ℝ) * t := by positivity
    have := Real.rpow_le_rpow_of_nonpos hn0 hnL (show -(2 * (A : ℝ) * t) ≤ 0 by linarith)
    rw [← Real.rpow_mul (by norm_num)] at this
    calc (2 : ℝ) ^ (-(2 * A * t * L)) = 2 ^ (2 * A * t) * 2 ^ ((L + 1) * -(2 * A * t)) := by
          rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hmle : (m : ℝ) ≤ (1 + 2 * A) * n := by
    rw [hm']
    have : (L : ℝ) ≤ n := by exact_mod_cast (Nat.log_lt_self 2 (by omega)).le
    nlinarith [show (0 : ℝ) ≤ A by positivity]
  have h3 : (m : ℝ) ^ a' ≤ (1 + 2 * A) ^ a' * (n : ℝ) ^ a' := by
    rw [← Real.mul_rpow (by positivity) hn0.le]
    exact Real.rpow_le_rpow hm0.le hmle ha
  calc (2 : ℝ) ^ (-(2 * A * t * L)) * (m : ℝ) ^ a' ≤
        (2 ^ (2 * A * t) * (n : ℝ) ^ (-(2 * A * t))) * ((1 + 2 * A) ^ a' * (n : ℝ) ^ a') :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = 2 ^ (2 * A * t) * (1 + 2 * A) ^ a' * ((n : ℝ) ^ (-(2 * A * t)) * (n : ℝ) ^ a') := by ring
    _ = _ := by rw [← Real.rpow_add hn0, he]; congr 2; ring

end P7Dev

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

theorem ray_ext {x y : Ray} (h : ∀ n, rayPrefix x n = rayPrefix y n) : x = y := by
  funext i
  have hx : i < (rayPrefix x (i + 1)).length := by simp [length_rayPrefix]
  rw [← getElem_rayPrefix x (i + 1) i hx, List.getElem_of_eq (h (i + 1)), getElem_rayPrefix]

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

theorem shiftRay_smul (g : BinaryTreeAut) (x : Ray) (n : ℕ) :
    shiftRay (x <• g) n = shiftRay x n <• sec g (rayPrefix x n) := by
  apply ray_ext
  intro m
  have h1 : rayPrefix (x <• g) (n + m) =
      (rayPrefix x n <• g) ++ (rayPrefix (shiftRay x n) m <• sec g (rayPrefix x n)) := by
    rw [rayPrefix_smul, rayPrefix_add, append_vertex_smul]
  have h2 : rayPrefix (x <• g) (n + m) =
      rayPrefix (x <• g) n ++ rayPrefix (shiftRay (x <• g) n) m := rayPrefix_add _ _ _
  rw [h2, rayPrefix_smul] at h1
  rw [rayPrefix_smul]
  exact List.append_cancel_left h1

/-- `x = x_1 … x_n (𝔰ⁿ x)`. -/
theorem prepend_rayPrefix_shiftRay (x : Ray) (n : ℕ) : prepend (rayPrefix x n) (shiftRay x n) = x := by
  funext i
  unfold prepend
  split_ifs with h
  · rw [getElem_rayPrefix]
  · simp only [shiftRay, length_rayPrefix] at h ⊢
    congr 1; omega

theorem rayPrefix_prepend (u : List Bool) (x : Ray) :
    rayPrefix (prepend u x) u.length = u := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp [prepend, h2]

theorem shiftRay_prepend (u : List Bool) (x : Ray) : shiftRay (prepend u x) u.length = x := by
  funext i
  simp [shiftRay, prepend]

/-- `(v x')·g = (v·g)(x'·g_v)`. -/
theorem prepend_smul (g : BinaryTreeAut) (v : List Bool) (x : Ray) :
    prepend v x <• g = prepend (v <• g) (x <• sec g v) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay (prepend v x <• g) v.length]
  rw [rayPrefix_smul, shiftRay_smul, rayPrefix_prepend, shiftRay_prepend]

theorem one_smul_ray (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul _ x

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

theorem sec_gen_cons_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (true :: u) = sec (gen (shiftSeq ω 1) γ) u := by
  rw [sec_cons, sec_gen_true]

theorem sec_gen_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) (hz : z ≠ []) :
    sec (gen ω γ) (List.replicate k true ++ false :: z) = 1 := by
  induction k generalizing ω with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [sec_cons, sec_gen_false]
    obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hz
    unfold letterElt
    split_ifs
    · exact sec_grigA_cons c z'
    · exact sec_one _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sec_gen_cons_true, ih]

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

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

/-! ### Generators on rays that are eventually all ones -/

theorem genFun_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    genFun ω γ (List.replicate n true) = List.replicate n true := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, genFun, ih]

theorem oneRay_smul_gen (ω : ℕ → Fin 3) (γ : BCD) : oneRay <• gen ω γ = oneRay := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, rayPrefix_oneRay, vertex_smul_gen, genFun_replicate_true]

end SchreierDev

end ErschlerZheng
end

section
/-!
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_eq_iff {x : X} {h h' : H} (hh : x <• h = x) (hh' : x <• h' = x) :
    germ x h = germ x h' ↔ GermEq x h h' := by
  rw [germ_def hh, germ_def hh', QuotientGroup.eq]
  change GermEq x (h⁻¹ * h') 1 ↔ GermEq x h h'
  constructor
  · intro e
    have := germEq_comp (germEq_refl x h) (by rw [hh]; exact e)
    rw [mul_inv_cancel_left, mul_one] at this
    exact GermEq.symm' this
  · intro e
    have := germEq_comp (germEq_refl x h⁻¹) (by rw [rsmul_inv_eq hh]; exact e)
    rw [inv_mul_cancel] at this
    exact GermEq.symm' this

theorem conj_fix {o x : X} {σ h : H} (hσ : o <• σ = x) (hh : x <• h = x) :
    o <• (σ * h * σ⁻¹) = o := by
  rw [rsmul_mul, rsmul_mul, hσ, hh, ← hσ, rsmul_inv_smul]

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

theorem exists_L_of_mem {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : ∃ σ ∈ L, x <• σ = x <• g := by
  have : x <• g ∈ rightOrbit L x := by
    rw [hL.1 x]; exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem exists_L_of_orbit {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X}
    (hx : x ∈ rightOrbit G o) : ∃ σ ∈ L, o <• σ = x := by
  have : x ∈ rightOrbit L o := by rw [hL.1 o]; exact hx
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

end GermBase

end ErschlerZheng
end

section
/-!
# Germs of `G_ω` read from sections along the ray (helpers for B3, B4)

For `k ∈ G_ω ⊔ L` and a ray `x` cofinal with `1^∞`, the sections of `k` along `x` are eventually
the sections along `1^∞` of an element `c ∈ {1, b_ω, c_ω, d_ω}`, i.e. `1` or `γ_{𝔰ⁿω}`; along a ray
not cofinal with `1^∞` they are eventually trivial. Two elements fixing `x` have the same germ at
`x` iff their sections along `x` eventually agree. Orbits and the finitary group come from A2.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ErschlerZheng

namespace GrigGermsDev

open GrigBasic RayBasic GrayDev SchreierDev GermBase

/-! ### Cylinders -/

theorem eventually_rayPrefix_eq (x : Ray) (n : ℕ) :
    ∀ᶠ y in nhds x, rayPrefix y n = rayPrefix x n := by
  have : ∀ᶠ y in nhds x, ∀ i : Fin n, y i = x i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply (i : ℕ)).continuousAt (x := x)
      ((isOpen_discrete {x i}).mem_nhds rfl)
  filter_upwards [this] with y hy
  simp only [rayPrefix]
  congr 1
  funext i
  exact hy i

theorem cyl_smul (k : BinaryTreeAut) (x y : Ray) (n : ℕ) (hy : rayPrefix y n = rayPrefix x n) :
    y <• k = prepend (rayPrefix x n <• k) (shiftRay y n <• sec k (rayPrefix x n)) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay y n]
  rw [hy, prepend_smul]

theorem germEq_of_sec {x : Ray} {k k' : BinaryTreeAut} {n : ℕ}
    (hv : rayPrefix x n <• k = rayPrefix x n <• k')
    (hs : sec k (rayPrefix x n) = sec k' (rayPrefix x n)) : GermEq x k k' := by
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  rw [cyl_smul k x y n hy, cyl_smul k' x y n hy, hv, hs]

/-! ### The set `V = {1, b_ω, c_ω, d_ω}` -/

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Cofinality classes are preserved (A2) -/

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

theorem mem_GL_of_L {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ finitary) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_right : finitary ≤ _) hg

/-! ### Eventual sections -/

theorem first_zero (x : Ray) (hx : ∃ k, x k = false) :
    ∃ k, x k = false ∧ ∀ j < k, x j = true := by
  classical
  exact ⟨Nat.find hx, Nat.find_spec hx, fun j hj => by simpa using Nat.find_min hx hj⟩

theorem rayPrefix_first_zero' (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true) :
    rayPrefix x (k + 1) = List.replicate k true ++ [false] := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp only [length_rayPrefix] at h1
    by_cases hi : i < k
    · rw [List.getElem_append_left (by simpa using hi)]; simp [hmin i hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      have : i = k := by omega
      subst this; simp [hk]

theorem rayPrefix_first_zero (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true)
    (n : ℕ) (hn : k + 2 ≤ n) :
    ∃ z : List Bool, z ≠ [] ∧ rayPrefix x n = List.replicate k true ++ false :: z := by
  refine ⟨rayPrefix (shiftRay x (k + 1)) (n - (k + 1)), ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp [length_rayPrefix] at this
    omega
  · rw [show n = (k + 1) + (n - (k + 1)) by omega, rayPrefix_add, rayPrefix_first_zero' x k hk hmin]
    simp [show k + 1 + (n - (k + 1)) - (k + 1) = n - (k + 1) by omega]

end GrigGermsDev

end ErschlerZheng
end

section
/-!
# B3: Example 3.2 (p. 18)

Germs of `G_ω` at a ray `x` are read from the sections along `x`: two elements fixing `x` have the
same germ iff their sections along `x` eventually agree (`GrigGermsDev`). Along a ray not cofinal
with `1^∞` the sections are eventually trivial; along a cofinal ray they are eventually `1` or
`γ_{𝔰ⁿω}`. Orbits and level transitivity come from A2 and the Gray-code path.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B3Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev

theorem germ_eq_of_sec' {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    {N : ℕ} (h : ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n)) :
    germ x k = germ x k' := by
  rw [germ_eq_iff hk hk']
  refine germEq_of_sec (n := N) ?_ (h N le_rfl)
  rw [← rayPrefix_smul, ← rayPrefix_smul, hk, hk']

theorem one_fix (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul_ray x

end B3Dev

end ErschlerZheng
end

section
/-!
# B4: germs read from sections (p. 42, the general-`ω` Fact 4.1)

`(g, x) ∈ ℋ^b` iff the sections of `g` along `x` are eventually `1` or `b_{𝔰ⁿω}` (conjugating by
the finitary transports changes no deep section). If every level-`n` section is in
`{1, a, b_{𝔰ⁿω}}`, that holds along every cofinal ray. Conversely the "bad" vertices (section not
in `{1, a, b_{𝔰^{|v|}ω}}`) form a subtree; if it were infinite, compactness of `∂T` would give a ray
along which every section is bad, while along every ray the sections are eventually good.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B4Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev

theorem sec_gen_along (ω' : ℕ → Fin 3) (γ : BCD) (y : Ray) :
    (∃ N, ∀ m ≥ N, sec (gen ω' γ) (rayPrefix y m) = 1) ∨ y = oneRay := by
  by_cases hz : ∃ k, y k = false
  · left
    obtain ⟨k, hk, hmin⟩ := first_zero y hz
    refine ⟨k + 2, fun m hm => ?_⟩
    obtain ⟨z, hz, e⟩ := rayPrefix_first_zero y k hk hmin m hm
    rw [e, sec_gen_replicate ω' γ k z hz]
  · right
    push Not at hz
    exact funext fun k => by simpa [oneRay] using hz k

/-- Conjugating by a finitary transport does not change deep sections. -/
theorem sec_conj_L {σ k : BinaryTreeAut} (hσ : σ ∈ finitary) {x : Ray} (hσx : oneRay <• σ = x)
    (hk : x <• k = x) :
    ∃ N, ∀ n ≥ N, sec (σ * k * σ⁻¹) (List.replicate n true) = sec k (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := hσ
  refine ⟨m, fun n hn => ?_⟩
  have h1 : sec σ (List.replicate n true) = 1 :=
    sec_eq_one_of_le σ hn hm _ (List.length_replicate)
  have hp : List.replicate n true <• σ = rayPrefix x n := by
    rw [← rayPrefix_oneRay, ← rayPrefix_smul, hσx]
  have hpk : rayPrefix x n <• k = rayPrefix x n := by rw [← rayPrefix_smul, hk]
  have hpσ : rayPrefix x n <• σ⁻¹ = List.replicate n true := by
    rw [← hp, vertex_smul_smul_inv]
  rw [sec_mul, sec_mul, hp, vertex_smul_mul, hp, hpk, sec_inv, hpσ, h1, inv_one, one_mul, mul_one]

theorem sec_mul_L {σ : BinaryTreeAut} (hσ : σ ∈ finitary) (g : BinaryTreeAut) (x : Ray) :
    ∃ N, ∀ n ≥ N, sec (g * σ⁻¹) (rayPrefix x n) = sec g (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := finitary.inv_mem hσ
  refine ⟨m, fun n hn => ?_⟩
  rw [sec_mul, sec_eq_one_of_le σ⁻¹ hn hm _ (by rw [length_vertex_smul, length_rayPrefix]),
    mul_one]

end B4Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.12 as stated fails for `υ̌_n` (prover 3, item 3)

The bound of Proposition 7.12 is uniform in `f`, and `f(0)` is free (only `f ⩾ 0`, `f`
non-increasing on `[0, ∞)` and the ratio condition on `[1, ∞)` are asked). The term `x = o = 1^∞`
of the sum is `f(0) · υ̌_n{g : (g, o) ∉ ℋ^b}`. For `υ_n` that mass is `0` (every factor `γ_j` acts at a
point whose first `j + 1` digits are `1`, where its germ is good). For `υ̌_n` it is not: with
`D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6`, the element `g_1 = a c a c` is `θ_6(e_1, γ)` for every `γ`, so
`υ̌_6(g_1⁻¹) = υ_6(g_1) ⩾ 2⁻⁶`, and the sections of `g_1⁻¹ = c a c a` along `1^∞` are `c_{𝔰ⁿω}`
(`n ⩾ 2`), so `(g_1⁻¹, o) ∉ ℋ^b`. Taking `f = 1` on `(0, ∞)` and `f(0) = M` large contradicts the
`υ̌` inequality.

The sum is a genuine (summable) sum: every `g ∈ G_ω` has only finitely many points where its
sections are not eventually `1` or `b_{𝔰ⁿω}` (closure induction: generators have at most `1^∞`), and
`υ̌_6` has finite support.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3P712Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev

/-! ### Germs read from sections, point by point -/

/-- The sections of `g` along `x` are eventually `1`, or eventually `b_{𝔰ⁿω}`. -/
def GoodAt (ω : ℕ → Fin 3) (g : BinaryTreeAut) (x : Ray) : Prop :=
  ∃ N, (∀ n ≥ N, sec g (rayPrefix x n) = 1) ∨
    (∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) .b)

theorem goodAt_mul (ω : ℕ → Fin 3) {g h : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x)
    (hh : GoodAt ω h (x <• g)) : GoodAt ω (g * h) x := by
  obtain ⟨N, hN⟩ := hg
  obtain ⟨M, hM⟩ := hh
  have e : ∀ n, sec (g * h) (rayPrefix x n) =
      sec g (rayPrefix x n) * sec h (rayPrefix (x <• g) n) := fun n => by
    rw [sec_mul, rayPrefix_smul]
  refine ⟨max N M, ?_⟩
  rcases hN with hN | hN <;> rcases hM with hM | hM
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), mul_one]
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), gen_mul_self]

theorem goodAt_inv (ω : ℕ → Fin 3) {g : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x) :
    GoodAt ω g⁻¹ (x <• g) := by
  obtain ⟨N, hN⟩ := hg
  have e : ∀ n, sec g⁻¹ (rayPrefix (x <• g) n) = (sec g (rayPrefix x n))⁻¹ := fun n => by
    rw [sec_inv, rayPrefix_smul, vertex_smul_smul_inv]
  refine ⟨N, ?_⟩
  rcases hN with hN | hN
  · exact Or.inl fun n hn => by rw [e, hN n hn, inv_one]
  · exact Or.inr fun n hn => by rw [e, hN n hn, gen_inv]

theorem goodAt_one (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω 1 x :=
  ⟨0, Or.inl fun n _ => sec_one _⟩

theorem goodAt_grigA (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω grigA x := by
  refine ⟨1, Or.inl fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : rayPrefix x (m + 1) = x 0 :: rayPrefix (shiftRay x 1) m := by
    simp [rayPrefix, List.ofFn_succ, shiftRay]
  rw [this, sec_grigA_cons]

theorem goodAt_gen (ω : ℕ → Fin 3) (γ : BCD) {x : Ray} (hx : x ≠ oneRay) :
    GoodAt ω (gen ω γ) x := by
  rcases sec_gen_along ω γ x with ⟨N, hN⟩ | h
  · exact ⟨N, Or.inl hN⟩
  · exact absurd h hx

theorem goodAt_gen_b (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω (gen ω .b) x := by
  by_cases hx : x = oneRay
  · subst hx
    exact ⟨0, Or.inr fun n _ => by rw [rayPrefix_oneRay, sec_gen_replicate_true]⟩
  · exact goodAt_gen ω .b hx

/-- Every element of `G_ω` has sections eventually `1` or `b` along all but finitely many rays. -/
theorem finite_not_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    {x | ¬ GoodAt ω g x}.Finite := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · simp [goodAt_grigA]
    · simp [goodAt_gen_b]
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .c h)
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .d h)
  | one => simp [goodAt_one]
  | mul g h _ _ ihg ihh =>
    refine (ihg.union (ihh.image fun y => y <• g⁻¹)).subset fun x hx => ?_
    by_cases h1 : GoodAt ω g x
    · right
      refine ⟨x <• g, fun h2 => hx (goodAt_mul ω h1 h2), ?_⟩
      exact rsmul_inv_smul x g
    · exact Or.inl h1
  | inv g _ ihg =>
    refine (ihg.image fun y => y <• g).subset fun x hx => ?_
    refine ⟨x <• g⁻¹, fun h2 => hx ?_, ?_⟩
    · have := goodAt_inv ω h2
      rwa [← rsmul_mul, inv_mul_cancel, rsmul_one] at this
    · show (x <• g⁻¹) <• g = x
      rw [← rsmul_mul, inv_mul_cancel, rsmul_one]

/-- Good sections give a germ in `ℋ^b` (as in B4). -/
theorem mem_of_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) {x : Ray}
    (hx : x ∈ orbitOne ω) (hG : GoodAt ω g x) : (g, x) ∈ letterGerms ω .b := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hgGL : g ∈ grigorchuk ω ⊔ finitary := mem_GL_of_G hg
  obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
  set σ := transport finitary x (x <• g)
  obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL hx)
  set ρ := transport finitary oneRay x
  have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  have hkGL : g * σ⁻¹ ∈ grigorchuk ω ⊔ finitary :=
    Subgroup.mul_mem _ hgGL (mem_GL_of_L (finitary.inv_mem hσL))
  refine ⟨hg, hx, g * σ⁻¹, hkGL, hk, rfl, ?_⟩
  have hK : oneRay <• (ρ * (g * σ⁻¹) * ρ⁻¹) = oneRay := conj_fix hρ hk
  obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hk
  obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
  obtain ⟨N, hN⟩ := hG
  rcases hN with hN | hN
  · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = 1 := by
      rw [← germ_one oneRay]
      exact germ_eq_of_sec' hK (one_fix oneRay) (N := max N (max N1 N3)) fun n hn => by
        rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega), sec_one]
    rw [this]; exact Subgroup.one_mem _
  · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = germ oneRay (gen ω .b) :=
      germ_eq_of_sec' hK hbo (N := max N (max N1 N3)) fun n hn => by
        rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega),
          sec_gen_replicate_true]
    rw [this]; exact Subgroup.mem_zpowers _

/-! ### The witness: `D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6` -/

/-- `ω = (201)^∞`. -/
def ω₁ : ℕ → Fin 3 := fun i => if i % 3 = 0 then 2 else if i % 3 = 1 then 0 else 1

/-- `k_n = 3`. -/
def k₁ : ℕ → ℕ := fun _ => 3

/-! ### `Λ_n` is finite; `Λ_6` is non-empty -/

theorem finite_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : (vSet D ω j k).Finite := by
  apply Set.Finite.subset ((List.finite_length_eq Bool k).image fun u =>
    List.replicate (D - j % D) true ++ u ++ List.replicate (frM D ω (ellIndex D k j) + 2) true ++
      [false])
  rintro v ⟨u, hu, rfl⟩
  exact ⟨u, hu.1, rfl⟩

theorem finite_fSet (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · apply Set.Finite.subset ((finite_vSet D ω j (2 * k n)).image (gTilde ω j))
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, hv, rfl⟩
  · exact Set.finite_singleton _

theorem cpl_cons_true (u : List Bool) :
    commonPrefixLength (true :: u) oneRay = commonPrefixLength u oneRay + 1 := by
  simp [commonPrefixLength, rayPrefix_oneRay, List.replicate_succ, List.takeWhile_cons]

theorem cpl_replicate_append (N : ℕ) (w : List Bool) :
    N ≤ commonPrefixLength (List.replicate N true ++ w) oneRay := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [List.replicate_succ, List.cons_append, cpl_cons_true]
    omega

theorem nonempty_fSet (i : Fin 6) : (fSet 3 ω₁ k₁ (i + 1) 6).Nonempty := by
  unfold fSet
  split_ifs with h
  · set m := frM 3 ω₁ (ellIndex 3 (2 * k₁ 6) (i + 1))
    set v := List.replicate (3 - (i + 1) % 3) true ++ List.replicate (2 * k₁ 6) true ++
      List.replicate (m + 2) true ++ [false]
    refine ⟨gTilde ω₁ (i + 1) v, v, ⟨List.replicate (2 * k₁ 6) true, ⟨by simp, ?_⟩, rfl⟩, ?_, rfl⟩
    · intro j hj _; simp
    · have : v = List.replicate (3 - (i + 1) % 3 + 2 * k₁ 6) true ++
          (List.replicate (m + 2) true ++ [false]) := by
        simp only [v, List.replicate_add, List.append_assoc]
      rw [this]
      refine le_trans ?_ (cpl_replicate_append _ _)
      have := i.2
      simp only [k₁]
      omega
  · exact Set.singleton_nonempty _

instance (i : Fin 6) : Finite (fSet 3 ω₁ k₁ (i + 1) 6) := (finite_fSet _ _ _ _ _).to_subtype

instance : Finite (LambdaN 3 ω₁ k₁ 6) := inferInstance

instance : Nonempty (fProd 3 ω₁ k₁ 6) :=
  ⟨fun i => ⟨(nonempty_fSet i).some, (nonempty_fSet i).some_mem⟩⟩

/-! ### `υ_6(g_1) ⩾ 2⁻⁶` -/

/-! ### Finite support and summability -/

end P3P712Dev

end ErschlerZheng
end

section
/-!
# Theorem 7.13 (I3) as a reduction to Propositions 3.3, 7.11, 7.12 (corrected) (prover 7)

Also used: Corollary 8.2 (J2, `μ_β` is a probability), Example 3.2 (B3, isotropy at `1^∞`), A2
(orbits of `L_fin`, `L_fin` auxiliary) and B1 (through prover 3's `GoodAt` ↔ `ℋ^b`).

The paper's proof, p. 43–44. Proposition 3.3 asks for
`Σ_{x ∈ o·G} G(o, x) μ_β{g : (g, x) ∉ ℋ^b} < ∞`.

* `x = o` and its Schreier neighbour: finitely many terms, each finite. The Green function is
  finite everywhere: Proposition 7.11 bounds `G(w, x)` for some `w` at distance `⩾ 2` from `x`, and
  `P^m(w, o) G(o, x) ⩽ G(w, x)` with `P^m(w, o) > 0` (non-degeneracy).
* `x ≠ o`: the generators have good germs at `x` (`P3P712.goodAt_gen`), so
  `μ_β{…} = ½ Σ_n C_β 2^{-nβ}(υ_n + υ̌_n){…}`. For `d(o, x) ⩾ 2`, `G(o, x) ⩽ f̃(d(o, x))` with the
  comparison function `f̃` of `P7Aux`, which satisfies Proposition 7.12's hypotheses with
  `D' = 1/(1-β)`. Proposition 7.12 (the `υ̌_n` sum over `x ≠ o`, the `υ_n` sum over the orbit)
  bounds the `n`-th term by `C' 2^n f̃(2^{n+2k_n})`, and `Σ_n 2^{-nβ} 2^n f̃(2^{n+2k_n}) < ∞` (p. 44).
* Both orbit sums of Proposition 7.12 are finite sums: `υ_n` has finite support and every element
  of `G_ω` has good germs at all but finitely many points.
-/

open scoped RightActions ENNReal
open Garrido DurrettProbability Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P7Dev

open GrigBasic P3P712Dev B8MarkovDev

/-! ### `μ_β` is non-degenerate (as in prover 5's `P5Goal`) -/

lemma not_eventually_const {D : ℕ} {ω : ℕ → Fin 3} (hω : SatisfiesFr D ω) :
    ¬ ∃ i : Fin 3, ∀ᶠ k in atTop, ω k = i := by
  rintro ⟨i, hi⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hi
  obtain ⟨m, -, h2, h1, -⟩ := hω N
  have hD : 1 ≤ D := by have := P6Dev.three_le_of_satisfiesFr hω; omega
  have a := hN (N * D + m) (by nlinarith)
  have b := hN (N * D + m + 2) (by nlinarith)
  rw [h2] at a; rw [h1] at b
  rw [← a] at b
  exact absurd b (by decide)

/-! ### Finite supports -/

theorem finite_support_upsilon (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) :
    {h | upsilon D ω k n h ≠ 0}.Finite := by
  by_cases hfin : Finite (LambdaN D ω k n)
  · refine (Set.finite_range (theta D ω k n)).subset fun h hh => ?_
    by_contra hr
    apply hh
    unfold upsilon
    have : IsEmpty {p // theta D ω k n p = h} := ⟨fun ⟨p, hp⟩ => hr ⟨p, hp⟩⟩
    rw [Nat.card_of_isEmpty]; simp
  · have : Infinite (LambdaN D ω k n) := not_finite_iff_infinite.mp hfin
    have h0 : Nat.card (LambdaN D ω k n) = 0 := Nat.card_eq_zero_of_infinite
    refine Set.finite_empty.subset fun h hh => hh ?_
    simp [upsilon, h0]

theorem finite_support_upsilonCheck (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) :
    {h | upsilonCheck D ω k n h ≠ 0}.Finite := by
  refine ((finite_support_upsilon D ω k n).image fun h => h⁻¹).subset fun h hh => ?_
  exact ⟨h⁻¹, hh, inv_inv h⟩

/-- The orbit sums of Proposition 7.12 are finitely supported. -/
theorem summable_orbit_sum (ω : ℕ → Fin 3) (ν : BinaryTreeAut → ℝ)
    (hν : {h | ν h ≠ 0}.Finite) (F : ℝ → ℝ) (Y : Set Ray) (hY : Y ⊆ orbitOne ω) :
    Summable fun x : Y => F (schreierDist ω oneRay x) *
      mass (fun g : grigorchuk ω => ν g)
        {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} := by
  set T : Set BinaryTreeAut := {h | ν h ≠ 0} ∩ grigorchuk ω
  have hT : T.Finite := hν.subset Set.inter_subset_left
  set Bad : Set Ray := ⋃ h ∈ T, {x | ¬ GoodAt ω h x}
  have hBad : Bad.Finite := hT.biUnion fun h hh => finite_not_goodAt ω hh.2
  refine summable_of_hasFiniteSupport ((hBad.preimage Subtype.val_injective.injOn).subset ?_)
  intro x hx
  by_contra hxB
  apply hx
  show _ * _ = 0
  rw [mul_eq_zero]; right
  unfold mass
  convert tsum_zero with g
  by_cases hg : ν (g : BinaryTreeAut) = 0
  · simp [Set.indicator, hg]
  · have hgood : GoodAt ω g x := by
      by_contra hng
      exact hxB (Set.mem_biUnion (x := (g : BinaryTreeAut)) ⟨hg, g.2⟩ hng)
    have hmem := mem_of_goodAt ω g.2 (hY x.2) hgood
    simp [Set.indicator, hmem]

/-! ### Generators have good germs off `o` -/

theorem gen_mem_letterGerms (ω : ℕ → Fin 3) {x : Ray} (hx : x ∈ orbitOne ω) (hxo : x ≠ oneRay)
    {s : grigorchuk ω} (hs : s ∈ genSet ω) : ((s : BinaryTreeAut), x) ∈ letterGerms ω .b := by
  refine mem_of_goodAt ω s.2 hx ?_
  simp only [genSet, gens, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h <;> rw [h]
  · exact goodAt_grigA ω x
  all_goals exact goodAt_gen ω _ hxo

/-! ### The mass of `μ_β` off `o` -/

lemma upsilonCheck_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    0 ≤ upsilonCheck D ω k n g := P6Dev.upsilon_nonneg _ _ _ _ _

/-- `C_β 2^{-nβ}` on `n ⩾ 1`, `D ∣ n`. -/
noncomputable def cN (D : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ D ∣ n then normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) else 0

lemma cN_nonneg (D : ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D) (n : ℕ) : 0 ≤ cN D β n := by
  unfold cN; split_ifs
  · exact mul_nonneg (P6Dev.normConst_pos D β hβ hD).le (by positivity)
  · exact le_rfl

theorem summable_indicator_upsilon (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ)
    (S : Set (grigorchuk ω)) (ν : BinaryTreeAut → ℝ) (hν : {h | ν h ≠ 0}.Finite) :
    Summable (S.indicator fun g : grigorchuk ω => ν g) := by
  refine summable_of_hasFiniteSupport ((hν.preimage Subtype.val_injective.injOn).subset ?_)
  intro g hg
  by_contra h
  apply hg
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at h
  simp [Set.indicator, h]

theorem ofReal_mass_muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β)
    (hD : 1 ≤ D) (hμ : IsProbability (muBeta D ω k β)) {x : Ray} (hx : x ∈ orbitOne ω)
    (hxo : x ≠ oneRay) :
    ENNReal.ofReal (mass (muBeta D ω k β)
        {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}) =
      ENNReal.ofReal (1 / 2) * ∑' n, ENNReal.ofReal (cN D β n) *
        (ENNReal.ofReal (mass (fun g : grigorchuk ω => upsilon D ω k n g)
            {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}) +
          ENNReal.ofReal (mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
            {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b})) := by
  set S := {g : grigorchuk ω | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}
  have hu := fun n => summable_indicator_upsilon D ω k n S _ (finite_support_upsilon D ω k n)
  have hc := fun n => summable_indicator_upsilon D ω k n S _ (finite_support_upsilonCheck D ω k n)
  unfold mass
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => Set.indicator_nonneg (fun g _ => hμ.1 g) g)
    (hμ.2.summable.indicator S)]
  have hpt : ∀ g, ENNReal.ofReal (S.indicator (muBeta D ω k β) g) =
      ENNReal.ofReal (1 / 2) * ∑' n, ENNReal.ofReal (cN D β n) *
        (ENNReal.ofReal (S.indicator (fun g : grigorchuk ω => upsilon D ω k n g) g) +
          ENNReal.ofReal (S.indicator (fun g : grigorchuk ω => upsilonCheck D ω k n g) g)) := by
    intro g
    by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg]
      have hgS : g ∉ genSet ω := fun hs => hg (gen_mem_letterGerms ω hx hxo hs)
      classical
      have hU : uniformMeasure (genSet ω) g = 0 := by simp [uniformMeasure, hgS]
      unfold muBeta
      rw [hU, mul_zero, zero_add, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_tsum_of_nonneg _ (P6Dev.summable_muBeta_series D ω k β hβ hD g)]
      · congr 1
        refine tsum_congr fun n => ?_
        unfold cN
        split_ifs
        · rw [ENNReal.ofReal_mul (mul_nonneg (P6Dev.normConst_pos D β hβ hD).le (by positivity)),
            ENNReal.ofReal_add (P6Dev.upsilon_nonneg _ _ _ _ _) (upsilonCheck_nonneg _ _ _ _ _)]
        · simp
      · intro n
        split_ifs
        · exact mul_nonneg (mul_nonneg (P6Dev.normConst_pos D β hβ hD).le (by positivity))
            (add_nonneg (P6Dev.upsilon_nonneg _ _ _ _ _) (P6Dev.upsilon_nonneg _ _ _ _ _))
        · exact le_rfl
    · simp [Set.indicator_of_notMem hg]
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
  congr 1
  refine tsum_congr fun n => ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add,
    ENNReal.ofReal_tsum_of_nonneg (fun g => Set.indicator_nonneg
      (fun g _ => P6Dev.upsilon_nonneg _ _ _ _ _) g) (hu n),
    ENNReal.ofReal_tsum_of_nonneg (fun g => Set.indicator_nonneg
      (fun g _ => upsilonCheck_nonneg _ _ _ _ _) g) (hc n)]

/-! ### The series of p. 44 -/

theorem summable_T (D A : ℕ) {β K a' e R₀ M : ℝ} (hβ0 : 0 < β) (hD : 1 ≤ D) (ht : 0 < 1 - β)
    (hK : 0 < K) (ha : 0 ≤ a') (he : a' = 2 * A * (1 - β) - e) (he1 : 1 < e) (hR : 4 ≤ R₀)
    (hRa : a' ≤ (1 - β) * Real.log R₀) (hM : 0 ≤ M) :
    Summable fun n : ℕ => cN D β n *
      (M * 2 ^ n * ftil K (1 - β) a' R₀ (2 ^ (n + 2 * kLog A n))) := by
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt R₀ (one_lt_two : (1 : ℝ) < 2)
  have hC0 := (P6Dev.normConst_pos D β hβ0 hD).le
  set B := normConst D β * M * K * ((2 : ℝ) ^ (2 * A * (1 - β)) * (1 + 2 * A) ^ a')
  have hB : 0 ≤ B := by positivity
  have hnn : ∀ n, 0 ≤ cN D β n * (M * 2 ^ n * ftil K (1 - β) a' R₀ (2 ^ (n + 2 * kLog A n))) :=
    fun n => mul_nonneg (cN_nonneg D β hβ0 hD n)
      (mul_nonneg (by positivity) (ftil_pos hK ht ha hR hRa _).le)
  have hb : ∀ n, N₀ + 1 ≤ n → cN D β n *
      (M * 2 ^ n * ftil K (1 - β) a' R₀ (2 ^ (n + 2 * kLog A n))) ≤ B * (n : ℝ) ^ (-e) := by
    intro n hn
    unfold cN
    split_ifs with hc
    · have hmax : max ((2 : ℝ) ^ (n + 2 * kLog A n)) R₀ = 2 ^ (n + 2 * kLog A n) := by
        refine max_eq_left (hN₀.le.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
      unfold ftil
      rw [hmax]
      have := term_le (β := β) (t := 1 - β) (a' := a') (e := e) A n (by omega) rfl ht ha he
      calc normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) *
            (M * 2 ^ n * (K / P6Dev.psi (1 - β) a' (2 ^ (n + 2 * kLog A n)))) =
          normConst D β * M * K * ((2 : ℝ) ^ (-((n : ℝ) * β)) * 2 ^ n *
            (P6Dev.psi (1 - β) a' (2 ^ (n + 2 * kLog A n)))⁻¹) := by ring
        _ ≤ normConst D β * M * K * ((2 : ℝ) ^ (2 * A * (1 - β)) * (1 + 2 * A) ^ a' *
            (n : ℝ) ^ (-e)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = B * (n : ℝ) ^ (-e) := by ring
    · rw [zero_mul]; positivity
  have hs1 : Summable fun n : ℕ => B * (n : ℝ) ^ (-e) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left B
  have hs2 : Summable fun n : ℕ => B * ((n + (N₀ + 1) : ℕ) : ℝ) ^ (-e) :=
    (summable_nat_add_iff (f := fun n : ℕ => B * (n : ℝ) ^ (-e)) (N₀ + 1)).mpr hs1
  have hs3 : Summable fun n : ℕ => cN D β (n + (N₀ + 1)) *
      (M * 2 ^ (n + (N₀ + 1)) * ftil K (1 - β) a' R₀
        (2 ^ ((n + (N₀ + 1)) + 2 * kLog A (n + (N₀ + 1))))) :=
    Summable.of_nonneg_of_le (fun n => hnn _) (fun n => hb (n + (N₀ + 1)) (by omega)) hs2
  exact (summable_nat_add_iff (f := fun n : ℕ => cN D β n *
      (M * 2 ^ n * ftil K (1 - β) a' R₀ (2 ^ (n + 2 * kLog A n)))) (N₀ + 1)).mp hs3

theorem schreierDist_self (ω : ℕ → Fin 3) (x : Ray) : schreierDist ω x x = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨1, WordBallDev.one_mem_wordBall _ _, by simp⟩)

end P7Dev

end ErschlerZheng
end

section
open scoped RightActions ENNReal
open Garrido DurrettProbability Filter
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open ErschlerZheng
open P7Dev in
/-- Theorem 7.13 (I3), a reduction to Propositions 3.3, 7.11, 7.12 (corrected), Corollary 8.2
(probability), Example 3.2 (isotropy) and A2. -/
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ)
    (hA : (D : ℝ) * (1 + β) / (2 * (1 - β)) < A) (hDA : D ∣ A) :
    HasNontrivialPoissonBoundary (muBeta D ω (kLog A) β) := by
  classical
  have hD3 := P6Dev.three_le_of_satisfiesFr hω
  have hD1 : 1 ≤ D := by omega
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD3
  have hDpos : (0 : ℝ) < D := by linarith
  have hβ0 : 0 < β := by
    have : 1 / (D : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hDr
    linarith
  have ht : 0 < 1 - β := by linarith
  have hAr : (0 : ℝ) < A := lt_of_le_of_lt (by positivity) hA
  have hApos : 0 < A := by exact_mod_cast hAr
  have hk := P6Dev.isAdmissibleSeq_kLog D A hD3 hDA hApos
  obtain ⟨_, _, hJ⟩ := isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le D β hβ0
  have hμ : IsProbability (muBeta D ω (kLog A) β) :=
    (hJ ω hω (kLog A) hk (P6Dev.eventually_kLog_le A)).1
  have hnd := isNondegenerate_muBeta D ω (kLog A) β
  have hB3 := (isLevelTransitive_and_isotropy_grigorchuk ω).2.2.2 (not_eventually_const hω)
  have hcof : IsCofinal oneRay := Filter.Eventually.of_forall fun _ => rfl
  have hGGo := (hB3.1 oneRay hcof).1
  have hHo := hB3.2.2
  have hGo : isotropy (grigorchuk ω ⊔ finitary) oneRay ≠ ⊥ := by
    intro h; rw [h] at hHo; exact not_lt_bot hHo
  have hL := (isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary).2.2 ω
  have hoo : oneRay ∈ orbitOne ω := ⟨1, (grigorchuk ω).one_mem, by simp⟩
  set o₀ : orbitOne ω := ⟨oneRay, hoo⟩ with ho₀
  refine hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top (grigorchuk ω) finitary hL
    oneRay hGo hGGo _ hμ hnd o₀ rfl (germLetterSubgroup ω .b) hHo ?_
  change ∑' x : orbitOne ω, _ * ENNReal.ofReal (mass (muBeta D ω (kLog A) β)
    {g : grigorchuk ω | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) < ⊤
  -- parameters
  have hA' := hA
  rw [div_lt_iff₀ (by positivity)] at hA'
  have hgap : (1 + β) / (1 - β) < 2 * A / D := by
    rw [div_lt_div_iff₀ ht hDpos]; nlinarith
  set ε : ℝ := (2 * A / D - (1 + β) / (1 - β)) / 2 with hεdef
  have hε : 0 < ε := by linarith
  set e : ℝ := (1 - β) / (1 + β) * (2 * (A : ℝ) / D - ε) with hedef
  have he1 : 1 < e := by
    have h1 : (1 + β) / (1 - β) < 2 * A / D - ε := by linarith
    calc (1 : ℝ) = (1 - β) / (1 + β) * ((1 + β) / (1 - β)) := by field_simp
      _ < e := mul_lt_mul_of_pos_left h1 (by positivity)
  set a' : ℝ := 2 * A * (1 - β) - e with ha'def
  have ha' : 0 ≤ a' := by
    have q1 : (1 - β) / (1 + β) ≤ 1 - β := div_le_self ht.le (by linarith)
    have q2 : 0 < 2 * (A : ℝ) / D - ε := by
      have : 0 < (1 + β) / (1 - β) := by positivity
      linarith
    have q3 : 2 * (A : ℝ) / D ≤ 2 * A := div_le_self (by positivity) (by linarith)
    have : e ≤ (1 - β) * (2 * A) := by
      calc e ≤ (1 - β) * (2 * (A : ℝ) / D - ε) := mul_le_mul_of_nonneg_right q1 q2.le
        _ ≤ (1 - β) * (2 * A) := mul_le_mul_of_nonneg_left (by linarith) ht.le
    rw [ha'def]; nlinarith
  set R₀ : ℝ := max 4 (Real.exp (a' / (1 - β))) with hR₀def
  have hR : 4 ≤ R₀ := le_max_left _ _
  have hRa : a' ≤ (1 - β) * Real.log R₀ := by
    have : a' / (1 - β) ≤ Real.log R₀ := by
      rw [← Real.log_exp (a' / (1 - β))]
      exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    rwa [div_le_iff₀ ht, mul_comm] at this
  obtain ⟨C, hC, hG⟩ := green_orbitKernel_muBeta_le D ω hω β hβ1 hβ2 A hApos hDA ε hε
  set K := C * R₀ ^ (1 - β) with hKdef
  have hK : 0 < K := by positivity
  set f := ftil K (1 - β) a' R₀ with hfdef
  have hD' : (D : ℝ) < 1 / (1 - β) := by
    rw [lt_div_iff₀ ht]
    have : 1 - β < 1 / (D : ℝ) := by linarith
    calc (D : ℝ) * (1 - β) < D * (1 / D) := mul_lt_mul_of_pos_left this hDpos
      _ = 1 := by field_simp
  obtain ⟨C', hC'⟩ := tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le D ω hω
    (kLog A) hk (1 / (1 - β)) hD'
  have hfpos : ∀ s, 0 < f s := fun s => ftil_pos hK ht ha' hR hRa s
  have hf0 : ∀ s, 0 ≤ s → 0 ≤ f s := fun s _ => (hfpos s).le
  have hfa : AntitoneOn f (Set.Ici 0) := ftil_antitone hK ht ha' hR hRa
  have hfr : ∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / (1 / (1 - β))) ≤ f (2 * s) / f s := by
    intro s hs
    rw [show -1 / (1 / (1 - β)) = -(1 - β) by rw [div_div_eq_mul_div, div_one]; ring]
    exact ftil_ratio hK ht ha' hR hRa s hs
  have hP := fun n hn => hC' f hf0 hfa hfr n hn
  -- notation
  set P := orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay with hPdef
  set Mx : orbitOne ω → ℝ≥0∞ := fun x => ENNReal.ofReal (mass (muBeta D ω (kLog A) β)
    {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) with hMx
  set Fu : ℕ → Ray → ℝ := fun n r => f (schreierDist ω oneRay r) *
    mass (fun g : grigorchuk ω => upsilon D ω (kLog A) n g)
      {g | ((g : BinaryTreeAut), r) ∉ letterGerms ω .b} with hFu
  set Fc : ℕ → Ray → ℝ := fun n r => f (schreierDist ω oneRay r) *
    mass (fun g : grigorchuk ω => upsilonCheck D ω (kLog A) n g)
      {g | ((g : BinaryTreeAut), r) ∉ letterGerms ω .b} with hFc
  have hmass_nonneg : ∀ (ν : BinaryTreeAut → ℝ), (∀ h, 0 ≤ ν h) → ∀ r : Ray,
      0 ≤ mass (fun g : grigorchuk ω => ν g) {g | ((g : BinaryTreeAut), r) ∉ letterGerms ω .b} :=
    fun ν hν r => tsum_nonneg fun g =>
      Set.indicator_nonneg (fun (g' : grigorchuk ω) _ => hν (g' : BinaryTreeAut)) g
  have hFu0 : ∀ n r, 0 ≤ Fu n r := fun n r =>
    mul_nonneg (hfpos _).le (hmass_nonneg _ (P6Dev.upsilon_nonneg _ _ _ _) r)
  have hFc0 : ∀ n r, 0 ≤ Fc n r := fun n r =>
    mul_nonneg (hfpos _).le (hmass_nonneg _ (upsilonCheck_nonneg _ _ _ _) r)
  -- the Green function is finite
  have hGfin : ∀ x : orbitOne ω, MarkovChain.green P o₀ x < ⊤ := by
    intro x
    obtain ⟨w, hw⟩ := exists_far ω x
    have hwx := hG w x (by unfold orbitDist; exact_mod_cast hw)
    exact green_lt_top_of (grigorchuk ω) hμ hnd oneRay w o₀ x
      (lt_of_le_of_lt hwx ENNReal.ofReal_lt_top)
  -- the pointwise split
  set Near : orbitOne ω → ℝ≥0∞ := fun x =>
    if schreierDist ω oneRay x ≤ 1 then MarkovChain.green P o₀ x * Mx x else 0 with hNear
  set Far : orbitOne ω → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / 2) * ∑' n,
    ENNReal.ofReal (cN D β n) *
      ((if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fu n x) else 0) +
        (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fc n x) else 0)) with hFar
  have hsplit : ∀ x : orbitOne ω, MarkovChain.green P o₀ x * Mx x ≤ Near x + Far x := by
    intro x
    by_cases hd : schreierDist ω oneRay x ≤ 1
    · simp only [hNear, if_pos hd]; exact le_self_add
    · have hd2 : 2 ≤ schreierDist ω oneRay x := by omega
      have hxo : (x : Ray) ≠ oneRay := by
        intro h; rw [h, schreierDist_self] at hd2; omega
      simp only [hNear, if_neg hd, zero_add]
      have hGx := hG o₀ x (by unfold orbitDist; exact_mod_cast hd2)
      have hbd := bound_le_ftil (β := β) (t := 1 - β) (e := e) A hC rfl ht ha' hR ha'def
        (orbitDist ω o₀ x) (by unfold orbitDist; exact_mod_cast hd2)
      have hGf : MarkovChain.green P o₀ x ≤ ENNReal.ofReal (f (schreierDist ω oneRay x)) :=
        hGx.trans (ENNReal.ofReal_le_ofReal hbd)
      calc MarkovChain.green P o₀ x * Mx x ≤ ENNReal.ofReal (f (schreierDist ω oneRay x)) * Mx x :=
            by gcongr
        _ = Far x := by
            simp only [hMx, hFar, if_pos hxo]
            rw [ofReal_mass_muBeta D ω (kLog A) β hβ0 hD1 hμ x.2 hxo, mul_left_comm,
              ← ENNReal.tsum_mul_left]
            congr 1
            refine tsum_congr fun n => ?_
            simp only [hFu, hFc]
            rw [ENNReal.ofReal_mul (hfpos _).le, ENNReal.ofReal_mul (hfpos _).le]
            ring
  -- the near part is a finite sum of finite terms
  have hNear_fin : ∑' x, Near x < ⊤ := by
    obtain hfin := (finite_near ω o₀).1
    rw [tsum_eq_sum (s := hfin.toFinset) (fun x hx => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
      exact if_neg hx)]
    refine ENNReal.sum_lt_top.mpr fun x _ => ?_
    simp only [hNear]
    split_ifs
    · exact ENNReal.mul_lt_top (hGfin x) ENNReal.ofReal_lt_top
    · exact ENNReal.zero_lt_top
  -- the far part: Proposition 7.12, term by term
  set T : ℕ → ℝ := fun n => cN D β n *
    ((2 * |C'|) * 2 ^ n * f (2 ^ (n + 2 * kLog A n))) with hT
  have hTs : Summable T := summable_T D A hβ0 hD1 ht hK ha' ha'def he1 hR hRa (by positivity)
  have hT0 : ∀ n, 0 ≤ T n := fun n => mul_nonneg (cN_nonneg D β hβ0 hD1 n)
    (mul_nonneg (by positivity) (hfpos _).le)
  have hterm : ∀ n, ENNReal.ofReal (cN D β n) *
      (∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fu n x) else 0) +
        ∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fc n x) else 0)) ≤
      ENNReal.ofReal (T n) := by
    intro n
    by_cases hc : 1 ≤ n ∧ D ∣ n
    · have hb := hP n hc.2
      set Bn : ℝ := |C'| * 2 ^ n * f (2 ^ (n + 2 * kLog A n)) with hBn
      have hX : ∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fu n x) else 0) ≤
          ENNReal.ofReal Bn := by
        calc _ ≤ ∑' x : orbitOne ω, ENNReal.ofReal (Fu n x) :=
              ENNReal.tsum_le_tsum fun x => by split_ifs <;> simp
          _ = ENNReal.ofReal (∑' x : orbitOne ω, Fu n x) := by
              have hsu : Summable fun x : orbitOne ω => Fu n x := by
                simp only [hFu]
                exact summable_orbit_sum ω _ (finite_support_upsilon D ω (kLog A) n) f
                  (orbitOne ω) subset_rfl
              exact (ENNReal.ofReal_tsum_of_nonneg (f := fun x : orbitOne ω => Fu n x)
                (fun x => hFu0 n (x : Ray)) hsu).symm
          _ ≤ ENNReal.ofReal Bn := by
              refine ENNReal.ofReal_le_ofReal (hb.2.1.trans ?_)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
                (by positivity)) (hfpos _).le
      have hY : ∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fc n x) else 0) ≤
          ENNReal.ofReal Bn := by
        have e1 : ∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fc n x) else 0) =
            ∑' y : ↥(orbitOne ω \ {oneRay}), ENNReal.ofReal (Fc n y) := by
          rw [tsum_subtype (orbitOne ω) (fun r => if r ≠ oneRay then ENNReal.ofReal (Fc n r) else 0),
            tsum_subtype (orbitOne ω \ {oneRay}) (fun r => ENNReal.ofReal (Fc n r))]
          congr 1; funext r
          by_cases h1 : r ∈ orbitOne ω <;> by_cases h2 : r = oneRay <;>
            simp [Set.indicator, h1, h2]
        have hsc : Summable fun x : ↥(orbitOne ω \ {oneRay}) => Fc n x := by
          simp only [hFc]
          exact summable_orbit_sum ω _ (finite_support_upsilonCheck D ω (kLog A) n) f
            (orbitOne ω \ {oneRay}) Set.sdiff_subset
        rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (f := fun x : ↥(orbitOne ω \ {oneRay}) => Fc n x)
          (fun x => hFc0 n (x : Ray)) hsc]
        refine ENNReal.ofReal_le_ofReal (hb.2.2.2.trans ?_)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
          (by positivity)) (hfpos _).le
      calc _ ≤ ENNReal.ofReal (cN D β n) * (ENNReal.ofReal Bn + ENNReal.ofReal Bn) :=
            by gcongr
        _ = ENNReal.ofReal (T n) := by
            have hB0 : 0 ≤ Bn := mul_nonneg (by positivity) (hfpos _).le
            rw [← ENNReal.ofReal_add hB0 hB0, ← ENNReal.ofReal_mul (cN_nonneg D β hβ0 hD1 n)]
            congr 1
            simp only [hT, hBn]; ring
    · have : cN D β n = 0 := by unfold cN; rw [if_neg hc]
      rw [this, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  have hFar_fin : ∑' x, Far x < ⊤ := by
    have e2 : ∑' x, Far x = ENNReal.ofReal (1 / 2) * ∑' n, ENNReal.ofReal (cN D β n) *
        (∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fu n x) else 0) +
          ∑' x : orbitOne ω, (if (x : Ray) ≠ oneRay then ENNReal.ofReal (Fc n x) else 0)) := by
      simp only [hFar]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
      congr 1
      refine tsum_congr fun n => ?_
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    rw [e2]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg hT0 hTs]
    exact ENNReal.ofReal_lt_top
  calc _ ≤ ∑' x, (Near x + Far x) := ENNReal.tsum_le_tsum hsplit
    _ = ∑' x, Near x + ∑' x, Far x := ENNReal.tsum_add
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hNear_fin, hFar_fin⟩
end
