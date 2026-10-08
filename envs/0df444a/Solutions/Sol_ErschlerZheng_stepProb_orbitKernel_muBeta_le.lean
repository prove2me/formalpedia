-- Prove2me | solution 1 for ErschlerZheng.stepProb_orbitKernel_muBeta_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T09:33:36.702398+00:00
-- url     : https://prove2.me/submissions/c6692f7e-a307-46ef-b636-49124cc6a3fa

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Walks
import Theorems.Thm_ErschlerZheng_mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero
import Theorems.Thm_ErschlerZheng_injOn_gTilde_and_ncard_fSet_eq
import Theorems.Thm_ErschlerZheng_orbitKernel_upsilon_eq_and_boundarySize_ge
import Theorems.Thm_Coulhon_stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge
import Theorems.Thm_LawlerSokal_half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize

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

/-- `uniformize` of a substochastic kernel is a transition kernel. -/
lemma isTransition_uniformize {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKs : ∀ x, Summable (K x))
    (hK1 : ∀ x, ∑' y, K x y ≤ 1) : IsTransition (uniformize K) := by
  have hite : ∀ x, Summable (fun y => if x = y then 1 - ∑' z, K x z else 0) := by
    intro x
    exact (hasSum_ite_eq x (1 - ∑' z, K x z)).summable.congr fun y => by
      split_ifs <;> simp_all [eq_comm]
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold uniformize
    have := hK0 x y
    split_ifs
    · linarith [hK1 x]
    · linarith
  · exact (hKs x).add (hite x)
  · unfold uniformize
    rw [(hKs x).tsum_add (hite x)]
    have : ∑' y, (if x = y then 1 - ∑' z, K x z else 0) = 1 - ∑' z, K x z := by
      rw [show (fun y => if x = y then 1 - ∑' z, K x z else 0) =
        fun y => if y = x then 1 - ∑' z, K x z else 0 by funext y; split_ifs <;> simp_all [eq_comm]]
      exact tsum_ite_eq x _
    rw [this]; ring

lemma uniformize_symm {K : X → X → ℝ} (hKs : IsSymmetric K) : IsSymmetric (uniformize K) := by
  intro x y; unfold uniformize
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h, hKs x y]

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

lemma orbitKernel_mul_le {μ ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (hνs : Summable ν) (hμs : Summable μ)
    (hμ : ∀ g, 0 ≤ μ g) {w : ℝ} (hle : ∀ g, w * ν g ≤ μ g) (o : X) (x y : rightOrbit K o) :
    w * orbitKernel K ν o x y ≤ orbitKernel K μ o x y := by
  classical
  unfold orbitKernel
  rw [← tsum_mul_left]
  have s1 : Summable (fun g : K => if (x : X) <• (g : H) = y then ν g else 0) :=
    Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hν g])
      (fun g => by split_ifs <;> simp [hν g]) hνs
  have s2 : Summable (fun g : K => if (x : X) <• (g : H) = y then μ g else 0) :=
    Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hμ g])
      (fun g => by split_ifs <;> simp [hμ g]) hμs
  refine Summable.tsum_le_tsum (fun g => ?_) (s1.mul_left w) s2
  split_ifs
  · exact hle g
  · simp

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

/-- `ν_n = (υ_n + υ̌_n)/2` on `G_ω`. -/
noncomputable def nuN (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : grigorchuk ω → ℝ :=
  fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2

lemma nuN_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : grigorchuk ω) :
    0 ≤ nuN D ω k n g :=
  div_nonneg (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _)) two_pos.le

lemma sum_nuN_le (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (s : Finset (grigorchuk ω)) :
    ∑ g ∈ s, nuN D ω k n g ≤ 1 := by
  unfold nuN upsilonCheck
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 := sum_upsilon_le D ω k n (fun g : grigorchuk ω => (g : BinaryTreeAut))
    Subtype.val_injective s
  have h2 := sum_upsilon_le D ω k n (fun g : grigorchuk ω => (g : BinaryTreeAut)⁻¹)
    (fun a b h => Subtype.val_injective (inv_injective h)) s
  try simp only at h1 h2
  linarith

lemma summable_nuN (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Summable (nuN D ω k n) :=
  summable_of_sum_le (fun g => nuN_nonneg D ω k n g) (sum_nuN_le D ω k n)

lemma tsum_nuN_le (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : ∑' g, nuN D ω k n g ≤ 1 :=
  (summable_nuN D ω k n).tsum_le_of_sum_le (sum_nuN_le D ω k n)

lemma nuN_inv (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : grigorchuk ω) :
    nuN D ω k n g⁻¹ = nuN D ω k n g := by
  unfold nuN upsilonCheck
  simp only [InvMemClass.coe_inv, inv_inv]
  ring

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

lemma uniformMeasure_nonneg {G : Type*} (F : Set G) (g : G) : 0 ≤ uniformMeasure F g := by
  classical
  unfold uniformMeasure
  split_ifs <;> positivity

/-- `C_β 2^{-nβ} ν_n ⩽ μ_β`. -/
lemma mul_nuN_le_muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D)
    (n : ℕ) (hn : 1 ≤ n) (hDn : D ∣ n) (g : grigorchuk ω) :
    normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * nuN D ω k n g ≤ muBeta D ω k β g := by
  have hs := summable_muBeta_series D ω k β hβ hD g
  have hC := (normConst_pos D β hβ hD).le
  have hle := hs.le_tsum n (fun m _ => by
    split_ifs
    · exact mul_nonneg (mul_nonneg hC (by positivity))
        (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
    · exact le_rfl)
  rw [if_pos ⟨hn, hDn⟩] at hle
  unfold muBeta nuN
  have hu := uniformMeasure_nonneg (genSet ω) g
  nlinarith

lemma muBeta_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D)
    (g : grigorchuk ω) : 0 ≤ muBeta D ω k β g := by
  have hC := (normConst_pos D β hβ hD).le
  unfold muBeta
  have := uniformMeasure_nonneg (genSet ω) g
  have : 0 ≤ ∑' m : ℕ, if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0 :=
    tsum_nonneg fun m => by
      split_ifs
      · exact mul_nonneg (mul_nonneg hC (by positivity))
          (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
      · exact le_rfl
  positivity

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

lemma three_le_of_satisfiesFr {D : ℕ} {ω : ℕ → Fin 3} (h : SatisfiesFr D ω) : 3 ≤ D := by
  obtain ⟨m, hm, -⟩ := h 0
  omega

end P6Dev

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

end WordBallDev

end ErschlerZheng
end

section
/-!
# J2: Corollary 8.2 (Erschler–Zheng p. 57), from Lemma 8.1, (7.7) and (8.1)

For `D ∣ n`, `n ⩾ 1`: each `𝔉_{j,n}` is finite and non-empty ((7.7) gives `|𝔉_{j,n}| = 2^{…}`
in the first case, a singleton otherwise), so `Λ_n` is finite and non-empty and `υ_n` is a
probability on `Aut(T)`; by Lemma 8.1 it lives on `G_ω`, and so does `υ̌_n`.

* `μ_β` is a probability: `½ + ½ Σ_n C_β 2^{−nβ}·2 = 1`, by the definition of `C_β`.
* Finite entropy: `−p log p` is subadditive over the pieces of `μ_β`; `H(υ_n) ⩽ log |Λ_n|`
  (`υ_n ⩾ 1/|Λ_n|` on its support) and `log₂ |Λ_n| ⩽ n(1 + 2k_n) ⩽ n + 2n²` eventually.
* Tail: `supp υ_m ⊆ B(2^{2k_m+2D+4} L_m) ⊆ B(2^{2k_n} L_n)` for `m + 2D + 4 ⩽ n` (`k` monotone,
  `L_n ⩾ 2^{n−m} L_m`), so the mass outside is at most `C_β Σ_{m > n−2D−4} 2^{−mβ}`.
-/

namespace ErschlerZheng

namespace P5Cor82Dev

open Garrido Filter Topology

set_option linter.unusedSectionVars false

variable {D : ℕ} {ω : ℕ → Fin 3} {k : ℕ → ℕ}

lemma fSet_finite_nonempty (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ}
    (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    (fSet D ω k j n).Finite ∧ (fSet D ω k j n).Nonempty := by
  by_cases hc : ω (j - 1) = 2 ∧ n < j + k n ∧ j ≤ n
  · have h := (injOn_gTilde_and_ncard_fSet_eq D ω hω k hk n hn j hj1 hc.1 hc.2.1 hc.2.2).2.2
    have hpos : 0 < (fSet D ω k j n).ncard := by rw [h]; positivity
    exact ⟨Set.finite_of_ncard_pos hpos, Set.nonempty_of_ncard_ne_zero hpos.ne'⟩
  · simp only [fSet, if_neg hc]
    exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

lemma lambda_finite (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    Finite (LambdaN D ω k n) := by
  have : ∀ i : Fin n, Finite (fSet D ω k (i + 1) n) := fun i =>
    (fSet_finite_nonempty hω hk hn (i + 1) (by omega)).1.to_subtype
  infer_instance

lemma lambda_nonempty (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    Nonempty (LambdaN D ω k n) :=
  ⟨(fun _ => false, fun i => ⟨_, (fSet_finite_nonempty hω hk hn (i + 1) (by omega)).2.some_mem⟩)⟩

lemma card_lambda_pos (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    0 < Nat.card (LambdaN D ω k n) := by
  have := lambda_finite hω hk hn
  have := lambda_nonempty hω hk hn
  exact Nat.card_pos

lemma upsilon_nonneg (n : ℕ) (g : BinaryTreeAut) : 0 ≤ upsilon D ω k n g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `υ_n` is a probability on `Aut(T)`. -/
lemma hasSum_upsilon (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    HasSum (upsilon D ω k n) 1 := by
  classical
  have := lambda_finite hω hk hn
  let _ : Fintype (LambdaN D ω k n) := Fintype.ofFinite _
  have hpos := card_lambda_pos hω hk hn
  have hcard : ∀ g, Nat.card {p : LambdaN D ω k n // theta D ω k n p = g} =
      (Finset.univ.filter fun p => theta D ω k n p = g).card := by
    intro g
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsupp : ∀ g ∉ Finset.univ.image (theta D ω k n), upsilon D ω k n g = 0 := by
    intro g hg
    unfold upsilon
    rw [hcard]
    have : (Finset.univ.filter fun p => theta D ω k n p = g) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p _ hp
      exact hg (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩)
    simp [this]
  have h : HasSum (upsilon D ω k n)
      (∑ g ∈ Finset.univ.image (theta D ω k n), upsilon D ω k n g) :=
    hasSum_sum_of_ne_finset_zero hsupp
  convert h using 1
  unfold upsilon
  rw [← Finset.sum_div]
  simp_rw [hcard]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Finset.card_univ,
    ← Nat.card_eq_fintype_card, div_self]
  exact_mod_cast hpos.ne'

lemma hasSum_upsilon_sub (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    HasSum (fun g : grigorchuk ω => upsilon D ω k n g) 1 := by
  have hsub : Function.support (upsilon D ω k n) ⊆ (grigorchuk ω : Set BinaryTreeAut) :=
    fun g hg => (mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero D ω hω k hk n hn g hg).1
  exact (hasSum_subtype_iff_of_support_subset hsub).mpr (hasSum_upsilon hω hk hn)

lemma hasSum_upsilonCheck_sub (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ}
    (hn : D ∣ n) : HasSum (fun g : grigorchuk ω => upsilonCheck D ω k n g) 1 := by
  have h := hasSum_upsilon_sub hω hk hn
  rw [← (Equiv.inv (grigorchuk ω)).hasSum_iff] at h
  convert h using 1
  ext g
  simp [upsilonCheck]

/-! ### `μ_β` is a probability -/

lemma genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite := by
  have : (gens ω).Finite := by
    unfold gens
    exact (((Set.finite_singleton _).insert _).insert _).insert _
  exact this.preimage Subtype.val_injective.injOn

lemma grigA_mem (ω : ℕ → Fin 3) : grigA ∈ grigorchuk ω :=
  Subgroup.subset_closure (by simp [gens])

lemma hasSum_uniform (ω : ℕ → Fin 3) : HasSum (uniformMeasure (genSet ω)) 1 := by
  classical
  set F := (genSet_finite ω).toFinset with hF
  have hsupp : ∀ g ∉ F, uniformMeasure (genSet ω) g = 0 := by
    intro g hg
    rw [hF, Set.Finite.mem_toFinset] at hg
    simp [uniformMeasure, hg]
  have h : HasSum (uniformMeasure (genSet ω)) (∑ g ∈ F, uniformMeasure (genSet ω) g) :=
    hasSum_sum_of_ne_finset_zero hsupp
  convert h using 1
  have hmem : ∀ g ∈ F, uniformMeasure (genSet ω) g = (Nat.card (genSet ω) : ℝ)⁻¹ := by
    intro g hg
    rw [hF, Set.Finite.mem_toFinset] at hg
    simp [uniformMeasure, hg]
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, nsmul_eq_mul]
  have hcard : Nat.card (genSet ω) = F.card := by
    rw [hF, Nat.card_eq_card_finite_toFinset]
  have hne : F.Nonempty := ⟨⟨grigA, grigA_mem ω⟩, by rw [hF, Set.Finite.mem_toFinset]; simp [genSet, gens]⟩
  rw [hcard, mul_inv_cancel₀]
  exact_mod_cast hne.card_pos.ne'

/-- The weights `2^{−nβ}` on `n ⩾ 1`, `D ∣ n`. -/
noncomputable def wt (D : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ D ∣ n then (2 : ℝ) ^ (-((n : ℝ) * β)) else 0

lemma wt_nonneg (D : ℕ) (β : ℝ) (n : ℕ) : 0 ≤ wt D β n := by
  unfold wt; split_ifs <;> positivity

lemma rpow_eq_pow (β : ℝ) (n : ℕ) : (2 : ℝ) ^ (-((n : ℝ) * β)) = ((2 : ℝ) ^ (-β)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

lemma summable_wt (D : ℕ) {β : ℝ} (hβ : 0 < β) : Summable (wt D β) := by
  have hr : (2 : ℝ) ^ (-β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine Summable.of_nonneg_of_le (wt_nonneg D β) (fun n => ?_)
    (summable_geometric_of_lt_one (by positivity) hr)
  unfold wt; split_ifs
  · rw [rpow_eq_pow]
  · positivity

lemma tsum_wt_pos {D : ℕ} (hD : 1 ≤ D) {β : ℝ} (hβ : 0 < β) : 0 < ∑' n, wt D β n := by
  have h := (summable_wt D hβ).le_tsum D (fun j _ => wt_nonneg D β j)
  have : 0 < wt D β D := by
    unfold wt; rw [if_pos ⟨hD, dvd_refl D⟩]; positivity
  linarith

lemma normConst_eq (D : ℕ) (β : ℝ) : normConst D β = (2 * ∑' n, wt D β n)⁻¹ := rfl

/-- The pieces `a_n(g) = C_β 2^{−nβ} (υ_n(g) + υ̌_n(g))` of `μ_β`. -/
noncomputable def piece (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (n : ℕ) (g : grigorchuk ω) : ℝ :=
  if 1 ≤ n ∧ D ∣ n then
    normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * (upsilon D ω k n g + upsilonCheck D ω k n g)
  else 0

lemma muBeta_eq (β : ℝ) (g : grigorchuk ω) :
    muBeta D ω k β g = 1 / 2 * uniformMeasure (genSet ω) g + 1 / 2 * ∑' n, piece D ω k β n g :=
  rfl

lemma piece_nonneg (β : ℝ) (n : ℕ) (g : grigorchuk ω) : 0 ≤ piece D ω k β n g := by
  have hC : 0 ≤ normConst D β := by
    unfold normConst
    refine inv_nonneg.mpr (mul_nonneg two_pos.le (tsum_nonneg fun n => ?_))
    split_ifs
    · positivity
    · exact le_rfl
  unfold piece; split_ifs
  · exact mul_nonneg (mul_nonneg hC (by positivity))
      (add_nonneg (upsilon_nonneg _ _) (upsilon_nonneg _ _))
  · exact le_rfl

lemma hasSum_piece (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) (β : ℝ) (n : ℕ) :
    HasSum (piece D ω k β n) (2 * normConst D β * wt D β n) := by
  unfold piece wt
  split_ifs with hc
  · have := ((hasSum_upsilon_sub hω hk hc.2).add (hasSum_upsilonCheck_sub hω hk hc.2)).mul_left
      (normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)))
    have e : 2 * normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) =
        normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * (1 + 1) := by ring
    rw [e]
    exact this
  · simp only [mul_zero]; exact hasSum_zero

lemma hasSum_tsum_piece (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ} (hβ : 0 < β)
    (hD : 1 ≤ D) : HasSum (fun g : grigorchuk ω => ∑' n, piece D ω k β n g) 1 := by
  set F : ℕ × grigorchuk ω → ℝ := fun p => piece D ω k β p.1 p.2 with hF
  have hF0 : 0 ≤ F := fun p => piece_nonneg β p.1 p.2
  have hrow : ∀ n, HasSum (fun g => F (n, g)) (2 * normConst D β * wt D β n) :=
    fun n => hasSum_piece hω hk β n
  have hFs : Summable F := (summable_prod_of_nonneg hF0).mpr
    ⟨fun n => (hrow n).summable, by
      simp_rw [fun n => (hrow n).tsum_eq]
      exact (summable_wt D hβ).mul_left _⟩
  have htot : HasSum (fun n => 2 * normConst D β * wt D β n) (∑' p, F p) :=
    hFs.hasSum.prod_fiberwise hrow
  have hval : ∑' p, F p = 1 := by
    rw [← htot.tsum_eq, tsum_mul_left, normConst_eq]
    have := tsum_wt_pos hD hβ (D := D)
    field_simp
  have hFs' : Summable fun p : grigorchuk ω × ℕ => F p.swap := hFs.prod_symm
  have hcol : ∀ g : grigorchuk ω, HasSum (fun n => F (n, g)) (∑' n, piece D ω k β n g) :=
    fun g => (hFs'.prod_factor g).hasSum
  have := hFs'.hasSum.prod_fiberwise hcol
  rw [← hval, ← (Equiv.prodComm (grigorchuk ω) ℕ).tsum_eq F]
  exact this

lemma isProbability_muBeta (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ}
    (hβ : 0 < β) (hD : 1 ≤ D) : IsProbability (muBeta D ω k β) := by
  refine ⟨fun g => ?_, ?_⟩
  · rw [muBeta_eq]
    have h1 : 0 ≤ uniformMeasure (genSet ω) g := by
      unfold uniformMeasure; split_ifs <;> positivity
    have h2 : 0 ≤ ∑' n, piece D ω k β n g := tsum_nonneg fun n => piece_nonneg β n g
    positivity
  · have := ((hasSum_uniform ω).mul_left (1 / 2)).add
      ((hasSum_tsum_piece hω hk hβ hD).mul_left (1 / 2))
    have h1 : (1 : ℝ) = 1 / 2 * 1 + 1 / 2 * 1 := by norm_num
    rw [h1]
    exact this

/-! ### Finite entropy -/

/-! ### The tail -/

end P5Cor82Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.19: `sup_{x,y} P^t_{μ_β}(x, y) ⩽ C t^{-1/β}` (Erschler–Zheng pp. 48–49, prover 6)

For `v ⩾ 1` take `n = D(⌊j/D⌋ + 1)`, `j` least with `v ⩽ 2^j`; then `D ∣ n`, `v ⩽ 2^{n-1}` and
`2^n ⩽ 2^{D+1} v`. For a finite non-empty `Ω` with `|Ω| ⩽ v`:

* the isoperimetric bound for `P_n = P_{(υ_n + υ̌_n)/2}` (sibling stub, G9-type) gives
  `|∂_{P_n} U| ⩾ |U|/2` for `U ⊆ Ω`;
* `P_n` is substochastic and symmetric; its `uniformize` `R_n` is a symmetric transition kernel with
  the same boundary sizes and the same Dirichlet form, so the Cheeger inequality (Markov D1) gives
  `λ₁^{R_n}(Ω) ⩾ 1/8`;
* `μ_β ⩾ C_β 2^{-nβ} (υ_n + υ̌_n)/2`, so `ℰ_{P_μ} ⩾ C_β 2^{-nβ} ℰ_{R_n}` and
  `λ₁^{P_μ}(Ω) ⩾ C_β 2^{-nβ}/8 ⩾ c v^{-β}` with `c = C_β 2^{-(D+1)β}/8`.

Coulhon's profile bound (Markov H2) with `(c, β)` gives the constant, chosen before `ω` and `A`.
-/

open scoped RightActions
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

set_option linter.unusedSectionVars false

/-! ### Dirichlet forms -/

section Dirichlet

variable {X : Type*}

/-- A function on `X × X` vanishing off `Ω × X`, with summable rows, is summable (after
`LawlerSokal.D1.summable_prod_of_rows`). -/
lemma summable_prod_of_rows (Ω : Finset X) (g : X × X → ℝ) (hg : ∀ p : X × X, p.1 ∉ Ω → g p = 0)
    (hrow : ∀ x, Summable (fun y => g (x, y))) : Summable g := by
  classical
  have hdecomp : g = fun p => ∑ x ∈ Ω, (if p.1 = x then g p else 0) := by
    funext p
    rw [Finset.sum_ite_eq]
    split_ifs with hp
    · rfl
    · exact hg p hp
  have hpiece : ∀ x, Summable (fun p : X × X => if p.1 = x then g p else 0) := by
    intro x
    have hinj : Function.Injective (fun y : X => (x, y)) := fun a b h => (Prod.mk.inj h).2
    have hsupp : ∀ p ∉ Set.range (fun y : X => (x, y)), (if p.1 = x then g p else 0) = 0 := by
      intro p hp
      split_ifs with h
      · exact absurd ⟨p.2, by ext <;> simp [h]⟩ hp
      · rfl
    have hcomp : ((fun p : X × X => if p.1 = x then g p else 0) ∘ fun y => (x, y)) =
        fun y => g (x, y) := by
      funext y; simp
    exact (hinj.summable_iff hsupp).mp (by rw [hcomp]; exact hrow x)
  rw [hdecomp]
  exact summable_sum fun x _ => hpiece x

/-- The Dirichlet-form summand is summable for `f` supported in a finite set (after
`LawlerSokal.D1.summable_dirichlet`, with `π = 1`). -/
lemma summable_dirichlet {P : X → X → ℝ} (hP : IsTransition P) (hs : MarkovChain.IsSymmetric P)
    (Ω : Finset X) (f : X → ℝ) (hf : ∀ x ∉ Ω, f x = 0) :
    Summable (fun p : X × X => (f p.1 - f p.2) ^ 2 * P p.1 p.2 * (fun _ => (1 : ℝ)) p.1) := by
  set G : X × X → ℝ := fun p => f p.1 ^ 2 * P p.1 p.2 with hG
  have hGs : Summable G := by
    refine summable_prod_of_rows Ω G (fun p hp => by simp [hG, hf p.1 hp]) fun x => ?_
    exact (hP.2.1 x).mul_left (f x ^ 2)
  have hGs' : Summable (G ∘ Prod.swap) :=
    (Equiv.summable_iff (Equiv.prodComm X X)).mpr hGs
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) ((hGs.add hGs').mul_left 2)
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hP.1 _ _)) zero_le_one
  · simp only [hG, Function.comp, Prod.fst_swap, Prod.snd_swap, mul_one]
    have h1 : (f p.1 - f p.2) ^ 2 ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2 := by
      nlinarith [sq_nonneg (f p.1 + f p.2)]
    have hw : 0 ≤ P p.1 p.2 := hP.1 _ _
    rw [hs p.2 p.1]
    nlinarith

lemma dirichletForm_nonneg (P : X → X → ℝ) (hP0 : ∀ x y, 0 ≤ P x y) (f : X → ℝ) :
    0 ≤ dirichletForm P (fun _ => 1) f := by
  unfold dirichletForm
  exact mul_nonneg (by norm_num) (tsum_nonneg fun p =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hP0 _ _)) zero_le_one)

variable [DecidableEq X]

lemma dirichletForm_uniformize (Q : X → X → ℝ) (π f : X → ℝ) :
    dirichletForm (uniformize Q) π f = dirichletForm Q π f := by
  unfold dirichletForm uniformize
  congr 1
  refine tsum_congr fun p => ?_
  by_cases h : p.1 = p.2
  · rw [h]; simp
  · simp [h]

lemma boundarySize_uniformize (Q : X → X → ℝ) (π : X → ℝ) (U : Finset X) :
    boundarySize (uniformize Q) π U = boundarySize Q π U := by
  unfold boundarySize uniformize
  refine Finset.sum_congr rfl fun x hx => tsum_congr fun y => ?_
  have : x ≠ (y : X) := fun h => y.2 (h ▸ hx)
  simp [this]

/-- The Cheeger step on a substochastic symmetric `Q` with `|∂_Q U| ⩾ |U|/2` on subsets of `Ω`,
transferred to `P ⩾ w Q`: `λ₁^P(Ω) ⩾ w/8`. -/
lemma eigen_ge [Countable X] {P Q : X → X → ℝ} (hP : IsTransition P)
    (hPs : MarkovChain.IsSymmetric P) (hQ0 : ∀ x y, 0 ≤ Q x y) (hQs : ∀ x, Summable (Q x))
    (hQ1 : ∀ x, ∑' y, Q x y ≤ 1) (hQS : MarkovChain.IsSymmetric Q) {w : ℝ} (hw : 0 ≤ w)
    (hwQ : ∀ x y, w * Q x y ≤ P x y) (Ω : Finset X) (hΩ : Ω.Nonempty)
    (hiso : ∀ U ⊆ Ω, U.Nonempty → (U.card : ℝ) / 2 ≤ boundarySize Q (fun _ => 1) U) :
    w / 8 ≤ dirichletEigenvalue P (fun _ => 1) Ω := by
  set R := uniformize Q with hR
  have hRT : IsTransition R := MarkovHK.isTransition_uniformize hQ0 hQs hQ1
  have hRS : MarkovChain.IsSymmetric R := MarkovHK.uniformize_symm hQS
  have hRrev : IsReversible R (fun _ => 1) := fun x y => by simp [hRS x y]
  have hcheeger : 1 / 2 * (1 / 2 : ℝ) ^ 2 ≤ dirichletEigenvalue R (fun _ => 1) Ω := by
    refine LawlerSokal.half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize R (fun _ => 1)
      hRT (fun _ => one_pos) hRrev Ω hΩ (1 / 2) (by norm_num) fun U hU hUne => ?_
    rw [hR, boundarySize_uniformize]
    have := hiso U hU hUne
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  -- the set defining `λ₁^P(Ω)`
  obtain ⟨x₀, hx₀⟩ := hΩ
  refine le_csInf ⟨_, fun x => if x = x₀ then 1 else 0, fun x hx => by
    show (if x = x₀ then (1 : ℝ) else 0) = 0
    rw [if_neg (fun h => hx (by rw [h]; exact hx₀))], by
      unfold normSq
      have : (fun x => (if x = x₀ then (1 : ℝ) else 0) ^ 2 * 1) =
          fun x => if x = x₀ then 1 else 0 := by
        funext x; split_ifs <;> simp
      rw [this, tsum_ite_eq], rfl⟩ ?_
  rintro e ⟨f, hf, hnorm, rfl⟩
  have hRle : dirichletEigenvalue R (fun _ => 1) Ω ≤ dirichletForm R (fun _ => 1) f := by
    refine csInf_le ⟨0, ?_⟩ ⟨f, hf, hnorm, rfl⟩
    rintro e ⟨g, -, -, rfl⟩
    exact dirichletForm_nonneg R hRT.1 g
  have hcmp : w * dirichletForm R (fun _ => 1) f ≤ dirichletForm P (fun _ => 1) f := by
    rw [hR, dirichletForm_uniformize]
    rw [← dirichletForm_uniformize Q]
    unfold dirichletForm
    rw [← mul_assoc, mul_comm w, mul_assoc, ← tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Summable.tsum_le_tsum (fun p => ?_)
      ((summable_dirichlet hRT hRS Ω f hf).mul_left w) (summable_dirichlet hP hPs Ω f hf)
    show w * ((f p.1 - f p.2) ^ 2 * uniformize Q p.1 p.2 * 1) ≤ (f p.1 - f p.2) ^ 2 * P p.1 p.2 * 1
    by_cases h : p.1 = p.2
    · rw [h]; simp
    · have := hwQ p.1 p.2
      have h2 := sq_nonneg (f p.1 - f p.2)
      simp only [uniformize, h, if_false, add_zero, mul_one]
      nlinarith
  nlinarith

end Dirichlet

/-! ### The choice of `n` -/

lemma exists_level (D : ℕ) (hD : 1 ≤ D) (v : ℝ) (hv : 1 ≤ v) :
    ∃ n : ℕ, 1 ≤ n ∧ D ∣ n ∧ v ≤ 2 ^ (n - 1) ∧ (2 : ℝ) ^ n ≤ 2 ^ (D + 1) * v := by
  classical
  have hex : ∃ j : ℕ, v ≤ 2 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt v (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  obtain ⟨j, hjv, hjmin⟩ : ∃ j : ℕ, v ≤ 2 ^ j ∧ ∀ i < j, ¬ v ≤ 2 ^ i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj2 : (2 : ℝ) ^ j ≤ 2 * v := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; linarith
    · have := hjmin (j - 1) (by omega)
      rw [not_le] at this
      have e : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      linarith
  refine ⟨D * (j / D + 1), ?_, dvd_mul_right _ _, ?_, ?_⟩
  · exact Nat.mul_pos (by omega) (Nat.succ_pos _)
  · have hlt : j < D * (j / D + 1) := Nat.lt_mul_div_succ j (by omega)
    calc v ≤ 2 ^ j := hjv
      _ ≤ 2 ^ (D * (j / D + 1) - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  · have hle : D * (j / D + 1) ≤ j + D := by
      have := Nat.mul_div_le j D
      have e : D * (j / D + 1) = D * (j / D) + D := by ring
      rw [e]; linarith [Nat.mul_comm D (j / D)]
    calc (2 : ℝ) ^ (D * (j / D + 1)) ≤ 2 ^ (j + D) := pow_le_pow_right₀ (by norm_num) hle
      _ = 2 ^ j * 2 ^ D := pow_add _ _ _
      _ ≤ (2 * v) * 2 ^ D := mul_le_mul_of_nonneg_right hj2 (by positivity)
      _ = 2 ^ (D + 1) * v := by rw [pow_succ]; ring

lemma rpow_level_ge (D n : ℕ) (β : ℝ) (hβ : 0 < β) (v : ℝ) (hv : 1 ≤ v)
    (hn : (2 : ℝ) ^ n ≤ 2 ^ (D + 1) * v) :
    (2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) * v ^ (-β) ≤ (2 : ℝ) ^ (-((n : ℝ) * β)) := by
  have h1 : (2 : ℝ) ^ (-((n : ℝ) * β)) = ((2 : ℝ) ^ n) ^ (-β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  have h2 : (2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) * v ^ (-β) = ((2 : ℝ) ^ (D + 1) * v) ^ (-β) := by
    rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    congr 2; push_cast; ring
  rw [h1, h2]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)

/-! ### The profile bound -/

/-- `Λ_{P_μ}(v) ⩾ c v^{-β}` for `v ⩾ 1`. -/
lemma profile_ge (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (β : ℝ) (hβ : 0 < β) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) [DecidableEq (orbitOne ω)]
    (hμ : IsProbability (muBeta D ω k β)) (v : ℝ) (hv : 1 ≤ v) :
    normConst D β / 8 * (2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) * v ^ (-β) ≤
      isoperimetricProfile (orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay)
        (fun _ => 1) v := by
  have hD3 := three_le_of_satisfiesFr hω
  have hD : 1 ≤ D := by omega
  set P := orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay with hP
  have hPS : MarkovChain.IsSymmetric P :=
    isSymmetric_orbitKernel _ (muBeta_inv D ω k β) oneRay
  obtain ⟨n, hn1, hDn, hvn, hn2⟩ := exists_level D hD v hv
  set Q := orbitKernel (grigorchuk ω) (nuN D ω k n) oneRay with hQ
  have hQ0 : ∀ x y, 0 ≤ Q x y := orbitKernel_nonneg' _ (nuN_nonneg D ω k n) oneRay
  have hrow := hasSum_orbitKernel_row (grigorchuk ω) (nuN_nonneg D ω k n)
    (summable_nuN D ω k n) (oneRay : Ray)
  have hQs : ∀ x, Summable (Q x) := fun x => (hrow x).summable
  have hQ1 : ∀ x, ∑' y, Q x y ≤ 1 := fun x => by
    rw [(hrow x).tsum_eq]; exact tsum_nuN_le D ω k n
  have hQS : MarkovChain.IsSymmetric Q :=
    isSymmetric_orbitKernel _ (nuN_inv D ω k n) oneRay
  set w := normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) with hw
  have hC := normConst_pos D β hβ hD
  have hw0 : 0 ≤ w := by positivity
  have hT : IsTransition P := isTransition_orbitKernel (grigorchuk ω) hμ (oneRay : Ray)
  have hμs : Summable (muBeta D ω k β) := hμ.2.summable
  have hwQ : ∀ x y, w * Q x y ≤ P x y := fun x y =>
    orbitKernel_mul_le _ (nuN_nonneg D ω k n) (summable_nuN D ω k n) hμs
      (muBeta_nonneg D ω k β hβ hD) (mul_nuN_le_muBeta D ω k β hβ hD n hn1 hDn)
      oneRay x y
  have hiso := (orbitKernel_upsilon_eq_and_boundarySize_ge D ω hω k hk n hDn hn1).2.2
  -- the profile
  refine le_csInf ?_ ?_
  · obtain ⟨x₀⟩ : Nonempty (orbitOne ω) := ⟨⟨oneRay, 1, (grigorchuk ω).one_mem, by simp⟩⟩
    exact ⟨_, {x₀}, Finset.singleton_nonempty _, by simpa using hv, rfl⟩
  rintro e ⟨Ω, hΩ, hΩv, rfl⟩
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hΩv
  have hev := eigen_ge hT hPS hQ0 hQs hQ1 hQS hw0 hwQ Ω hΩ fun U hU hUne => by
    have hcard : U.card ≤ 2 ^ (n - 1) := by
      have h1 : (U.card : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_le_card hU
      have h2 : (U.card : ℝ) ≤ 2 ^ (n - 1) := by linarith
      exact_mod_cast h2
    have := hiso U hUne hcard
    have eQ : orbitKernel (grigorchuk ω)
        (fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2) oneRay = Q := rfl
    rw [eQ] at this
    have hpos : (0 : ℝ) < U.card := by exact_mod_cast hUne.card_pos
    rw [le_div_iff₀ hpos] at this
    linarith
  have hlev := rpow_level_ge D n β hβ v hv hn2
  calc normConst D β / 8 * (2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) * v ^ (-β)
      = normConst D β / 8 * ((2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) * v ^ (-β)) := by ring
    _ ≤ normConst D β / 8 * (2 : ℝ) ^ (-((n : ℝ) * β)) :=
        mul_le_mul_of_nonneg_left hlev (by positivity)
    _ = w / 8 := by rw [hw]; ring
    _ ≤ _ := hev

end P6Dev

end ErschlerZheng
end

section
open scoped RightActions
open DurrettProbability MarkovChain
open ErschlerZheng
open P6Dev in
theorem solution (D : ℕ) (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β)
    (hβ2 : β < 1) :
    ∃ C : ℝ, ∀ ω : ℕ → Fin 3, SatisfiesFr D ω → ∀ [DecidableEq (orbitOne ω)],
      ∀ k : ℕ → ℕ, IsAdmissibleSeq D k → ∀ t : ℕ, 1 ≤ t → ∀ x y : orbitOne ω,
        DurrettProbability.stepProb (orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay)
          t x y ≤ C / (t : ℝ) ^ (1 / β) := by
  have hD : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; simp at hβ1; linarith
    · exact h
  have hβ : 0 < β := by
    have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : (0 : ℝ) ≤ 1 - 1 / D := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hD'
    linarith
  set c := normConst D β / 8 * (2 : ℝ) ^ (-(((D : ℝ) + 1) * β)) with hc
  have hc0 : 0 < c := by have := normConst_pos D β hβ hD; positivity
  obtain ⟨C, -, hC⟩ :=
    Coulhon.stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge c β hc0 hβ
  refine ⟨C, fun ω hω _ k hk t ht x y => ?_⟩
  have hμ := P5Cor82Dev.isProbability_muBeta hω hk hβ hD
  have hPT := isTransition_orbitKernel (grigorchuk ω) hμ (oneRay : Ray)
  have hPS : MarkovChain.IsSymmetric (orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay) :=
    isSymmetric_orbitKernel _ (muBeta_inv D ω k β) oneRay
  exact (hC (orbitOne ω) _ hPT hPS fun v hv => profile_ge D ω hω β hβ k hk hμ v hv).1
    t ht x y
end
