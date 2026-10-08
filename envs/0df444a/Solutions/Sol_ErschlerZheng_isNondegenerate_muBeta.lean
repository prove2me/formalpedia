-- Prove2me | solution 1 for ErschlerZheng.isNondegenerate_muBeta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:01:55.853859+00:00
-- url     : https://prove2.me/submissions/3033fe74-1c1c-4f0e-af5c-e4deee823a02

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction

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
# Walks: facts backing sentences of the notes (not results of the paper)

1. For a non-degenerate `μ`, `HasNontrivialPoissonBoundary μ` is the literal p. 2 criterion
   (moved from `checks/lean/WalksGuards.lean`).
2. The point mass `δ_1` on a non-trivial group: a probability of finite entropy with `h = 0`,
   every function is `δ_1`-harmonic (so the literal criterion holds), and
   `¬ HasNontrivialPoissonBoundary δ_1` (moved from `WalksGuards.lean`, §Degenerate).
3. `μ_β` is non-degenerate (moved from `Dev/P3Goal.lean`).
4. `pathMeasure μ x` is a probability measure when points are measurable: the path map is
   a.e. equal to a map that factors through the countable set `insert 1 (support μ)`.
5. `HasVolumeExponent` along `ℕ` is the same as the limit along real `r`, since
   `log ⌊r⌋ / log r → 1`.
-/

open MeasureTheory Filter Topology

set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace NewWalksDev

/-! ### Item 1: non-degenerate `μ` -/

section Nondegenerate

variable {G : Type*} [Group G]

end Nondegenerate

/-! ### Item 2: the point mass at the identity -/

section Degenerate

variable {G : Type*} [Group G]

end Degenerate

/-! ### Item 3: `μ_β` is non-degenerate -/

section MuBeta

open Garrido

theorem gens_inv {ω : ℕ → Fin 3} {x : BinaryTreeAut} (hx : x ∈ gens ω) : x⁻¹ = x := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact GrigBasic.grigA_inv
  all_goals exact GrigBasic.gen_inv _ _

theorem genSet_inv {ω : ℕ → Fin 3} {g : grigorchuk ω} (hg : g ∈ genSet ω) : g⁻¹ = g :=
  Subtype.ext (by rw [InvMemClass.coe_inv]; exact gens_inv hg)

theorem upsilon_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    0 ≤ upsilon D ω k n g := by
  unfold upsilon; positivity

theorem normConst_nonneg (D : ℕ) (β : ℝ) : 0 ≤ normConst D β := by
  unfold normConst
  apply inv_nonneg.mpr
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg fun n => by split_ifs <;> positivity

theorem genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite :=
  (show (gens ω).Finite by unfold gens; exact Set.toFinite _).preimage
    Subtype.val_injective.injOn

theorem grigA_mem_genSet (ω : ℕ → Fin 3) :
    (⟨grigA, Subgroup.subset_closure (by simp [gens])⟩ : grigorchuk ω) ∈ genSet ω := by
  simp [genSet, gens]

/-- `μ_β` charges every generator: its `½ u_S` part alone is positive on `S`. -/
theorem muBeta_pos_of_mem (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) {g : grigorchuk ω}
    (hg : g ∈ genSet ω) : 0 < muBeta D ω k β g := by
  unfold muBeta
  have hcard : 0 < Nat.card (genSet ω) := by
    haveI := (genSet_finite ω).to_subtype
    haveI : Nonempty (genSet ω) := ⟨⟨_, hg⟩⟩
    exact Nat.card_pos
  have h1 : uniformMeasure (genSet ω) g = (Nat.card (genSet ω) : ℝ)⁻¹ := by
    unfold uniformMeasure; rw [if_pos hg]
  have h2 : 0 ≤ ∑' n : ℕ, (if 1 ≤ n ∧ D ∣ n then
      normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) *
        (upsilon D ω k n g + upsilonCheck D ω k n g) else 0) :=
    tsum_nonneg fun n => by
      split_ifs
      · exact mul_nonneg (mul_nonneg (normConst_nonneg D β) (by positivity))
          (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
      · exact le_rfl
  rw [h1]
  have : (0 : ℝ) < (Nat.card (genSet ω) : ℝ)⁻¹ := by positivity
  linarith

/-- The support of `μ_β` contains the generators, which are involutions generating `G_ω`, so
it generates `G_ω` as a semigroup. -/
theorem muBeta_isNondegenerate (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) :
    IsNondegenerate (muBeta D ω k β) := by
  unfold IsNondegenerate
  rw [eq_top_iff]
  intro g hgtop
  clear hgtop
  have hsub : genSet ω ⊆ {g | muBeta D ω k β g ≠ 0} := fun g hg =>
    (muBeta_pos_of_mem D ω k β hg).ne'
  have hcl : Subgroup.closure (genSet ω) = ⊤ := Subgroup.closure_closure_coe_preimage
  have hg : g ∈ Subgroup.closure (genSet ω) := by rw [hcl]; trivial
  refine Subsemigroup.closure_mono hsub ?_
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact Subsemigroup.subset_closure hx
  | inv_mem x hx => rw [genSet_inv hx]; exact Subsemigroup.subset_closure hx
  | one =>
    have ha := grigA_mem_genSet ω
    set a : grigorchuk ω := ⟨grigA, Subgroup.subset_closure (by simp [gens])⟩
    rw [show (1 : grigorchuk ω) = a⁻¹ * a from (inv_mul_cancel a).symm, genSet_inv ha]
    exact Subsemigroup.mul_mem _ (Subsemigroup.subset_closure ha) (Subsemigroup.subset_closure ha)
  | mul x y _ _ hx hy => exact Subsemigroup.mul_mem _ hx hy

end MuBeta

/-! ### Item 4: `pathMeasure μ x` is a probability measure -/

section PathMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

end PathMeasure

/-! ### Item 5: the volume exponent along `ℕ` and along `ℝ` -/

end NewWalksDev

end ErschlerZheng

end

section
open MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open ErschlerZheng
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) :
    IsNondegenerate (muBeta D ω k β) :=
  NewWalksDev.muBeta_isNondegenerate D ω k β
end
