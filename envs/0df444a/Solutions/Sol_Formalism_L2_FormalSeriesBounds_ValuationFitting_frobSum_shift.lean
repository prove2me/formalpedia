-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationFitting.frobSum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:10.41383+00:00
-- url     : https://prove2.me/submissions/fa34f883-4de7-427d-bada-b542af439cd2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_pow_frob
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_rpow_neg_succ
import Theorems.Thm_ReciprocityTheory_PGsh_Up_summable_geom_p
import Theorems.Thm_ReciprocityTheory_PGsh_Up_tsum_geom_p


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.ValuationFitting
theorem _root_.solution {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    {G : ∀ g, Cart V d (I g) (J g)} {big : Fin 2 → ZMod d → Prop} {rh : ℕ} {h : Fin 2 → ℕ}
    {ht : ∀ g, Fin (h g) → I g → C}
    {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    {O : Type} [CommRing O] [Algebra ℤ_[V.l] O] {σ : O ≃ₐ[ℤ_[V.l]] O} {cp : R} {gB : ℕ}
    {H : HodgeTateDatum V.l gB vm R O σ cp} {U : UnramData V.l gB vm R O σ cp H}
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) (g : Fin 2) (a : ZMod d) :
    ReciprocityTheory.PGsh.Up.frobSum U (T.ix g a) =
      S4.frobSum V.l (pT G g) a - (rh : ℝ) / ((V.l : ℝ) - 1) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ k : Fin U.m, ((U.r k + rh : ℕ) : ℝ) ≤ B :=
    ⟨∑ k, ((U.r k + rh : ℕ) : ℝ), fun k => Finset.single_le_sum
      (f := fun k => ((U.r k + rh : ℕ) : ℝ)) (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ k)⟩
  have hsG := summable_geom_p (p := V.l)
    (fun n => ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ))
    (fun n => Nat.cast_nonneg _) B (fun n => hB _)
  have hsρ := summable_geom_p (p := V.l) (fun _ => (rh : ℝ)) (fun _ => Nat.cast_nonneg _) rh
    (fun _ => le_rfl)
  have hsum : (∑' n : ℕ, (V.l : ℝ) ^ (-((n : ℝ) + 1)) *
      ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ)) = S4.frobSum V.l (pT G g) a := by
    unfold S4.frobSum
    refine tsum_congr fun n => ?_
    rw [pow_frob U.φ (T.ix g) (T.ix_frob g) a (n + 1), rpow_neg_succ V.l_prime.pos, T.rank]
  unfold ReciprocityTheory.PGsh.Up.frobSum
  have e1 : ∀ n : ℕ, (V.l : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) (T.ix g a)) : ℝ) =
      (V.l : ℝ) ^ (-((n : ℝ) + 1)) * ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ) -
        (V.l : ℝ) ^ (-((n : ℝ) + 1)) * rh := by
    intro n; push_cast; ring
  simp_rw [e1]
  rw [Summable.tsum_sub hsG hsρ, tsum_mul_right, tsum_geom_p, hsum]
  ring
end Formalism.L2.FormalSeriesBounds.ValuationFitting
