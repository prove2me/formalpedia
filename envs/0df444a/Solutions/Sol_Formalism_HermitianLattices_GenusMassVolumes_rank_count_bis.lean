-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.rank_count_bis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:01.245854+00:00
-- url     : https://prove2.me/submissions/becd5e5b-f474-4aca-be64-336cfb89ed3b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma card_orbits_mul_card_eq_card_of_free (G Y : Type) [Group G] [Fintype G] [Fintype Y] [MulAction G Y]
    (h : ∀ y : Y, MulAction.stabilizer G y = ⊥) :
    Nat.card (MulAction.orbitRel.Quotient G Y) * Fintype.card G = Fintype.card Y := by
  classical
  have hc : ∀ ω : MulAction.orbitRel.Quotient G Y,
      Fintype.card (MulAction.stabilizer G ω.out) = 1 := by
    intro ω
    rw [Fintype.card_eq_nat_card, h]
    exact Subgroup.card_bot
  rw [MulAction.card_eq_sum_card_group_div_card_stabilizer G Y, Nat.card_eq_fintype_card]
  simp only [hc, Nat.div_one, Finset.sum_const, Finset.card_univ, smul_eq_mul]
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : RankCountExact := by
  intro ι _ Γ _ _ Y _ _ hfree
  have hi : ∀ i, (Nat.card (MulAction.orbitRel.Quotient (Γ i) Y) : ℝ) =
      ((Fintype.card (Γ i) : ℝ))⁻¹ * Fintype.card Y := by
    intro i
    have h := card_orbits_mul_card_eq_card_of_free (Γ i) Y (hfree i)
    have hpos : (0 : ℝ) < Fintype.card (Γ i) := by exact_mod_cast Fintype.card_pos
    rw [eq_inv_mul_iff_mul_eq₀ hpos.ne', ← h]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_mul]
end Formalism.HermitianLattices.GenusMassVolumes
