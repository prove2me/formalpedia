-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x2.sum_addChar_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:28.856191+00:00
-- url     : https://prove2.me/submissions/83a23c03-e247-44c9-9003-ff72e75cc419

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_normsq_eq_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2
namespace Formalism.FourierDecayAlt.P.A6x2
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type)
    [AddCommGroup G] [Fintype G] (v : G → E) :
    ∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 := by
  classical
  have key : ((∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 : ℝ) : ℂ) =
      (((Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have h1 : ∀ χ : AddChar G ℂ, ((‖∑ g, χ (-g) • v g‖ : ℂ)) ^ 2 =
        ∑ g, ∑ h, χ (g - h) * inner ℂ (v g) (v h) := by
      intro χ
      rw [normsq_eq_inner, sum_inner]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [inner_smul_left, inner_smul_right, AddChar.map_neg_eq_conj, Complex.conj_conj,
        sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ g : G, ∑ χ : AddChar G ℂ, ∑ h, χ (g - h) * inner ℂ (v g) (v h) =
        (Fintype.card G : ℂ) * (‖v g‖ : ℂ) ^ 2 := by
      intro g
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
      rw [Finset.sum_eq_single g]
      · rw [if_pos rfl, normsq_eq_inner]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ g) h
    simp_rw [h2]
    rw [Finset.mul_sum]
  exact_mod_cast key
end Formalism.FourierDecayAlt.P.A6x2
