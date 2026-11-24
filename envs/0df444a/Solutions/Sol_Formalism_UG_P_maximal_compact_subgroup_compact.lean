-- Prove2me | solution 1 for Formalism.UG.P.maximal_compact_subgroup_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:51.816707+00:00
-- url     : https://prove2.me/submissions/9293508d-c1a9-480b-9028-19c3abfa54bf

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Theorems.Thm_Formalism_UG_P_isCompact_units_of_unitary
import Theorems.Thm_Formalism_UG_P_mem_Upq_iff
import Theorems.Thm_Formalism_UG_P_mem_blockDiag_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.KpqSubgroupCompact := by
  intro p q
  have hJ : ((JpqUnit p q : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := rfl
  have hset : ((Formalism.UG.Upq p q ⊓ Subgroup.centralizer {JpqUnit p q} : Subgroup _) :
      Set (GL (Fin p ⊕ Fin q) ℂ)) = ↑(Formalism.UG.Upq p q) ∩ Formalism.UG.blockDiag p q := by
    ext g
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, mem_blockDiag_iff]
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hJ]
  refine ⟨_, hset, ?_⟩
  rw [hset]
  have hT : IsClosed {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ |
      star M * Formalism.UG.Jpq p q * M = Formalism.UG.Jpq p q ∧ Formalism.UG.Jpq p q * M = M * Formalism.UG.Jpq p q} := by
    apply IsClosed.inter
    · exact isClosed_eq ((continuous_star.mul continuous_const).mul continuous_id) continuous_const
    · exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hU : ∀ M ∈ {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ |
      star M * Formalism.UG.Jpq p q * M = Formalism.UG.Jpq p q ∧ Formalism.UG.Jpq p q * M = M * Formalism.UG.Jpq p q},
      star M * M = 1 := by
    rintro M ⟨h1, h2⟩
    have hJJ := Jpq_mul_self p q
    calc star M * M = star M * M * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [hJJ, mul_one]
      _ = star M * (Formalism.UG.Jpq p q * M) * Formalism.UG.Jpq p q := by rw [h2]; simp only [mul_assoc]
      _ = 1 := by rw [← mul_assoc, h1, hJJ]
  convert isCompact_units_of_unitary hT hU using 1
  ext g
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_Upq_iff, mem_blockDiag_iff, Set.mem_setOf_eq]
end Formalism.UG.P
