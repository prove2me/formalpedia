-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.eS_mul_asAlg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:47.932199+00:00
-- url     : https://prove2.me/submissions/62531301-6998-469e-88d8-22aac56dd96e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_mul_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    eS τ ρ * ρ.asAlgebraHom a = (charOf τ 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K T (τ.asAlgebraHom a * τ g⁻¹) • ρ g := by
  induction a using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, eS_mul_rho]
    simp only [charOf, ← map_mul]
  | add f g hf hg =>
    rw [map_add, mul_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add, add_mul, map_add, add_smul]
  | smul r f hf =>
    rw [map_smul, mul_smul_comm, hf, smul_comm r, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_mul_assoc, map_smul, smul_eq_mul, mul_smul]
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
