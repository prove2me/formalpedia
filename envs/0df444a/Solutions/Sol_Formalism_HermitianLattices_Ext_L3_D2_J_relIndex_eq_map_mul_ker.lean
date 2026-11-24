-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.relIndex_eq_map_mul_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:17.382565+00:00
-- url     : https://prove2.me/submissions/a247b06d-46db-4d1e-8800-d9aad53c1734

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {A B : AddSubgroup G} (hBA : B ≤ A) :
    B.relIndex A = (B.map f).relIndex (A.map f) * (B ⊓ f.ker).relIndex (A ⊓ f.ker) := by
  have h1 : (B.map f).relIndex (A.map f) = (B ⊔ (A ⊓ f.ker)).relIndex A := by
    rw [AddSubgroup.relIndex_map_map]
    have e1 : A ⊔ f.ker = A ⊔ (B ⊔ f.ker) := by
      rw [← sup_assoc, sup_eq_left.2 hBA]
    rw [e1, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right]
    congr 1
    rw [inf_comm A, sup_inf_assoc_of_le _ hBA]
  have h2 : (B ⊓ f.ker).relIndex (A ⊓ f.ker) = B.relIndex (B ⊔ (A ⊓ f.ker)) := by
    have e2 : B ⊓ f.ker = B ⊓ (A ⊓ f.ker) := by rw [← inf_assoc, inf_eq_left.2 hBA]
    rw [sup_comm, AddSubgroup.relIndex_sup_right, e2, AddSubgroup.inf_relIndex_right]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hBA inf_le_left)).symm
end Formalism.HermitianLattices.Ext.L3.D2.J
