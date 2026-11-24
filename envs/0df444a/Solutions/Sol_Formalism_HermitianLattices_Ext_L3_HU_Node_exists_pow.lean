-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Node.exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:08.567995+00:00
-- url     : https://prove2.me/submissions/0fecf736-6a60-4f36-859f-3aa49ee5975b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_pow_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
open Formalism.HermitianLattices.Ext.L3.HU.Node
namespace Formalism.HermitianLattices.Ext.L3.HU.Node
theorem _root_.solution (hS : IsLocUnif S ϖ) {ι : Type*} (s : Finset ι) (a : ι → K) :
    ∃ l : ℕ, ∀ i ∈ s, ϖ ^ l * a i ∈ S := by
  choose L hL using hS.arch
  refine ⟨∑ i ∈ s, L (a i), fun i hi => ?_⟩
  have hle : L (a i) ≤ ∑ j ∈ s, L (a j) :=
    Finset.single_le_sum (f := fun j => L (a j)) (fun _ _ => Nat.zero_le _) hi
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact S.mul_mem (S.pow_mem hS.mem _) (hL _)
end Formalism.HermitianLattices.Ext.L3.HU.Node
