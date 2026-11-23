-- Prove2me | solution 1 for Formalism.FG.witt_teichmuller_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:10.044957+00:00
-- url     : https://prove2.me/submissions/3c1662c4-2c1c-425d-8960-8063d23cc9bf

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Theorems.Thm_Formalism_FG_WittVectorsCharZero_neZero_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG
open Formalism.FG.WittVectorsCharZero
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.WittTeichRoot := by
  intro l _ d hd
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hNpos : 0 < l ^ d - 1 := by
    have : l ≤ l ^ d := Nat.le_self_pow (by omega) l
    omega
  haveI : NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := neZero_cast l d hd
  haveI : NeZero (((l ^ d - 1 : ℕ) : AlgebraicClosure (ZMod l))) := by
    have h := NeZero.of_injective (f := algebraMap (ZMod l) (AlgebraicClosure (ZMod l)))
      (a := (((l ^ d - 1 : ℕ) : ZMod l))) (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective
    rw [map_natCast] at h
    exact h
  have hdeg : (Polynomial.cyclotomic (l ^ d - 1) (AlgebraicClosure (ZMod l))).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hNpos).ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot μ (l ^ d - 1) := Polynomial.isRoot_cyclotomic_iff.mp hμ
  refine ⟨WittVector.teichmuller l μ, hprim.map_of_injective ?_⟩
  intro a b h
  have h2 := congrArg (fun w => WittVector.coeff w 0) h
  simpa [WittVector.teichmuller_coeff_zero] using h2
end Formalism.FG
