-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.signatureOneComplementOfMinorNeZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:54.399703+00:00
-- url     : https://prove2.me/submissions/71102a2a-b7b5-4087-9e46-0120f71c484b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_injL
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormMinorNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Base
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
private theorem HermSpace_B_add_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x + y) z = H.B x z + H.B y z := by
  rw [map_add, LinearMap.add_apply]
end Base
section Base2
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base2
section CaseA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
end CaseA
section Gram
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Gram
section V0
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end V0
section Sig
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
end Sig
section Perp
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
end Perp
section DetBlocks
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
end DetBlocks
section Lift
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Lift
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCaseBSig := by
  intro K V _ _ _ _ σ H r F F' hT hP hD
  obtain ⟨x, hx, x', hx', h1, -, h3, -, -, -⟩ := normalFormMinorNeZero K V H r F F' hD
  unfold Formalism.HermitianLatticeCounting.S6.SigPerp
  refine ⟨F.z - x, h1, ?_, fun w hw hwz hw0 => ?_⟩
  · rw [h3, map_neg, Complex.neg_re]
    linarith
  · apply hP w
    · intro a
      induction a using Fin.lastCases with
      | last =>
        have e : F.e (Fin.last r) = (F.z - x) + x := (sub_add_cancel F.z x).symm
        rw [e, HermSpace_B_add_left, B_swap0 H hwz, hw x (Submodule.mem_sup_left hx), add_zero]
      | cast b => exact hw _ (Submodule.mem_sup_left ((e_mem_X F) b))
    · intro hwI
      apply hw0
      exact Dl_injL F F' (le_refl r) hD hwI
        (fun u hu => B_swap0 H (hw u (Submodule.mem_sup_right hu)))
end Formalism.HermitianLatticeCounting.P
