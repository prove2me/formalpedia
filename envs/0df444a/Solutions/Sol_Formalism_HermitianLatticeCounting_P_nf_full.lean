-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nf_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:36.14635+00:00
-- url     : https://prove2.me/submissions/8bad6173-867c-4d77-85ed-96904231bf1c

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_swap
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_II_comm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_jointSpan_comm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leadingMinorNeZero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normSqScalarMulEq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_jointSpanRadical
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_jointSpanComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {H : HermSpace K V} {r : ℕ} (F F' : FlagD H r) (hA : F.Aniso) (hA' : F'.Aniso) (j : ℕ) (hj : j ≤ r)
    (c : K) (hS : NFShape F F' j c) : NFFull F F' j hj c := by
  obtain ⟨hc, hfr, hlead, hex, hb, hb', hI, hI', hz⟩ := id hS
  have hminor := leadingMinorNeZero K V H r F F' j hj c hA' hb hI' hz
  have hnorm := normSqScalarMulEq K V H r F F' j hj c hI hI' hz hminor
  obtain ⟨hrad, hfin, hx⟩ := jointSpanRadical K V H r F F' j hj c hA' hb hb' hI hI' hz hminor
  have hcompl := jointSpanComplement K V H r F F' j hj c hI' hz hminor
  have hz' : F.z - c⁻¹ • F'.z ∈ F'.X ⊔ F.X := by
    rw [sup_comm]
    have := Submodule.smul_mem _ (-c⁻¹) hz
    convert this using 1
    rw [smul_sub, smul_smul, show -c⁻¹ * c = -1 by rw [neg_mul, inv_mul_cancel₀ hc]]
    simp only [neg_smul, one_smul]
    abel
  have hminor' : Formalism.HermitianLatticeCounting.S6.Dl F' F j (hj.trans (Nat.le_succ r)) ≠ 0 := by
    rw [Dl_swap]
    exact fun h0 => hminor (star_eq_zero.1 h0)
  have hb2 : Formalism.HermitianLatticeCounting.S6.II F' F ⊓ F'.Xa j = ⊥ := by rw [II_comm]; exact hb'
  have hb2' : Formalism.HermitianLatticeCounting.S6.II F' F ⊓ F.Xa j = ⊥ := by rw [II_comm]; exact hb
  have hI2 : F'.X = F'.Xa j ⊔ Formalism.HermitianLatticeCounting.S6.II F' F := by rw [II_comm]; exact hI'
  have hI2' : F.X = F.Xa j ⊔ Formalism.HermitianLatticeCounting.S6.II F' F := by rw [II_comm]; exact hI
  obtain ⟨-, -, hx'⟩ := jointSpanRadical K V H r F' F j hj c⁻¹ hA hb2 hb2' hI2 hI2' hz' hminor'
  have hcompl' := jointSpanComplement K V H r F' F j hj c⁻¹ hI2' hz' hminor'
  rw [jointSpan_comm, II_comm] at hx'
  rw [jointSpan_comm] at hcompl'
  unfold Formalism.HermitianLatticeCounting.S6.NFFull
  exact ⟨hS, hnorm, hminor, hrad, hfin, hx, hx', hcompl, hcompl'⟩
end Formalism.HermitianLatticeCounting.P
